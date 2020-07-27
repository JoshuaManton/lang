package main

import "core:reflect"

translate_ir_to_vm :: proc(ir: ^IR_Result) -> ^VM {
    vm := make_vm();

    for variable in ir.global_variables {
        address := vm_allocate_static_storage(vm, cast(int)variable.type.size, cast(int)variable.type.align);
        assert(address != 0);
        // weird that we have to do this pointery thing
        storage := &variable.storage.kind.(Global_Storage);
        storage.address = cast(u64)address;
    }

    for procedure in ir.procedures {
        if procedure.name == "main" {
            vm.entry_point = cast(u64)len(vm.instructions);
        }

        gen_vm_proc(vm, procedure);
    }

    return vm;
}

gen_vm_load_from_storage :: proc(vm: ^VM, procedure: ^IR_Proc, dst: Register, storage: ^IR_Storage) {
    switch kind in storage.kind {
        case Stack_Frame_Storage: {
            add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(kind.offset_in_stack_frame + cast(u64)storage.type_stored.size)});
            gen_vm_load_from_pointer(vm, procedure, dst, .rt, cast(u64)storage.type_stored.size);
        }
        case Global_Storage: {
            assert(kind.address != 0);
            add_instruction(vm, MOVI{.rt, cast(i64)kind.address}); // todo(josh): this kind.address could probably be an immediate
            gen_vm_load_from_pointer(vm, procedure, dst, .rt, cast(u64)storage.type_stored.size);
        }
        case: panic(tprint(storage));
    }
}

gen_vm_load_from_pointer :: proc(vm: ^VM, procedure: ^IR_Proc, dst: Register, ptr_reg: Register, size: u64) {
    switch size {
        case 1: add_instruction(vm, LOAD8 {dst, ptr_reg});
        case 2: add_instruction(vm, LOAD16{dst, ptr_reg});
        case 4: add_instruction(vm, LOAD32{dst, ptr_reg});
        case 8: add_instruction(vm, LOAD64{dst, ptr_reg});
        case: panic("too big");
    }
}

gen_vm_store_to_storage :: proc(vm: ^VM, procedure: ^IR_Proc, src: Register, storage: ^IR_Storage) {
    switch storage_kind in storage.kind {
        case Stack_Frame_Storage: {
            add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(storage_kind.offset_in_stack_frame + cast(u64)storage.type_stored.size)});
            gen_vm_store_to_pointer(vm, procedure, .rt, src, cast(u64)storage.type_stored.size);
        }
        case Global_Storage: {
            assert(storage_kind.address != 0);
            add_instruction(vm, MOVI{.rt, cast(i64)storage_kind.address});
            gen_vm_store_to_pointer(vm, procedure, .rt, src, cast(u64)storage.type_stored.size);
        }
        case: panic(tprint(storage));
    }
}

gen_vm_store_to_pointer :: proc(vm: ^VM, procedure: ^IR_Proc, dst_ptr: Register, src: Register, size: u64) {
    switch size {
        case 1: add_instruction(vm, STORE8 {dst_ptr, src});
        case 2: add_instruction(vm, STORE16{dst_ptr, src});
        case 4: add_instruction(vm, STORE32{dst_ptr, src});
        case 8: add_instruction(vm, STORE64{dst_ptr, src});
        case: panic("too big");
    }
}

gen_vm_proc :: proc(vm: ^VM, procedure: ^IR_Proc) {
    // header
    label(vm, procedure.name);

    // save caller things :CallingConvention
    vm_comment(vm, "save caller frame and return address");
    add_instruction(vm, PUSH{.rfp});
    add_instruction(vm, PUSH{.ra});

    // setup our stack frame
    vm_comment(vm, "setup stack frame");
    add_instruction(vm, MOV{.rfp, .rsp});
    add_instruction(vm, ADDI{.rsp, .rsp, cast(i64)-procedure.stack_frame_size});

    // for param in procedure.parameters {
    //     gen_vm_load_from_storage(vm, procedure, .rt, param.storage);
    // }

    // generate the body
    vm_comment(vm, "body");
    gen_vm_block(vm, procedure, procedure.block);

    if procedure.name == "main" {
        // :CallingConvention
        vm_comment(vm, "special sauce for main()");
        add_instruction(vm, ADDI{.rsp, .rsp, cast(i64)procedure.stack_frame_size});
        // add_instruction(vm, POP{.ra});
        // add_instruction(vm, POP{.rfp});
        add_instruction(vm, EXIT{});
    }
    else {
        // return
        gen_vm_return(vm, procedure);
    }
}

gen_vm_return :: proc(vm: ^VM, procedure: ^IR_Proc, ir_return: ^IR_Return = nil) {
    vm_comment(vm, "return");
    add_instruction(vm, ADDI{.rsp, .rsp, cast(i64)procedure.stack_frame_size});

    // :CallingConvention
    add_instruction(vm, POP{.ra});
    add_instruction(vm, POP{.rfp});

    if ir_return != nil {
        if reg, ok := getval(&ir_return.result_register); ok {
            assert(ir_return.type.size == 4 || ir_return.type.size == 8);
            add_instruction(vm, PUSH{VM_REGISTER(reg^)});
        }
    }

    add_instruction(vm, MOV{.rip, .ra});
}

gen_vm_block :: proc(vm: ^VM, procedure: ^IR_Proc, block: ^IR_Block) {
    for inst in &block.instructions {
        vm_comment(vm, aprint(reflect.union_variant_type_info(inst.kind)));
        switch kind in &inst.kind {
            case IR_Move_Immediate: {
                switch val in kind.value {
                    case i64: add_instruction(vm, MOVI{VM_REGISTER(kind.dst), kind.value.(i64)});
                    case f64: panic("todo(josh): support floats");
                    case: panic(tprint(val));
                }
            }
            case IR_Store: gen_vm_store_to_storage(vm, procedure, VM_REGISTER(kind.reg), kind.storage);
            case IR_Load:  gen_vm_load_from_storage (vm, procedure, VM_REGISTER(kind.dst), kind.storage);
            case IR_Binop: {
                switch kind.op {
                    case .Plus:          add_instruction(vm, ADD{VM_REGISTER(kind.dst), VM_REGISTER(kind.lhs), VM_REGISTER(kind.rhs)});
                    case .Multiply:      add_instruction(vm, MUL{VM_REGISTER(kind.dst), VM_REGISTER(kind.lhs), VM_REGISTER(kind.rhs)});
                    case .Minus:         add_instruction(vm, SUB{VM_REGISTER(kind.dst), VM_REGISTER(kind.lhs), VM_REGISTER(kind.rhs)});
                    case .Equal_To:      add_instruction(vm, EQ {VM_REGISTER(kind.dst), VM_REGISTER(kind.lhs), VM_REGISTER(kind.rhs)});
                    case .Not_Equal:     add_instruction(vm, NEQ{VM_REGISTER(kind.dst), VM_REGISTER(kind.lhs), VM_REGISTER(kind.rhs)});
                    case .Divide:        unimplemented();
                    case .Mod:           unimplemented();
                    case .Mod_Mod:       unimplemented();
                    case .Shift_Left:    unimplemented();
                    case .Shift_Right:   unimplemented();
                    case .Bit_Xor:       unimplemented();
                    case .Bit_Or:        unimplemented();
                    case .Bit_And:       unimplemented();
                    case .Bit_Not:       unimplemented();
                    case .Not:           unimplemented();
                    case .Less:          unimplemented();
                    case .Greater:       unimplemented();
                    case .Less_Equal:    unimplemented();
                    case .Greater_Equal: unimplemented();
                    case .And:           unimplemented();
                    case .Or:            unimplemented();
                }
            }
            case IR_Unary: {
                #partial
                switch kind.op {
                    case .Minus: {
                        add_instruction(vm, SUB{VM_REGISTER(kind.dst), .rz, VM_REGISTER(kind.rhs)});
                    }
                    case .Not: {
                        add_instruction(vm, EQ{VM_REGISTER(kind.dst), VM_REGISTER(kind.rhs), .rz});
                    }
                    case: panic(tprint(kind.op));
                }
            }
            case IR_If: {
                end_of_if_label := aprint("if_", kind.s);
                else_label := aprint("if_else_", kind.s);
                if kind.else_block != nil {
                    add_instruction(vm, GOTOIFZ{VM_REGISTER(kind.condition_reg), else_label});
                }
                else {
                    add_instruction(vm, GOTOIFZ{VM_REGISTER(kind.condition_reg), end_of_if_label});
                }

                gen_vm_block(vm, procedure, kind.block);

                if kind.else_block != nil {
                    add_instruction(vm, GOTO{end_of_if_label});
                    label(vm, else_label);
                    gen_vm_block(vm, procedure, kind.else_block);
                }
                label(vm, end_of_if_label);
            }
            case IR_Call: {
                switch kind.procedure_name {
                    // todo(josh): proper intrinsics
                    case "__trap": {
                        add_instruction(vm, TRAP{});
                    }
                    case "__print_int": {
                        assert(len(kind.parameters) == 1);
                        p := kind.parameters[0];
                        gen_vm_block(vm, procedure, p.block);
                        add_instruction(vm, PRINT_INT{VM_REGISTER(p.result_register)});
                    }
                    case: {
                        for reg in kind.registers_to_save {
                            add_instruction(vm, PUSH{VM_REGISTER(reg)});
                        }

                        parameter_rsp_offset: i64 = -16; // :CallingConvention the top of the stack for a procedure has 8 bytes for caller rfp and 8 bytes for caller ra
                        for param in kind.parameters {
                            gen_vm_block(vm, procedure, param.block);
                            parameter_rsp_offset -= cast(i64)param.type.size;
                            add_instruction(vm, ADDI{.rt, .rsp, parameter_rsp_offset});
                            switch param.type.size {
                                case 1: add_instruction(vm, STORE8 {.rt, VM_REGISTER(param.result_register)});
                                case 2: add_instruction(vm, STORE16{.rt, VM_REGISTER(param.result_register)});
                                case 4: add_instruction(vm, STORE32{.rt, VM_REGISTER(param.result_register)});
                                case 8: add_instruction(vm, STORE64{.rt, VM_REGISTER(param.result_register)});
                                case: panic(tprint(param.type.size));
                            }
                        }

                        call(vm, kind.procedure_name);

                        if reg, ok := getval(&kind.result_register); ok {
                            add_instruction(vm, POP{VM_REGISTER(reg^)});
                        }

                        for idx := len(kind.registers_to_save)-1; idx >= 0; idx -= 1 {
                            add_instruction(vm, POP{VM_REGISTER(kind.registers_to_save[idx])});
                        }
                    }
                }
            }
            case IR_Take_Address: {
                switch storage_kind in kind.storage_to_take_address_of.kind {
                    case Global_Storage: {
                        add_instruction(vm, MOVI{VM_REGISTER(kind.dst), cast(i64)storage_kind.address});
                    }
                    case Stack_Frame_Storage: {
                        add_instruction(vm, ADDI{VM_REGISTER(kind.dst), .rfp, -cast(i64)(storage_kind.offset_in_stack_frame + cast(u64)kind.storage_to_take_address_of.type_stored.size)});
                    }
                    case: panic(tprint(kind.storage_to_take_address_of));
                }
            }
            case IR_Dereference: {
                gen_vm_load_from_storage(vm, procedure, VM_REGISTER(kind.dst), kind.storage_to_dereference);
                gen_vm_load_from_pointer(vm, procedure, VM_REGISTER(kind.dst), VM_REGISTER(kind.dst), cast(u64)kind.storage_to_dereference.type_stored.kind.(Type_Ptr).ptr_to.size);
            }
            case IR_Return: {
                gen_vm_return(vm, procedure, &kind);
            }

            case: panic(tprint(kind));
        }
    }
}

VM_REGISTER :: proc(r: u64) -> Register {
    return .r1 + Register(r);
}