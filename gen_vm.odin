package main

import "core:reflect"

translate_ir_to_vm :: proc(ir: ^IR_Result) -> ^VM {
    vm := make_vm();

    for procedure in ir.procedures {
        // :EntryPoint
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
            add_instruction(vm, MOVI{.rt, VM_GLOBAL_STORAGE_BEGIN + cast(i64)kind.offset}); // todo(josh): this kind.offset could probably be an immediate
            gen_vm_load_from_pointer(vm, procedure, dst, .rt, cast(u64)storage.type_stored.size);
        }
        case Indirect_Storage: {
            #partial
            switch pointer_storage in kind.storage_of_pointer.kind {
                case Register_Storage: {
                    // for handling rvalues that produce a pointer like (&foo)^
                    gen_vm_load_from_pointer(vm, procedure, dst, VM_REGISTER(pointer_storage.register), cast(u64)kind.storage_of_pointer.type_stored.kind.(Type_Ptr).ptr_to.size);
                }
                case: {
                    gen_vm_load_from_storage(vm, procedure, dst, kind.storage_of_pointer);
                    gen_vm_load_from_pointer(vm, procedure, dst, dst, cast(u64)kind.storage_of_pointer.type_stored.kind.(Type_Ptr).ptr_to.size);
                }
            }
        }
        case Register_Storage: {
            panic("This is would mean a stupid register copy, please handle the case at the call-site where `storage` is already a register.");
        }
        case: panic(twrite(storage));
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

gen_vm_store_to_storage :: proc(vm: ^VM, procedure: ^IR_Proc, dst: ^IR_Storage, src: Register) {
    switch storage_kind in dst.kind {
        case Stack_Frame_Storage: {
            add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(storage_kind.offset_in_stack_frame + cast(u64)dst.type_stored.size)});
            gen_vm_store_to_pointer(vm, procedure, .rt, src, cast(u64)dst.type_stored.size);
        }
        case Global_Storage: {
            add_instruction(vm, MOVI{.rt, VM_GLOBAL_STORAGE_BEGIN + cast(i64)storage_kind.offset});
            gen_vm_store_to_pointer(vm, procedure, .rt, src, cast(u64)dst.type_stored.size);
        }
        case Indirect_Storage: {
            #partial
            switch pointer_storage in storage_kind.storage_of_pointer.kind {
                case Register_Storage: {
                    // for handling rvalues that produce a pointer like (&foo)^
                    gen_vm_store_to_pointer(vm, procedure, VM_REGISTER(pointer_storage.register), src, cast(u64)dst.type_stored.size);
                }
                case: {
                    gen_vm_load_from_storage(vm, procedure, .rt, storage_kind.storage_of_pointer);
                    gen_vm_store_to_pointer(vm, procedure, .rt, src, cast(u64)dst.type_stored.size);
                }
            }
        }
        case Register_Storage: {
            panic("what does this mean, storing to a register? sounds wack");
        }
        case: panic(twrite(dst));
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

/*
gen_vm_copy :: proc(vm: ^VM, dst: ^IR_Storage, src: ^IR_Storage) {
    switch dst_kind in dst.kind {
        case Register_Storage: {
            switch src_kind in src.kind {
                case Register_Storage: {
                    add_instruction(vm, MOV{VM_REGISTER(dst_kind.register), VM_REGISTER(src_kind.register)});
                }
                case Stack_Frame_Storage: {
                    add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(src_kind.offset_in_stack_frame + cast(u64)src.type_stored.size)});
                    gen_vm_load_from_pointer(vm, VM_REGISTER(dst_kind.register), .rt, cast(u64)src.type_stored.size);
                }
                case Global_Storage: {
                    assert(src_kind.address != 0);
                    add_instruction(vm, MOVI{.rt, VM_GLOBAL_STORAGE_BEGIN + cast(i64)src_kind.address}); // todo(josh): this src_kind.address could probably be an immediate
                    gen_vm_load_from_pointer(vm, VM_REGISTER(dst_kind.register), .rt, cast(u64)src.type_stored.size);
                }
                case Indirect_Storage: {
                    gen_vm_copy(vm, dst, src_kind.storage_of_pointer);
                    gen_vm_load_from_pointer(vm, VM_REGISTER(dst_kind.register), VM_REGISTER(dst_kind.register), cast(u64)src_kind.storage_of_pointer.type_stored.kind.(Type_Ptr).ptr_to.size);
                }
                case: panic("");
            }
        }
        case Stack_Frame_Storage: {
            switch src_kind in src.kind {
                case Register_Storage: {
                    add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(dst_kind.offset_in_stack_frame + cast(u64)dst.type_stored.size)});
                    gen_vm_store_to_pointer(vm, .rt, VM_REGISTER(src_kind.register), cast(u64)dst.type_stored.size);
                }
                case Stack_Frame_Storage: {
                }
                case Global_Storage: {
                }
                case Indirect_Storage: {
                }
                case: panic("");
            }
        }
        case Global_Storage: {

        }
        case Indirect_Storage: {

        }
    }
}
*/

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

    // generate the body
    vm_comment(vm, "body");
    gen_vm_block(vm, procedure, procedure.block);

    // :EntryPoint
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
            add_instruction(vm, PUSH{VM_REGISTER(reg^.register)});
        }
    }

    add_instruction(vm, MOV{.rip, .ra});
}

gen_vm_block :: proc(vm: ^VM, procedure: ^IR_Proc, block: ^IR_Block) {
    for inst in &block.instructions {
        vm_comment(vm, awrite(reflect.union_variant_type_info(inst.kind)));
        switch kind in &inst.kind {
            case IR_Move_Immediate: {
                switch val in kind.value {
                    case i64: add_instruction(vm, MOVI{VM_REGISTER(kind.dst.register),  val});
                    case f64: add_instruction(vm, MOVIF{VM_REGISTER(kind.dst.register), val});
                    case: panic(twrite(val));
                }
            }
            case IR_Store: gen_vm_store_to_storage(vm, procedure, kind.storage, VM_REGISTER(kind.reg.register));
            case IR_Load:  gen_vm_load_from_storage(vm, procedure, VM_REGISTER(kind.dst.register), kind.storage);
            case IR_Binop: {
                switch kind.op {
                    case .Plus: {
                        if is_integer_type(kind.type) {
                            add_instruction(vm, ADD{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                        else {
                            assert(is_float_type(kind.type));
                            add_instruction(vm, ADDF{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                    }
                    case .Minus: {
                        if is_integer_type(kind.type) {
                            add_instruction(vm, SUB{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                        else {
                            assert(is_float_type(kind.type));
                            add_instruction(vm, SUBF{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                    }
                    case .Multiply: {
                        if is_integer_type(kind.type) {
                            add_instruction(vm, MUL{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                        else {
                            assert(is_float_type(kind.type));
                            add_instruction(vm, MULF{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                    }
                    case .Divide: {
                        if is_signed_integer_type(kind.type) {
                            add_instruction(vm, DIVS{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                        else if is_unsigned_integer_type(kind.type) {
                            add_instruction(vm, DIVU{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                        else {
                            assert(is_float_type(kind.type));
                            add_instruction(vm, DIVF{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                        }
                    }
                    case .Mod: {
                        add_instruction(vm, MOD{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Mod_Mod: {
                        add_instruction(vm, MODMOD{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Shift_Left: {
                        add_instruction(vm, SHL{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Shift_Right: {
                        add_instruction(vm, SHR{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Bit_Xor: {
                        add_instruction(vm, BWXOR{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Bit_Or: {
                        add_instruction(vm, BWOR{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Bit_And: {
                        add_instruction(vm, BWAND{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Bit_Not: {
                        add_instruction(vm, BWNOT{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register)});
                    }
                    case .Equal_To: {
                        add_instruction(vm, EQ{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Not_Equal: {
                        add_instruction(vm, NEQ{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Not: {
                        unimplemented();
                    }
                    case .Less: {
                        add_instruction(vm, LT{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Greater: {
                        add_instruction(vm, LTE{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.rhs.register), VM_REGISTER(kind.lhs.register)});
                    }
                    case .Less_Equal: {
                        add_instruction(vm, LTE{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.lhs.register), VM_REGISTER(kind.rhs.register)});
                    }
                    case .Greater_Equal: {
                        add_instruction(vm, LT{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.rhs.register), VM_REGISTER(kind.lhs.register)});
                    }
                    case .And: {
                        unimplemented();
                    }
                    case .Or: {
                        unimplemented();
                    }
                    case: panic(twrite(kind));
                }
            }
            case IR_Unary: {
                #partial
                switch kind.op {
                    case .Minus: {
                        add_instruction(vm, SUB{VM_REGISTER(kind.dst.register), .rz, VM_REGISTER(kind.rhs.register)});
                    }
                    case .Not: {
                        add_instruction(vm, EQ{VM_REGISTER(kind.dst.register), VM_REGISTER(kind.rhs.register), .rz});
                    }
                    case: panic(twrite(kind.op));
                }
            }
            case IR_If: {
                end_of_if_label := awrite("if_", kind.s);
                else_label := awrite("if_else_", kind.s);
                if kind.else_block != nil {
                    add_instruction(vm, GOTOIFZ{VM_REGISTER(kind.condition_reg.register), else_label});
                }
                else {
                    add_instruction(vm, GOTOIFZ{VM_REGISTER(kind.condition_reg.register), end_of_if_label});
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
                    case "__trap": {
                        add_instruction(vm, TRAP{});
                    }
                    case "__print_int": {
                        assert(len(kind.parameters) == 1);
                        p := kind.parameters[0];
                        gen_vm_block(vm, procedure, p.block);
                        add_instruction(vm, PRINT_INT{VM_REGISTER(p.result_register.register)});
                    }
                    case "__print_float": {
                        assert(len(kind.parameters) == 1);
                        p := kind.parameters[0];
                        gen_vm_block(vm, procedure, p.block);
                        add_instruction(vm, PRINT_FLOAT{VM_REGISTER(p.result_register.register)});
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
                                case 1: add_instruction(vm, STORE8 {.rt, VM_REGISTER(param.result_register.register)});
                                case 2: add_instruction(vm, STORE16{.rt, VM_REGISTER(param.result_register.register)});
                                case 4: add_instruction(vm, STORE32{.rt, VM_REGISTER(param.result_register.register)});
                                case 8: add_instruction(vm, STORE64{.rt, VM_REGISTER(param.result_register.register)});
                                case: panic(twrite(param.type.size));
                            }
                        }

                        call(vm, kind.procedure_name);

                        if reg, ok := getval(&kind.result_register); ok {
                            add_instruction(vm, POP{VM_REGISTER(reg^.register)});
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
                        add_instruction(vm, MOVI{VM_REGISTER(kind.dst.register), VM_GLOBAL_STORAGE_BEGIN + cast(i64)storage_kind.offset});
                    }
                    case Stack_Frame_Storage: {
                        add_instruction(vm, ADDI{VM_REGISTER(kind.dst.register), .rfp, -cast(i64)(storage_kind.offset_in_stack_frame + cast(u64)kind.storage_to_take_address_of.type_stored.size)});
                    }
                    case Register_Storage: {
                        panic("Cannot take address of something with register storage.");
                    }
                    case Indirect_Storage: {
                        panic("I don't think this makes any sense? Maybe &foo^? Kinda weird");
                    }
                    case: panic(twrite(kind.storage_to_take_address_of));
                }
            }
            case IR_Return: {
                gen_vm_return(vm, procedure, &kind);
            }

            case: panic(twrite(kind));
        }
    }
}

VM_REGISTER :: proc(r: u64) -> Register {
    return .r1 + Register(r);
}