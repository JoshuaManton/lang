package main

import "core:fmt"

IR_Result :: struct {
    procedures: [dynamic]^IR_Proc,
    global_variables: [dynamic]^IR_Var,
    data_segment_size: u64, // todo(josh): handle alignment
}

IR_Proc :: struct {
    name: string,
    parameters: [dynamic]^IR_Var,
    stack_frame_size: u64,
    block: ^IR_Block,
    register_freelist: [dynamic]u64,
}

IR_Var :: struct {
    procedure: ^IR_Proc, // note(josh): nil for global vars
    storage: IR_Storage,
    type: ^Type,
}

IR_Block :: struct {
    instructions: [dynamic]IR_Instruction,
}

IR_Storage :: struct {
    kind: union {
        Stack_Frame_Storage,
        Global_Storage,
    },
}
Stack_Frame_Storage :: struct {
    procedure: ^IR_Proc,
    offset_in_stack_frame: u64,
    size: u64,
}
Global_Storage :: struct {
    offset_in_data_segment: u64,
    size: u64,
}

IR_Instruction :: struct {
    kind: IR_Instruction_Kind,
}
IR_Instruction_Kind :: union {
    IR_Binop,
    IR_Unary,
    IR_Store,
    IR_Load,
    IR_Move_Immediate,
    IR_If,
    IR_Call,
    IR_Return,
}

IR_Call :: struct {
    parameters: [dynamic]Call_Parameter,
    procedure_name: string, // todo(josh): handle function pointers
    result_register: Maybe(u64),
}
Call_Parameter :: struct {
    block: ^IR_Block,
    result_register: u64,
    type: ^Type,
}

IR_If :: struct {
    condition_reg: u64,
    s: int,
    block: ^IR_Block,
    else_block: ^IR_Block,
}
IR_Unary :: struct {
    op: Operator,
    dst: u64,
    rhs: u64,
}
IR_Binop :: struct {
    op: Operator,
    dst: u64,
    lhs: u64,
    rhs: u64,
}
IR_Return :: struct {
    result_register: Maybe(u64),
    type: ^Type,
}
IR_Move_Immediate :: struct {
    dst: u64,
    value: union {
        i64,
        f64,
        u64,
    },
}
IR_Store :: struct {
    storage: IR_Storage,
    reg: u64,
}
IR_Load :: struct {
    storage: IR_Storage,
    dst: u64,
}
IR_Push :: struct {
    dst: u64,
    type: ^Type,
}

current_block: ^IR_Block;

@(deferred_out=pop_ir_block)
PUSH_IR_BLOCK :: proc(new_block: ^IR_Block) -> ^IR_Block {
    old := current_block;
    current_block = new_block;
    return old;
}

pop_ir_block :: proc(old: ^IR_Block) {
    current_block = old;
}

generate_ir :: proc() -> ^IR_Result {
    ir := new(IR_Result);

    for node in global_scope.nodes {
        file := node.kind.(Ast_File);
        for node in file.block.nodes {
            #partial
            switch kind in &node.kind {
                case Ast_Proc: gen_ir_proc(ir, &kind);
                case Ast_Var:  gen_ir_var(ir, &kind, nil);
            }
        }
    }

    return ir;
}

gen_ir_proc :: proc(ir: ^IR_Result, ast_procedure: ^Ast_Proc) -> ^IR_Proc {
    ir_procedure := new(IR_Proc);
    assert(ast_procedure.name != "");
    ir_procedure.name = ast_procedure.name;

    append(&ir_procedure.register_freelist, 2);
    append(&ir_procedure.register_freelist, 1);
    append(&ir_procedure.register_freelist, 0);
    append(&ir.procedures, ir_procedure);

    for var in ast_procedure.variables {
        ir_var := gen_ir_var(ir, var, ir_procedure);
        if var.is_parameter {
            append(&ir_procedure.parameters, ir_var);
        }
    }

    ir_procedure.block = new(IR_Block);

    PUSH_IR_BLOCK(ir_procedure.block);
    gen_ir_scope(ir, ir_procedure, ast_procedure.block);

    return ir_procedure;
}

gen_ir_scope :: proc(ir: ^IR_Result, procedure: ^IR_Proc, scope: ^Ast_Scope) {
    for node in scope.nodes {
        gen_ir_statement(ir, procedure, node);
    }

    for idx := len(scope.all_defers)-1; idx >= 0; idx -= 1 {
        defer_stmt := scope.all_defers[idx];
        gen_ir_statement(ir, procedure, defer_stmt.stmt);
    }
}

gen_ir_statement :: proc(ir: ^IR_Result, procedure: ^IR_Proc, node: ^Ast_Node) {
    switch stmt in &node.kind {
        case Ast_Scope:  gen_ir_scope(ir, procedure, &stmt);
        case Ast_Proc:   gen_ir_proc(ir, &stmt);
        case Ast_Assign: gen_ir_assign(procedure, &stmt);
        case Ast_If:     gen_ir_if(ir, procedure, &stmt);
        case Ast_Var: {
            if stmt.expr != nil {
                panic("we do not handle inline variable initializers");
            }
        }
        case Ast_Expr_Statement: {
            reg := gen_ir_expr(procedure, stmt.expr, false);
            free_register(procedure, reg); // :^)
        }
        case Ast_Return: {
            ret: IR_Return;
            if stmt.expr != nil {
                reg := gen_ir_expr(procedure, stmt.expr);
                ret.result_register = reg;
                ret.type = stmt.expr.type;
                free_register(procedure, reg); // todo(josh): is freeing this immediately the correct thing?
            }
            ir_inst(procedure, ret);
        }
        case Ast_While:          panic("Ast_While");
        case Ast_For:            panic("Ast_For");
        case Ast_Continue:       panic("Ast_Continue");
        case Ast_Break:          panic("Ast_Break");

        case Ast_Defer:  // skip, handled separately in gen_ir_scope()
        case Ast_Struct: // skip, no need for IR for structs
        case Ast_Expr:       panic("Shouldn't be any expressions at statement level.");
        case Ast_Typespec:   panic("Shouldn't be any typespecs at statement level.");
        case Ast_Identifier: panic("Shouldn't be any identifiers at statement level.");
        case Ast_File: panic(tprint(stmt));
        case: panic(tprint(stmt));
    }
}

gen_ir_if :: proc(ir: ^IR_Result, procedure: ^IR_Proc, iff: ^Ast_If) {
    cond := gen_ir_expr(procedure, iff.condition);
    defer free_register(procedure, cond);
    ir_if: IR_If;
    ir_if.s = NODE(iff).s;
    ir_if.block = new(IR_Block);
    ir_if.else_block = new(IR_Block);
    ir_if.condition_reg = cond;
    ir_inst(procedure, ir_if);

    // main block
    {
        PUSH_IR_BLOCK(ir_if.block);
        gen_ir_scope(ir, procedure, iff.body);
    }

    // else block
    {
        PUSH_IR_BLOCK(ir_if.else_block);
        gen_ir_scope(ir, procedure, &iff.else_stmt.kind.(Ast_Scope)); // todo(josh): handle single-liners
    }
}

gen_ir_assign :: proc(procedure: ^IR_Proc, assign: ^Ast_Assign) {
    result := gen_ir_expr(procedure, assign.rhs);
    defer free_register(procedure, result);
    storage := get_storage_for_expr(assign.lhs);
    gen_ir_store(procedure, storage, result);
}

gen_ir_store :: proc(procedure: ^IR_Proc, storage: IR_Storage, reg: u64) {
    ir_inst(procedure, IR_Store{storage, reg});
}

gen_ir_load :: proc(procedure: ^IR_Proc, storage: IR_Storage, dst: u64) {
    ir_inst(procedure, IR_Load{storage, dst});
}

ir_inst :: proc(procedure: ^IR_Proc, instruction: IR_Instruction_Kind) {
    assert(current_block != nil);
    append(&current_block.instructions, IR_Instruction{instruction});
}

get_storage_for_expr :: proc(expr: ^Ast_Expr) -> IR_Storage {
    #partial
    switch kind in expr.kind {
        case Expr_Identifier: {
            #partial
            switch decl in kind.ident.resolved_declaration.kind {
                case Decl_Var: {
                    assert(decl.var.storage.kind != nil);
                    return decl.var.storage;
                }
                case: panic(tprint(decl)); // todo(josh): error logging
            }
        }
        case: panic(tprint(kind));
    }
    unreachable();
    return {};
}

gen_ir_expr :: proc(procedure: ^IR_Proc, expr: ^Ast_Expr, require_result := true) -> u64 {
    switch kind in expr.kind {
        case Expr_Number: {
            dst := alloc_register(procedure);
            switch expr.type {
                case type_i64: ir_inst(procedure, IR_Move_Immediate{dst, kind.int_value});
                case type_int: ir_inst(procedure, IR_Move_Immediate{dst, kind.int_value});
                case: panic(tprint(expr.type));
            }
            return dst;
        }
        case Expr_Binary: {
            lhs_reg := gen_ir_expr(procedure, kind.lhs);
            defer free_register(procedure, lhs_reg);
            rhs_reg := gen_ir_expr(procedure, kind.rhs);
            defer free_register(procedure, rhs_reg);
            dst := alloc_register(procedure);
            ir_inst(procedure, IR_Binop{kind.op, dst, lhs_reg, rhs_reg});
            return dst;
        }
        case Expr_Identifier: {
            storage := get_storage_for_expr(expr);
            dst := alloc_register(procedure);
            gen_ir_load(procedure, storage, dst);
            return dst;
        }
        case Expr_Call: {
            ir_call: IR_Call;
            for p in kind.params {
                param: Call_Parameter;
                param.block = new(IR_Block);
                param.type = p.type;
                PUSH_IR_BLOCK(param.block);
                param.result_register = gen_ir_expr(procedure, p);
                defer free_register(procedure, param.result_register);
                append(&ir_call.parameters, param);
            }
            #partial
            switch kind in kind.procedure_expr.kind {
                case Expr_Identifier: {
                    ir_call.procedure_name = kind.ident.name;
                }
                case: {
                    unimplemented(); // todo(josh): handle function pointer calls
                }
            }

            if expr.mode == .No_Value {
                assert(expr.type == nil);
                assert(require_result == false);
                ir_inst(procedure, ir_call);
                return 0;
            }
            else {
                assert(expr.type != nil);
                proc_type := &kind.procedure_expr.type.kind.(Type_Proc);
                assert(proc_type.return_type != nil);
                result := alloc_register(procedure);
                ir_call.result_register = result;
                ir_inst(procedure, ir_call);
                return result;
            }
        }
        case Expr_Unary: {
            #partial
            switch kind.op {
                case .Minus: {
                    expr_reg := gen_ir_expr(procedure, kind.rhs);
                    defer free_register(procedure, expr_reg);
                    dst := alloc_register(procedure);
                    ir_inst(procedure, IR_Unary{kind.op, dst, expr_reg});
                    return dst;
                }
                case: panic(tprint(kind.op));
            }
        }
        case Expr_String:      panic("Expr_String");
        case Expr_Selector:    panic("Expr_Selector");
        case Expr_Subscript:   panic("Expr_Subscript");
        case Expr_Cast:        panic("Expr_Cast");
        case Expr_Null:        panic("Expr_Null");
        case Expr_True:        panic("Expr_True");
        case Expr_False:       panic("Expr_False");
        case Expr_Paren:       panic("Expr_Paren");
        case Expr_Address_Of:  panic("Expr_Address_Of");
        case Expr_Dereference: panic("Expr_Dereference");
        case: panic(tprint(kind));
    }
    unreachable();
    return 0;
}

alloc_register :: proc(procedure: ^IR_Proc) -> u64 {
    reg := pop(&procedure.register_freelist);
    return reg;
}

free_register :: proc(procedure: ^IR_Proc, reg: u64) {
    append(&procedure.register_freelist, reg);
}

gen_ir_var :: proc(ir: ^IR_Result, var: ^Ast_Var, procedure: ^IR_Proc) -> ^IR_Var {
    if procedure == nil {
        ir_var := make_ir_var(var, IR_Storage{Global_Storage{ir.data_segment_size, cast(u64)var.type.size}});
        ir.data_segment_size += cast(u64)ir_var.type.size; // todo(josh): handle alignment
        append(&ir.global_variables, ir_var);
        return ir_var;
    }
    else {
        ir_var := make_ir_var(var, IR_Storage{Stack_Frame_Storage{procedure, procedure.stack_frame_size, cast(u64)var.type.size}});
        procedure.stack_frame_size += cast(u64)ir_var.type.size; // todo(josh): handle alignment
        ir_var.procedure = procedure;
        return ir_var;
    }
    unreachable();
    return {};
}

make_ir_var :: proc(var: ^Ast_Var, storage: IR_Storage) -> ^IR_Var {
    var.storage = storage;
    ir_var := new(IR_Var);
    assert(var.type != nil);
    ir_var.type = var.type;
    ir_var.storage = storage;
    return ir_var;
}

translate_ir_to_vm :: proc(ir: ^IR_Result) -> ^VM {
    vm := make_vm();

    for procedure in ir.procedures {
        if procedure.name == "main" {
            vm.entry_point = cast(u64)len(vm.instructions);
        }

        function_header(vm, procedure.name);

        gen_vm_block(vm, procedure.block);

        for idx := len(procedure.parameters)-1; idx >= 0; idx -= 1 {
            param := procedure.parameters[idx];
            assert(param.type.size == 4 || param.type.size == 8);
            add_instruction(vm, POP{.rz});
        }

        if procedure.name == "main" {
            add_instruction(vm, ADDI{.rt, .rfp, -4});
            add_instruction(vm, LOAD32{.r1, .rt});
            add_instruction(vm, PRINT_REG{.r1});

            add_instruction(vm, EXIT{});
        }

        ret(vm);
    }

    execute_vm(vm);
    return vm;
}

arr: [32]int;

gen_vm_block :: proc(vm: ^VM, block: ^IR_Block) {
    for inst in &block.instructions {
        switch kind in &inst.kind {
            case IR_Move_Immediate: add_instruction(vm, MOVI{VM_REGISTER(kind.dst), kind.value.(i64)});
            case IR_Store: {
                // todo(josh): handle global storage
                switch storage in kind.storage.kind {
                    case Stack_Frame_Storage: {
                        add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(storage.offset_in_stack_frame + storage.size)});
                        switch storage.size {
                            case 1: add_instruction(vm, STORE8 {.rt, VM_REGISTER(kind.reg)});
                            case 2: add_instruction(vm, STORE16{.rt, VM_REGISTER(kind.reg)});
                            case 4: add_instruction(vm, STORE32{.rt, VM_REGISTER(kind.reg)});
                            case 8: add_instruction(vm, STORE64{.rt, VM_REGISTER(kind.reg)});
                        }
                    }
                    case Global_Storage: {
                        offset := vm_allocate_static_storage(vm, cast(int)storage.size);
                        add_instruction(vm, MOVI{.rt, cast(i64)offset});
                        switch storage.size {
                            case 1: add_instruction(vm, STORE8 {.rt, VM_REGISTER(kind.reg)});
                            case 2: add_instruction(vm, STORE16{.rt, VM_REGISTER(kind.reg)});
                            case 4: add_instruction(vm, STORE32{.rt, VM_REGISTER(kind.reg)});
                            case 8: add_instruction(vm, STORE64{.rt, VM_REGISTER(kind.reg)});
                        }
                    }
                    case: panic(tprint(storage));
                }
            }
            case IR_Load: {
                switch storage in kind.storage.kind {
                    case Stack_Frame_Storage: {
                        add_instruction(vm, ADDI{.rt, .rfp, -cast(i64)(storage.offset_in_stack_frame + storage.size)});
                        switch storage.size {
                            case 1: add_instruction(vm, LOAD8 {VM_REGISTER(kind.dst), .rt});
                            case 2: add_instruction(vm, LOAD16{VM_REGISTER(kind.dst), .rt});
                            case 4: add_instruction(vm, LOAD32{VM_REGISTER(kind.dst), .rt});
                            case 8: add_instruction(vm, LOAD64{VM_REGISTER(kind.dst), .rt});
                        }
                    }
                    case Global_Storage: {
                        unimplemented();
                    }
                    case: panic(tprint(storage));
                }
            }
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
                    case: panic(tprint(kind.op));
                }
            }
            case IR_If: {
                end_of_if_label := aprint("if_", kind.s);
                else_label := aprint("if_else_", kind.s);
                add_instruction(vm, GOTOIFZ{VM_REGISTER(kind.condition_reg), else_label});
                gen_vm_block(vm, kind.block);
                add_instruction(vm, GOTO{end_of_if_label});
                label(vm, else_label);
                gen_vm_block(vm, kind.else_block);
                label(vm, end_of_if_label);
            }
            case IR_Call: {
                add_instruction(vm, PUSH{.rfp});
                add_instruction(vm, PUSH{.ra});

                for param in kind.parameters {
                    gen_vm_block(vm, param.block);
                    assert(param.type.size == 4 || param.type.size == 8);
                    add_instruction(vm, PUSH{VM_REGISTER(param.result_register)});
                }

                call(vm, kind.procedure_name);

                if reg, ok := getval(&kind.result_register); ok {
                    add_instruction(vm, POP{VM_REGISTER(reg^)});
                }

                add_instruction(vm, POP{.ra});
                add_instruction(vm, POP{.rfp});
            }
            case IR_Return: {
                if reg, ok := getval(&kind.result_register); ok {
                    assert(kind.type.size == 4 || kind.type.size == 8);
                    add_instruction(vm, PUSH{VM_REGISTER(reg^)});
                }
                ret(vm);
            }

            case: panic(tprint(kind));
        }
    }
}

VM_REGISTER :: proc(r: u64) -> Register {
    return .r1 + Register(r);
}
