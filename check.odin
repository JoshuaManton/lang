package main

import "core:fmt"
import "core:mem"

// todo(josh): untyped types

type_i8:  ^Type;
type_i16: ^Type;
type_i32: ^Type;
type_i64: ^Type;

type_u8:  ^Type;
type_u16: ^Type;
type_u32: ^Type;
type_u64: ^Type;

type_f32: ^Type;
type_f64: ^Type;

type_byte:  ^Type;
type_int:   ^Type;
type_uint:  ^Type;
type_float: ^Type;

type_bool: ^Type;

type_string: ^Type;

type_rawptr: ^Type;

type_typeid: ^Type;

// type_untyped_number: ^Type;

all_types: [dynamic]^Type;

init_types :: proc() {
    assert(current_scope != nil);
    assert(global_scope == current_scope);

    // numeric types
    type_i8  = TYPE(make_type(Type_Primitive{}, 1)); register_declaration(global_scope, "i8",  Decl_Type{type_i8});
    type_i16 = TYPE(make_type(Type_Primitive{}, 2)); register_declaration(global_scope, "i16", Decl_Type{type_i16});
    type_i32 = TYPE(make_type(Type_Primitive{}, 4)); register_declaration(global_scope, "i32", Decl_Type{type_i32});
    type_i64 = TYPE(make_type(Type_Primitive{}, 8)); register_declaration(global_scope, "i64", Decl_Type{type_i64});

    type_u8  = TYPE(make_type(Type_Primitive{}, 1)); register_declaration(global_scope, "u8",  Decl_Type{type_u8});
    type_u16 = TYPE(make_type(Type_Primitive{}, 2)); register_declaration(global_scope, "u16", Decl_Type{type_u16});
    type_u32 = TYPE(make_type(Type_Primitive{}, 4)); register_declaration(global_scope, "u32", Decl_Type{type_u32});
    type_u64 = TYPE(make_type(Type_Primitive{}, 8)); register_declaration(global_scope, "u64", Decl_Type{type_u64});

    type_f32 = TYPE(make_type(Type_Primitive{}, 4)); register_declaration(global_scope, "f32", Decl_Type{type_f32});
    type_f64 = TYPE(make_type(Type_Primitive{}, 8)); register_declaration(global_scope, "f64", Decl_Type{type_f64});

    // numeric aliases
    type_byte  = type_u8;  register_declaration(global_scope, "byte",  Decl_Type{type_byte});
    type_int   = type_i64; register_declaration(global_scope, "int",   Decl_Type{type_int});
    type_uint  = type_u64; register_declaration(global_scope, "uint",  Decl_Type{type_uint});
    type_float = type_f64; register_declaration(global_scope, "float", Decl_Type{type_float});

    // "special" types
    type_rawptr = TYPE(make_type(Type_Ptr{nil}, 8)); register_declaration(global_scope, "rawptr", Decl_Type{type_rawptr});
    type_bool = TYPE(make_type(Type_Primitive{}, 1)); register_declaration(global_scope, "bool", Decl_Type{type_bool});
    type_string = TYPE(make_type_struct([]Field{{"data", TYPE(get_or_make_type_ptr_to(type_byte))}, {"length", type_int}})); register_declaration(global_scope, "string", Decl_Type{type_string});
    type_typeid = TYPE(make_type_named("typeid", type_int)); register_declaration(global_scope, "typeid", Decl_Type{type_typeid});

    // untyped types
    // type_untyped_number = TYPE(make_type(Type_Untyped_Number{}, 0));
}

begin_typechecking :: proc() {
    typecheck_scope(global_scope);
    for file in global_scope.nodes {
        if _, ok := file.kind.(Ast_File); !ok do continue;
        for decl in file.kind.(Ast_File).scope.ordered_declarations {
            #partial
            switch kind in decl.kind {
                case Decl_Struct: logf("struct %", kind.structure.name);
                case Decl_Proc:   logf("proc %", kind.procedure.header.name);
                case Decl_Var:    logf("var %", kind.var.name);
            }
        }
    }
}

typecheck_scope :: proc(scope: ^Ast_Scope) {
    for node in scope.nodes {
        typecheck_node(node);
    }
}

typecheck_node :: proc(node: ^Ast_Node, expected_type: ^Type = nil) {
    if node.state == .Resolved {
        return;
    }
    else if node.state == .Resolving {
        panic(twrite("circular dependency: ", node^));
    }

    node.state = .Resolving;

    switch kind in &node.kind {
        case Ast_File:           typecheck_scope(kind.scope);
        case Ast_Scope:          typecheck_scope(&kind);
        case Ast_Var:            typecheck_var(&kind);         assert(kind.type != nil);
        case Ast_Proc:           typecheck_proc(&kind);        assert(kind.header.type != nil);
        case Ast_Proc_Header:    typecheck_proc_header(&kind); assert(kind.type != nil);
        case Ast_If:             typecheck_if(&kind);
        case Ast_While:          typecheck_while(&kind);
        case Ast_For:            typecheck_for(&kind);
        case Ast_Return:         typecheck_return(&kind);
        case Ast_Expr_Statement: typecheck_expr(kind.expr, nil);
        case Ast_Assign:         typecheck_assign(&kind);
        case Ast_Defer:          typecheck_defer(&kind);
        case Ast_Identifier:     assert(false, "should never get here with an Ast_Identifier");
        case Ast_Include:        typecheck_node(NODE(kind.file));
        case Ast_Continue:       // todo(josh): verify that we are inside a loop?
        case Ast_Break:          // todo(josh): verify that we are inside a loop?
        case Ast_Struct: {
            assert(kind.type != nil);
            complete_type(kind.type);
        }
        case Ast_Expr:           typecheck_expr(&kind, expected_type);
        case: panic(twrite(node));
    }

    node.state = .Resolved;

    if node.enclosing_scope.is_file_scope && node.declaration != nil {
        append(&node.enclosing_scope.ordered_declarations, node.declaration);
    }
}

typecheck_identifier :: proc(ident: ^Ast_Identifier) -> Checked_Expr {
    checked: Checked_Expr;
    switch decl in ident.resolved_declaration.kind {
        case Decl_Type: {
            assert(decl.type != nil);
            checked.type = type_typeid;
            checked.mode = .Constant;
            checked.constant_value = decl.type.id;
        }
        case Decl_Struct: {
            assert(decl.structure.type != nil);
            checked.type = type_typeid;
            checked.mode = .Constant;
            checked.constant_value = TYPE(decl.structure.type).id;
        }
        case Decl_Var: {
            typecheck_node(cast(^Ast_Node)decl.var);
            checked.type = decl.var.type;
            if decl.var.is_const {
                assert(decl.var.constant_value != nil);
                checked.constant_value = decl.var.constant_value;
                checked.mode = .Constant;
            }
            else {
                checked.mode = .LValue;
            }
        }
        case Decl_Proc: {
            typecheck_node(cast(^Ast_Node)decl.procedure.header);
            checked.type = TYPE(decl.procedure.header.type);
            checked.mode = .RValue;
        }
        case: panic(twrite(ident));
    }
    assert(checked.type != nil);
    assert(checked.mode != .Invalid);
    return checked;
}

typecheck_var :: proc(var: ^Ast_Var) {
    declared_type: ^Type;
    expr_type: ^Type;
    if var.typespec != nil {
        checked := typecheck_expr(var.typespec, type_typeid);
        declared_type = all_types[checked.constant_value.(TypeID)];
    }
    if var.expr != nil {
        checked_expr := typecheck_expr(var.expr, declared_type);
        assert(checked_expr.type != nil);
        expr_type = checked_expr.type;
    }
    if declared_type == nil && expr_type == nil {
        panic("Must supply either an expression or a type for a var decl");
    }
    if declared_type != nil && expr_type != nil {
        assert(declared_type == expr_type); // todo(josh): we'll need a routine for checking if types are compatible at some point
    }
    if declared_type != nil do var.type = declared_type;
    if expr_type     != nil do var.type = expr_type;
    assert(var.type != nil);

    if var.is_const {
        assert(var.expr != nil);
        assert(var.expr.checked.constant_value != nil, "Constant variables require a constant value expression.");
        var.constant_value = var.expr.checked.constant_value;
        if var.type == type_typeid {
            var.is_type_alias_for = all_types[var.expr.checked.constant_value.(TypeID)];
        }
    }
}

typecheck_typespec :: proc(typespec: ^Expr_Typespec) -> Checked_Expr {
    switch kind in &typespec.kind {
        case Typespec_Identifier: {
            assert(kind.ident != nil);
            assert(kind.ident.resolved_declaration != nil);
            checked_ident := typecheck_identifier(kind.ident);
            assert(checked_ident.type == type_typeid);
            assert(checked_ident.constant_value != nil);
            typespec.type = all_types[checked_ident.constant_value.(TypeID)];
        }
        case Typespec_Ptr: {
            typecheck_typespec(kind.ptr_to);
            assert(kind.ptr_to.type != nil);
            typespec.type = TYPE(get_or_make_type_ptr_to(kind.ptr_to.type));
        }
        case Typespec_Slice: {
            typecheck_typespec(kind.slice_of);
            assert(kind.slice_of.type != nil);
            typespec.type = TYPE(get_or_make_type_slice_of(kind.slice_of.type));
        }
        case Typespec_Array: {
            typecheck_typespec(kind.array_of);
            assert(kind.array_of.type != nil);
            checked_length := typecheck_expr(kind.length, type_int); // todo(josh): allow indexing with other integer types
            assert(checked_length.type != nil);
            assert(checked_length.constant_value != nil);
            constant_size := checked_length.constant_value.(i64);
            typespec.type = TYPE(get_or_make_type_array_of(kind.array_of.type, cast(int)constant_size)); // todo(josh): remove this cast!!!!
        }
        case: panic(twrite(typespec));
    }
    assert(typespec.type != nil);
    checked: Checked_Expr;
    checked.mode = .Constant;
    checked.constant_value = typespec.type.id;
    checked.type = type_typeid;
    expr := EXPR(typespec);
    expr.checked = checked;
    return checked;
}

typecheck_proc :: proc(procedure: ^Ast_Proc) {
    if procedure.is_foreign {
        assert(procedure.block == nil);
    }
    else {
        assert(procedure.block != nil);
        typecheck_scope(procedure.block);
    }

    typecheck_node(cast(^Ast_Node)procedure.header);
    assert(procedure.header.type != nil);
}

typecheck_proc_header :: proc(header: ^Ast_Proc_Header) {
    param_types: [dynamic]^Type;
    for param in header.params {
        typecheck_var(param);
        assert(param.type != nil);
        append(&param_types, param.type);
    }
    return_type: ^Type;
    if header.return_typespec != nil { typecheck_typespec(header.return_typespec); return_type = header.return_typespec.type; }
    header.type = make_type_proc(param_types[:], return_type);
}

typecheck_return :: proc(return_statement: ^Ast_Return) {
    if return_statement.expr != nil {
        declared_return_type := NODE(return_statement).enclosing_procedure.header.type;
        assert(declared_return_type != nil);
        checked_return := typecheck_expr(return_statement.expr, TYPE(declared_return_type.return_type));
        assert(checked_return.type != nil);
        assert(NODE(return_statement).enclosing_procedure.header.return_typespec.type == checked_return.type);
    }
}

typecheck_if :: proc(if_statement: ^Ast_If) {
    checked_condition := typecheck_expr(if_statement.condition, type_bool);
    assert(checked_condition.type != nil);
    assert(checked_condition.type == type_bool);
    typecheck_scope(if_statement.body);
    if if_statement.else_stmt != nil {
        typecheck_node(if_statement.else_stmt);
    }
}

typecheck_while :: proc(while_loop: ^Ast_While) {
    checked_condition := typecheck_expr(while_loop.condition, type_bool);
    assert(checked_condition.type != nil);
    assert(checked_condition.type == type_bool);
    typecheck_scope(while_loop.body);
}

typecheck_for :: proc(for_loop: ^Ast_For) {
    typecheck_node(for_loop.pre_statement);
    checked_condition := typecheck_expr(for_loop.condition, type_bool);
    typecheck_node(for_loop.post_statement);
    assert(checked_condition.type != nil);
    assert(checked_condition.type == type_bool);
    typecheck_scope(for_loop.body);
}

typecheck_assign :: proc(assign: ^Ast_Assign) {
    checked_lhs := typecheck_expr(assign.lhs, nil);
    assert(checked_lhs.type != nil);
    checked_rhs := typecheck_expr(assign.rhs, checked_lhs.type);
    assert(checked_rhs.type != nil);
    assert(checked_lhs.type == checked_rhs.type);
    assert(checked_lhs.mode == .LValue);
    assert(checked_rhs.mode != .No_Value);
}

typecheck_defer :: proc(defer_statement: ^Ast_Defer) {
    assert(defer_statement.stmt != nil);
    typecheck_node(defer_statement.stmt);
}

Checked_Expr :: struct {
    type: ^Type,
    constant_value: Constant_Value,
    mode: Addressing_Mode,
}

typecheck_expr :: proc(expr: ^Ast_Expr, expected_type: ^Type) -> Checked_Expr {
    checked: Checked_Expr;
    switch kind in &expr.kind {
        case Expr_Binary: {
            checked_lhs := typecheck_expr(kind.lhs, nil); // todo(josh): should we pass the expected_type through here? I think so.
            checked_rhs := typecheck_expr(kind.rhs, nil); // todo(josh): should we pass the expected_type through here? I think so.
            complete_type(checked_lhs.type);
            complete_type(checked_rhs.type);
            assert(checked_lhs.mode != .No_Value);
            assert(checked_rhs.mode != .No_Value);
            assert(checked_lhs.type != nil);
            assert(checked_lhs.type == checked_rhs.type);

            switch kind.op {
                case .Plus: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of + must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of + must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val + checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val + checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Minus: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of - must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of - must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val - checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val - checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Multiply: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of * must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of * must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val * checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val * checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Divide: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of / must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of / must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val / checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val / checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Mod: {
                    assert(is_integer_type(checked_lhs.type), "LHS of % must be an integer type.");
                    assert(is_integer_type(checked_lhs.type), "RHS of % must be an integer type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type; // todo(josh): make sure left and right are both integers
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val % checked_rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Mod_Mod: {
                    assert(is_integer_type(checked_lhs.type), "LHS of %% must be an integer type.");
                    assert(is_integer_type(checked_lhs.type), "RHS of %% must be an integer type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type; // todo(josh): make sure left and right are both integers
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val %% checked_rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Shift_Left: {
                    assert(is_unsigned_integer_type(checked_lhs.type), "LHS of << must be an unsigned integer.");
                    assert(is_unsigned_integer_type(checked_lhs.type), "RHS of << must be an unsigned integer.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type; // todo(josh): make sure left and right are both integers
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        // todo(josh): constant values
                        unimplemented();
                    }
                }
                case .Shift_Right: {
                    assert(is_unsigned_integer_type(checked_lhs.type), "LHS of >> must be an unsigned integer.");
                    assert(is_unsigned_integer_type(checked_lhs.type), "RHS of >> must be an unsigned integer.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        // todo(josh): constant values
                        unimplemented();
                    }
                }
                case .Bit_Xor: {
                    assert(is_unsigned_integer_type(checked_lhs.type), "LHS of ~ must be an unsigned integer.");
                    assert(is_unsigned_integer_type(checked_lhs.type), "RHS of ~ must be an unsigned integer.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type; // todo(josh): make sure left and right are both integers
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val ~ checked_rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Bit_And: {
                    assert(is_unsigned_integer_type(checked_lhs.type), "LHS of & must be an unsigned integer.");
                    assert(is_unsigned_integer_type(checked_lhs.type), "RHS of & must be an unsigned integer.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type; // todo(josh): make sure left and right are both integers
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val & checked_rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Bit_Or: {
                    assert(is_unsigned_integer_type(checked_lhs.type), "LHS of | must be an unsigned integer.");
                    assert(is_unsigned_integer_type(checked_lhs.type), "RHS of | must be an unsigned integer.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = checked_lhs.type; // todo(josh): make sure left and right are both integers
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val | checked_rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Equal_To: {
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val == checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val == checked_rhs.constant_value.(f64);
                            case string: checked.constant_value = val == checked_rhs.constant_value.(string);
                            case bool:   checked.constant_value = val == checked_rhs.constant_value.(bool);
                            case TypeID: checked.constant_value = val == checked_rhs.constant_value.(TypeID);
                        }
                    }
                }
                case .Not_Equal: {
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val != checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val != checked_rhs.constant_value.(f64);
                            case string: checked.constant_value = val != checked_rhs.constant_value.(string);
                            case bool:   checked.constant_value = val != checked_rhs.constant_value.(bool);
                            case TypeID: checked.constant_value = val != checked_rhs.constant_value.(TypeID);
                        }
                    }
                }
                case .Less: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of < must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of < must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val < checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val < checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Greater: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of > must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of > must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val > checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val > checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Less_Equal: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of <= must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of <= must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val <= checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val <= checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Greater_Equal: {
                    assert(is_numeric_type(checked_lhs.type), "LHS of >= must be a numeric type.");
                    assert(is_numeric_type(checked_lhs.type), "RHS of >= must be a numeric type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    checked.constant_value = val >= checked_rhs.constant_value.(i64);
                            case f64:    checked.constant_value = val >= checked_rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .And: {
                    assert(is_bool_type(checked_lhs.type), "LHS of && must be a bool type.");
                    assert(is_bool_type(checked_lhs.type), "RHS of && must be a bool type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    panic("wat");
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   checked.constant_value = val && checked_rhs.constant_value.(bool);
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Or: {
                    assert(is_bool_type(checked_lhs.type), "LHS of || must be a bool type.");
                    assert(is_bool_type(checked_lhs.type), "RHS of || must be a bool type.");
                    assert(checked_lhs.type == checked_rhs.type);
                    checked.type = type_bool;
                    if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                        switch val in checked_lhs.constant_value {
                            case i64:    panic("wat");
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   checked.constant_value = val || checked_rhs.constant_value.(bool);
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Not: panic("no unary ops here");
                case .Bit_Not: panic("no unary here");
                case: unimplemented(twrite(kind.op));
            }

            if checked_lhs.constant_value != nil && checked_rhs.constant_value != nil {
                assert(checked.constant_value != nil);
                checked.mode = .Constant;
            }
            else {
                assert(checked.constant_value == nil);
                checked.mode = .RValue;
            }
        }
        case Expr_Address_Of: {
            checked_rhs := typecheck_expr(kind.rhs, nil); // todo(josh): should we pass an expected type here?
            assert(checked_rhs.type != nil);
            assert(checked_rhs.mode == .LValue, "Cannot take the address of a non-lvalue.");
            checked.type = TYPE(get_or_make_type_ptr_to(checked_rhs.type));
            checked.mode = .RValue;
        }
        case Expr_Dereference: {
            checked_lhs := typecheck_expr(kind.lhs, nil); // todo(josh): should we pass an expected type here?
            complete_type(checked_lhs.type);
            lhs_type := checked_lhs.type;
            ptr, ok := checked_lhs.type.kind.(Type_Ptr);
            assert(ok);
            assert(ptr.ptr_to != nil);
            checked.type = ptr.ptr_to;
            checked.mode = .LValue;
        }
        case Expr_Cast: {
            // todo(josh): constant values
            typecheck_typespec(kind.typespec);
            assert(kind.typespec.type != nil);
            complete_type(kind.typespec.type);
            checked_rhs := typecheck_expr(kind.rhs, nil);
            assert(checked_rhs.type != nil);
            complete_type(checked_rhs.type);

            ok := can_do_cast(checked_rhs.type, kind.typespec.type);
            assert(ok, "cannot do cast");

            checked.type = kind.typespec.type;
            checked.mode = .RValue;

            can_do_cast :: proc(source, target: ^Type) -> bool {
                if is_pointer_type(source) && is_pointer_type(target) do return true;
                if is_numeric_type(source) && is_numeric_type(target) do return true;
                return false;
            }
        }
        case Expr_Unary: {
            checked_rhs := typecheck_expr(kind.rhs, nil); // todo(josh): should we pass an expected type here?
            complete_type(checked_rhs.type);
            assert(checked_rhs.type != nil);
            #partial
            switch kind.op {
                case .Not: { // !
                    assert(checked_rhs.type == type_bool);
                    checked.type = type_bool;
                    if checked_rhs.constant_value != nil {
                        checked.constant_value = !checked_rhs.constant_value.(bool);
                    }
                }
                case .Minus: {
                    assert(is_signed_integer_type(checked_rhs.type) || is_float_type(checked_rhs.type));
                    checked.type = checked_rhs.type;
                    if checked_rhs.constant_value != nil {
                        #partial
                        switch val in checked_rhs.constant_value {
                            case i64: checked.constant_value = -val;
                            case f64: checked.constant_value = -val;
                        }
                    }
                }
                case .Plus: {
                    // pretty much a no-op right now
                    assert(is_signed_integer_type(checked_rhs.type) || is_float_type(checked_rhs.type));
                    checked.type = checked_rhs.type;
                    checked.constant_value = checked_rhs.constant_value;
                }
                case .Bit_Not: {
                    assert(is_integer_type(checked_rhs.type));
                    checked.type = checked_rhs.type;
                    if checked_rhs.constant_value != nil {
                        switch val in checked_rhs.constant_value {
                            case i64:    checked.constant_value = ~val;
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case: unimplemented(twrite(kind.op));
            }

            if checked_rhs.constant_value != nil {
                assert(checked.constant_value != nil);
                checked.mode = .Constant;
            }
            else {
                checked.mode = .RValue;
            }
        }
        case Expr_Number: {
            if expected_type != nil {
                assert(is_numeric_type(expected_type));
                checked.type = expected_type;
                switch {
                    case is_float_type  (expected_type): checked.constant_value = kind.float_value;
                    case is_integer_type(expected_type): checked.constant_value = cast(i64)kind.int_value;
                    case: panic("wat");
                }
            }
            else {
                if kind.has_a_dot {
                    checked.type = type_float;
                    checked.constant_value = kind.float_value;
                }
                else {
                    checked.type = type_int;
                    checked.constant_value = cast(i64)kind.int_value;
                }
            }
            assert(checked.constant_value != nil);
            checked.mode = .Constant;
        }
        case Expr_Size_Of: {
            checked_size_of := typecheck_expr(kind.thing_to_get_the_size_of, nil);
            complete_type(checked_size_of.type);
            size: int;
            if checked_size_of.type == type_typeid {
                true_type := all_types[checked_size_of.constant_value.(TypeID)];
                size = true_type.size;
            }
            else {
                size = checked_size_of.type.size;
            }
            checked.type = type_int;
            checked.mode = .Constant;
            checked.constant_value = cast(i64)size;
        }
        case Expr_Type_Of: {
            checked_expr := typecheck_expr(kind.thing_to_get_the_type_of, nil);
            checked.type = type_typeid;
            checked.mode = .Constant;
            checked.constant_value = checked_expr.type.id;
        }
        case Expr_Selector: {
            checked_lhs := typecheck_expr(kind.lhs, nil); // todo(josh): should we pass an expected type here?
            complete_type(checked_lhs.type);
            assert(checked_lhs.type != nil);
            structure, ok := checked_lhs.type.kind.(Type_Struct);
            assert(ok);

            type_of_field: ^Type;
            for field in structure.fields {
                if field.name == kind.ident.name {
                    type_of_field = field.type;
                    break;
                }
            }
            assert(type_of_field != nil);
            checked.type = type_of_field;
            checked.mode = .LValue;
        }
        case Expr_Subscript: {
            // todo(josh): constant values

            checked_lhs := typecheck_expr(kind.lhs, nil);
            complete_type(checked_lhs.type);
            array_type, ok := checked_lhs.type.kind.(Type_Array);
            assert(ok, "need array for lhs"); // todo(josh): error handling

            // todo(josh): handle different integer types: byte, i32, u16, etc
            checked_index := typecheck_expr(kind.index, type_int);
            assert(is_integer_type(checked_index.type), "need int for index expr");
            complete_type(checked_index.type);

            checked.type = array_type.array_of;
            checked.mode = .LValue;
        }
        case Expr_String: {
            checked.type = type_string;
            checked.mode = .Constant;
            checked.constant_value = kind.str;
        }
        case Expr_Call: {
            checked_proc := typecheck_expr(kind.procedure_expr, nil);
            assert(checked_proc.type != nil);
            proc_type, ok := checked_proc.type.kind.(Type_Proc);
            assert(ok);
            assert(len(proc_type.param_types) == len(kind.params));
            for param, idx in kind.params {
                target_type := proc_type.param_types[idx];
                assert(target_type != nil);

                checked_param := typecheck_expr(param, target_type);
                assert(checked_param.type != nil);
                assert(checked_param.type == target_type);
            }

            if proc_type.return_type != nil {
                checked.type = proc_type.return_type;
                checked.mode = .RValue;
            }
            else {
                checked.mode = .No_Value;
            }
        }
        case Expr_Identifier: {
            checked = typecheck_identifier(kind.ident);
        }
        case Expr_Typespec: {
            checked = typecheck_typespec(&kind);
        }
        case Expr_Null: {
            checked.mode = .Constant;
            unimplemented();
        }
        case Expr_True:  checked.type = type_bool; checked.mode = .Constant; checked.constant_value = true;
        case Expr_False: checked.type = type_bool; checked.mode = .Constant; checked.constant_value = false;
        case Expr_Paren: {
            checked = typecheck_expr(kind.expr, expected_type);
        }
        case: panic(twrite(expr));
    }

    if expected_type != nil && checked.type != nil && expected_type != checked.type {
        fmt.println("-------------------------------");
        fmt.println(expr.kind);
        fmt.println(checked);
        fmt.println(expected_type);
        panic("expr.type didn't match expected_type:");
    }

    if checked.mode != .No_Value {
        assert(checked.type != nil);
    }
    assert(checked.mode != .Invalid);
    expr.checked = checked;
    return checked;
}



is_pointer_type :: proc(t: ^Type) -> bool {
    _, ok := t.kind.(Type_Ptr);
    return ok;
}
is_numeric_type :: proc(t: ^Type) -> bool {
    return is_integer_type(t) || is_float_type(t);
}
is_integer_type :: proc(t: ^Type) -> bool {
    switch t {
        case type_i8, type_i16, type_i32, type_i64, type_u8, type_u16, type_u32, type_u64: return true;
    }
    return false;
}
is_float_type :: proc(t: ^Type) -> bool {
    switch t {
        case type_f32, type_f64: return true;
    }
    return false;
}
is_signed_integer_type :: proc(t: ^Type) -> bool {
    switch t {
        case type_i8, type_i16, type_i32, type_i64: return true;
    }
    return false;
}
is_unsigned_integer_type :: proc(t: ^Type) -> bool {
    switch t {
        case type_u8, type_u16, type_u32, type_u64: return true;
    }
    return false;
}
is_bool_type :: proc(t: ^Type) -> bool {
    switch t {
        case type_bool: return true;
    }
    return false;
}



TYPE_MAGIC :: 789162976;
Type :: struct {
    kind: union {
        Type_Incomplete,
        Type_Primitive,
        Type_Untyped_Number,
        Type_Named,
        Type_Struct,
        Type_Ptr,
        Type_Slice,
        Type_Array,
        Type_Proc,
    },
    id:    TypeID,
    size:  int,
    align: int,
    magic: int,
    state: Resolve_State,
}

Type_Incomplete :: struct {
    node: ^Ast_Node,
}

Type_Primitive :: struct {

}

Type_Untyped_Number :: struct {

}

Type_Named :: struct {
    name: string,
    base: ^Type,
}

Type_Struct :: struct {
    fields: []Field,
    offsets: []int,
}
Field :: struct {
    name: string,
    type: ^Type,
}

Type_Ptr :: struct {
    ptr_to: ^Type,
}

Type_Slice :: struct {
    slice_of: ^Type,
}

Type_Array :: struct {
    array_of: ^Type,
    length: int,
}

Type_Proc :: struct {
    param_types: []^Type,
    return_type: ^Type,
}

TYPE :: proc(k: ^$T) -> ^Type {
    t := cast(^Type)k;
    assert(t.magic == TYPE_MAGIC);
    return t;
}

make_incomplete_type :: proc(node: ^Ast_Node) -> ^Type {
    t := new(Type);
    t.kind = Type_Incomplete{node};
    t.magic = TYPE_MAGIC;
    t.id = cast(TypeID)len(all_types);
    append(&all_types, t);
    return t;
}

make_type :: proc(kind: $T, size: int, align := -1) -> ^T {
    t := make_incomplete_type(nil);
    t.kind = kind;
    complete_type_size_align(t, size, align);
    return cast(^T)t;
}

complete_type :: proc(t: ^Type) {
    if t.state == .Resolved {
        return;
    }
    else if t.state == .Resolving {
        panic("circular type dependency");
    }

    _, ok := t.kind.(Type_Incomplete);
    assert(ok);

    incomplete := &t.kind.(Type_Incomplete);
    assert(incomplete.node != nil);

    t.state = .Resolving;

    #partial
    switch kind in &incomplete.node.kind {
        case Ast_Struct: {
            fields: [dynamic]Field;
            for field in kind.fields {
                typecheck_var(field);
                assert(field.type != nil);
                append(&fields, Field{field.name, field.type});
            }
            append(&incomplete.node.enclosing_scope.ordered_declarations, incomplete.node.declaration);
            complete_type_struct(t, fields[:]);
        }
        case: panic(twrite(incomplete.node.kind));
    }

    t.state = .Resolved;
}

complete_type_size_align :: proc(t: ^Type, size: int, align: int) {
    size := size;
    align := align;

    // note(josh): this won't handle every case in the universe, but it is plenty good enough
    if size == 0 do size = 1;
    if align == -1 do align = next_power_of_two(size);

    // note(josh): This means that a string, for example, even though it has a "true" size of 12,
    // will have an actual size of 16. This automatically makes the type work for arrays, but it
    // will result is extra padding if you have a thing of this type in a struct
    // For more information, watch May 4th, 2020 stream, 3 hours 34 minutes.
    t.size = mem.align_forward_int(size, align);
    assert(t.size % align == 0);
    t.align = align;
    t.state = .Resolved;
}

make_type_struct :: proc(fields: []Field) -> ^Type_Struct {
    t := make_incomplete_type(nil);
    complete_type_struct(t, fields);
    return &t.kind.(Type_Struct);
}

complete_type_struct :: proc(t: ^Type, fields: []Field) {
    offsets := make([]int, len(fields));
    size := 0;
    largest_alignment := 1;
    for field, idx in fields {
        next_alignment := -1;
        if idx < len(fields)-1 {
            next := &fields[idx+1];
            next_alignment = next.type.align;
        }

        size_delta := field.type.size;
        if next_alignment != -1 {
            // todo(josh): do we need %% here or just %
            size_delta += (next_alignment - field.type.size) %% next_alignment;
        }
        offsets[idx] = size;
        // logf("field %, offset %", field.name, size);
        size += size_delta;
        largest_alignment = max(largest_alignment, field.type.align);
    }
    t.kind = Type_Struct{fields, offsets};
    complete_type_size_align(t, size, largest_alignment);
}

make_type_proc :: proc(param_types: []^Type, return_type: ^Type) -> ^Type_Proc {
    return make_type(Type_Proc{param_types, return_type}, 8);
}

make_type_named :: proc(name: string, type: ^Type) -> ^Type_Named {
    return make_type(Type_Named{name, type}, type.size);
}

get_or_make_type_ptr_to :: proc(type: ^Type) -> ^Type_Ptr {
    for other in all_types {
        if _, ok := other.kind.(Type_Ptr); ok {
            other_ptr := &other.kind.(Type_Ptr);
            if other_ptr.ptr_to == type {
                return other_ptr;
            }
        }
    }
    return make_type(Type_Ptr{type}, type_rawptr.size);
}

get_or_make_type_slice_of :: proc(type: ^Type) -> ^Type_Slice {
    for other in all_types {
        if _, ok := other.kind.(Type_Slice); ok {
            other_slice := &other.kind.(Type_Slice);
            if other_slice.slice_of == type {
                return other_slice;
            }
        }
    }
    return make_type(Type_Slice{type}, type_rawptr.size + type_int.size);
}

get_or_make_type_array_of :: proc(type: ^Type, length: int) -> ^Type_Array {
    for other in all_types {
        if _, ok := other.kind.(Type_Array); ok {
            other_array := &other.kind.(Type_Array);
            if other_array.array_of == type && other_array.length == length {
                return other_array;
            }
        }
    }
    return make_type(Type_Array{type, length}, type.size * length);
}



next_power_of_two :: proc(x: int) -> int {
    k := x -1;
    when size_of(int) == 8 {
        k = k | (k >> 32);
    }
    k = k | (k >> 16);
    k = k | (k >> 8);
    k = k | (k >> 4);
    k = k | (k >> 2);
    k = k | (k >> 1);
    k += 1 + int(x <= 0);
    return k;
}