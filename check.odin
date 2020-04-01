package main

import "core:fmt"

type_i8: ^Type;
type_i16: ^Type;
type_i32: ^Type;
type_i64: ^Type;

type_u8: ^Type;
type_u16: ^Type;
type_u32: ^Type;
type_u64: ^Type;

type_f32: ^Type;
type_f64: ^Type;

type_byte: ^Type;
type_int: ^Type;
type_uint: ^Type;
type_float: ^Type;

type_bool: ^Type;
type_string: ^Type;

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
    type_int   = type_i32; register_declaration(global_scope, "int",   Decl_Type{type_int});
    type_uint  = type_u32; register_declaration(global_scope, "uint",  Decl_Type{type_uint});
    type_float = type_f32; register_declaration(global_scope, "float", Decl_Type{type_float});

    // "special" types
    type_bool = TYPE(make_type(Type_Primitive{}, 1)); register_declaration(global_scope, "bool", Decl_Type{type_bool});

    type_string = TYPE(make_type_struct([]Field{{"data", TYPE(get_or_make_type_ptr_to(type_byte))}, {"length", type_int}})); register_declaration(global_scope, "string", Decl_Type{type_string});
}

TYPE :: proc(k: ^$T) -> ^Type {
    t := cast(^Type)k;
    assert(t.magic == TYPE_MAGIC);
    return t;
}

make_type :: proc(kind: $T, size: int) -> ^T {
    t := new(Type);
    t.kind = kind;
    t.size = size;
    t.magic = TYPE_MAGIC;
    append(&all_types, t);
    return cast(^T)t;
}

make_type_struct :: proc(fields: []Field) -> ^Type_Struct {
    size := 0;
    for field in fields do size += field.type.size;
    assert(size != 0);
    return make_type(Type_Struct{fields}, size);
}

make_type_proc :: proc(param_types: []^Type, return_type: ^Type) -> ^Type_Proc {
    return make_type(Type_Proc{param_types, return_type}, 8);
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
    return make_type(Type_Ptr{type}, 8);
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
    return make_type(Type_Slice{type}, 16);
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

typecheck_file :: proc(file: ^Ast_File) {
    typecheck_scope(file.block);
}

typecheck_scope :: proc(scope: ^Ast_Scope) {
    for node in scope.nodes {
        typecheck_node(node);
    }
}

typecheck_node :: proc(node: ^Ast_Node) {
    switch kind in &node.kind {
        case Ast_File:           typecheck_file(&kind);
        case Ast_Scope:          typecheck_scope(&kind);
        case Ast_Identifier:     typecheck_identifier(&kind); assert(kind.type != nil);
        case Ast_Var:            typecheck_var(&kind);        assert(kind.type != nil);
        case Ast_Proc:           typecheck_proc(&kind);       assert(kind.type != nil);
        case Ast_Struct:         typecheck_struct(&kind);     assert(kind.type != nil);
        case Ast_If:             typecheck_if(&kind);
        case Ast_Return:         typecheck_return(&kind);
        case Ast_Expr:           panic("there should be no Ast_Exprs here, only Ast_Expr_Statements");
        case Ast_Expr_Statement: typecheck_expr(kind.expr);
        case Ast_Typespec:       typecheck_typespec(&kind);   assert(kind.type != nil);
        case Ast_Assign: {
            assert(kind.op == .Assign); // todo(josh): handle +=, -=, <<=, etc
            typecheck_expr(kind.lhs); assert(kind.lhs.type != nil);
            typecheck_expr(kind.rhs); assert(kind.rhs.type != nil);
            assert(kind.lhs.type == kind.rhs.type);
            assert(kind.lhs.mode == .LValue);
            assert(kind.rhs.mode != .No_Value);
        }
        case: panic(tprint(node));
    }
}

typecheck_identifier :: proc(ident: ^Ast_Identifier) {
    switch decl in ident.resolved_declaration.kind {
        case Decl_Type:   ident.type = decl.type;
        case Decl_Struct: ident.type = TYPE(decl.structure.type);
        case Decl_Proc:   ident.type = TYPE(decl.procedure.type);
        case Decl_Var:    ident.type = decl.var.type;
        case: panic(tprint(ident.resolved_declaration));
    }
    assert(ident.type != nil);
}

typecheck_var :: proc(var: ^Ast_Var) {
    typespec_type: ^Type;
    expr_type: ^Type;
    if var.typespec != nil { typecheck_typespec(var.typespec); assert(var.typespec.type != nil); typespec_type = var.typespec.type; }
    if var.expr     != nil { typecheck_expr(var.expr);         assert(var.expr.type != nil);     expr_type     = var.expr.type;     }
    if typespec_type == nil && expr_type == nil {
        panic("Must supply either an expression or a type for a var decl");
    }
    if typespec_type != nil && expr_type != nil {
        assert(typespec_type == expr_type);
    }
    if typespec_type != nil do var.type = typespec_type;
    if expr_type     != nil do var.type = expr_type;
    assert(var.type != nil);
}

typecheck_typespec :: proc(typespec: ^Ast_Typespec) {
    switch kind in &typespec.kind {
        case Typespec_Identifier: {
            assert(kind.ident != nil);
            typecheck_identifier(kind.ident);
            assert(kind.ident.type != nil);
            assert(kind.ident.resolved_declaration != nil);
            #partial
            switch decl in kind.ident.resolved_declaration.kind {
                case Decl_Type:   typespec.type = decl.type;
                case Decl_Struct: typespec.type = TYPE(decl.structure.type);
                case: panic(fmt.tprint(decl, "used as a type when it is not a type"));
            }
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
            typespec.type = TYPE(get_or_make_type_array_of(kind.array_of.type, kind.length.kind.(Expr_Number).int_value));
        }
        case: panic(tprint(typespec));
    }
    assert(typespec.type != nil);
}

typecheck_proc :: proc(procedure: ^Ast_Proc) {
    param_types: [dynamic]^Type;
    for param in procedure.params {
        typecheck_var(param);
        assert(param.type != nil);
        append(&param_types, param.type);
    }
    return_type: ^Type;
    if procedure.return_typespec != nil { typecheck_typespec(procedure.return_typespec); return_type = procedure.return_typespec.type; }
    procedure.type = make_type_proc(param_types[:], return_type);

    if procedure.is_foreign {
        assert(procedure.block == nil);
    }
    else {
        assert(procedure.block != nil);
        typecheck_scope(procedure.block);
    }
}

typecheck_struct :: proc(structure: ^Ast_Struct) {
    fields: [dynamic]Field;
    for field in structure.fields {
        typecheck_var(field);
        assert(field.type != nil);
        append(&fields, Field{field.name, field.type});
    }
    structure.type = make_type_struct(fields[:]);
}

typecheck_if :: proc(if_statement: ^Ast_If) {
    typecheck_expr(if_statement.condition);
    assert(if_statement.condition.type != nil);
    assert(if_statement.condition.type == type_bool);
    typecheck_scope(if_statement.body);

    for else_if in if_statement.else_ifs {
        typecheck_if(else_if);
    }

    if if_statement.else_body != nil {
        typecheck_scope(if_statement.else_body);
    }
}

typecheck_return :: proc(return_statement: ^Ast_Return) {
    if return_statement.expr != nil {
        typecheck_expr(return_statement.expr);
        assert(return_statement.expr.type != nil);
        assert(NODE(return_statement).enclosing_procedure.return_typespec.type == return_statement.expr.type);
    }
}

typecheck_expr :: proc(expr: ^Ast_Expr) {
    switch kind in expr.kind {
        case Expr_Binary: {
            typecheck_expr(kind.lhs);
            typecheck_expr(kind.rhs);
            assert(kind.lhs.mode != .No_Value);
            assert(kind.rhs.mode != .No_Value);
            lhs_type := kind.lhs.type;
            rhs_type := kind.rhs.type;
            assert(lhs_type != nil);
            assert(lhs_type == rhs_type);

            switch kind.op {
                case .Multiply:      expr.type = lhs_type;
                case .Divide:        expr.type = lhs_type;
                case .Mod:           expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                case .Mod_Mod:       expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                case .Shift_Left:    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                case .Shift_Right:   expr.type = lhs_type; // todo(josh): make sure left and right are both integers

                case .Plus:          expr.type = lhs_type;
                case .Minus:         expr.type = lhs_type;
                case .Bit_Xor:       expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                case .Bit_And:       expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                case .Bit_Or:        expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                case .Bit_Not:       expr.type = lhs_type; // todo(josh): make sure left and right are both integers

                case .Equal_To:      expr.type = type_bool;
                case .Not_Equal:     expr.type = type_bool;
                case .Less:          expr.type = type_bool;
                case .Greater:       expr.type = type_bool;
                case .Less_Equal:    expr.type = type_bool;
                case .Greater_Equal: expr.type = type_bool;
                case .And:           expr.type = type_bool;
                case .Or:            expr.type = type_bool;
                case .Not: panic("no unary ops here");
                case: unimplemented(fmt.tprint(kind.op));
            }

            expr.mode = .RValue;
        }
        case Expr_Address_Of: {
            typecheck_expr(kind.rhs);
            assert(kind.rhs.type != nil);
            assert(kind.rhs.mode == .LValue);
            rhs_type := kind.rhs.type;
            expr.type = TYPE(get_or_make_type_ptr_to(rhs_type));
            expr.mode = .RValue;
        }
        case Expr_Dereference: {
            typecheck_expr(kind.lhs);
            lhs_type := kind.lhs.type;
            ptr, ok := lhs_type.kind.(Type_Ptr);
            assert(ok);
            assert(ptr.ptr_to != nil);
            expr.type = ptr.ptr_to;
            expr.mode = .LValue;
        }
        case Expr_Unary: {
            typecheck_expr(kind.rhs);
            rhs_type := kind.rhs.type;
            assert(rhs_type != nil);
            #partial
            switch kind.op {
                case .Not:       assert(rhs_type == type_bool); expr.type = type_bool;
                case .Minus:     expr.type = rhs_type;
                case .Plus:      expr.type = rhs_type;
                case: unimplemented(fmt.tprint(kind.op));
            }
            expr.mode = .RValue;
        }
        case Expr_Number: {
            // todo(josh): support more than just ints
            expr.type = type_int;
            expr.mode = .RValue;
        }
        case Expr_Selector: {
            typecheck_expr(kind.lhs);
            assert(kind.lhs.type != nil);
            structure, ok := kind.lhs.type.kind.(Type_Struct);
            assert(ok);

            type_of_field: ^Type;
            for field in structure.fields {
                if field.name == kind.field {
                    type_of_field = field.type;
                    break;
                }
            }
            assert(type_of_field != nil);
            expr.type = type_of_field;
            expr.mode = .LValue;
        }
        case Expr_Subscript: {
            typecheck_expr(kind.lhs);
            typecheck_expr(kind.index);
            assert(kind.lhs.type != nil);
            assert(kind.index.type != nil);

            array_type, ok := kind.lhs.type.kind.(Type_Array);
            assert(ok, "need array for lhs"); // todo(josh): error handling
            assert(is_integer_type(kind.index.type), "need int for index expr"); // todo(josh): handle different integer types: byte, i32, u16, etc

            expr.type = array_type.array_of;
            expr.mode = .LValue;
        }
        case Expr_String: {
            expr.type = type_string;
            expr.mode = .RValue;
        }
        case Expr_Call: {
            typecheck_expr(kind.procedure_expr);
            assert(kind.procedure_expr.type != nil);
            proc_type, ok := kind.procedure_expr.type.kind.(Type_Proc);
            assert(ok);
            assert(len(proc_type.param_types) == len(kind.params));
            for param, idx in kind.params {
                typecheck_expr(param);
                assert(param.type != nil);

                target_type := proc_type.param_types[idx];
                assert(target_type != nil);
                assert(param.type == target_type);
            }

            if proc_type.return_type != nil {
                expr.type = proc_type.return_type;
                expr.mode = .RValue;
            }
            else {
                expr.mode = .No_Value;
            }
        }
        case Expr_Identifier: {
            typecheck_identifier(kind.ident);
            assert(kind.ident.type != nil);
            expr.type = kind.ident.type;
            expr.mode = .LValue;
        }
        case Expr_Null: {
            unimplemented();
            expr.mode = .RValue;
        }
        case Expr_True:  expr.type = type_bool; expr.mode = .RValue;
        case Expr_False: expr.type = type_bool; expr.mode = .RValue;
        case Expr_Paren: {
            typecheck_expr(kind.expr);
            assert(kind.expr != nil);
            expr.type = kind.expr.type;
            expr.mode = kind.expr.mode;
        }
        case: panic(tprint(expr));
    }
}

get_type_through_declaration :: proc(decl: ^Declaration) -> ^Type {
    switch decl in decl.kind {
        case Decl_Type:   return decl.type;
        case Decl_Var:    return decl.var.type;
        case Decl_Proc:   return TYPE(decl.procedure.type);
        case Decl_Struct: return TYPE(decl.structure.type);
        case: panic(tprint(decl));
    }
    unreachable();
    return {};
}



is_integer_type :: proc(t: ^Type) -> bool {
    switch t {
        case type_i8, type_i16, type_i32, type_i64, type_u8, type_u16, type_u32, type_u64: return true;
    }
    return false;
}



TYPE_MAGIC :: 789162976;
Type :: struct {
    kind: union {
        Type_Primitive,
        Type_Struct,
        Type_Ptr,
        Type_Slice,
        Type_Array,
        Type_Proc,
    },
    size: int,
    magic: int,
}

Type_Primitive :: struct {

}

Type_Struct :: struct {
    fields: []Field,
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