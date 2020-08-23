package main

import "core:fmt"
import "core:mem"

// todo(josh): untyped types

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

type_byte:  ^Type;
type_int:   ^Type;
type_uint:  ^Type;
type_float: ^Type;

type_bool: ^Type;

type_string: ^Type;

type_rawptr: ^Type;

type_typeid: ^Type;

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
    type_rawptr = TYPE(make_type(Type_Ptr{nil}, 8)); register_declaration(global_scope, "rawptr", Decl_Type{type_rawptr});
    type_bool = TYPE(make_type(Type_Primitive{}, 1)); register_declaration(global_scope, "bool", Decl_Type{type_bool});
    type_string = TYPE(make_type_struct([]Field{{"data", TYPE(get_or_make_type_ptr_to(type_byte))}, {"length", type_int}})); register_declaration(global_scope, "string", Decl_Type{type_string});
    type_typeid = TYPE(make_type_named("typeid", type_int)); register_declaration(global_scope, "typeid", Decl_Type{type_typeid});
}

TYPE :: proc(k: ^$T) -> ^Type {
    t := cast(^Type)k;
    assert(t.magic == TYPE_MAGIC);
    return t;
}

make_type :: proc(kind: $T, size: int, align := -1, loc := #caller_location) -> ^T {
    assert(size > 0);

    align := align;

    // note(josh): this won't handle every case in the universe, but it is plenty good enough
    if align == -1 do align = next_power_of_two(size);

    t := new(Type);
    t.kind = kind;

    // todo(josh): This means that a string, for example, even though it has a "true" size of 12,
    // will have an actual size of 16. This automatically makes the type work for arrays, but it
    // will result is extra padding if you have a thing of this type in a struct
    // For more information, watch May 4th, 2020 stream, 3 hours 34 minutes.
    t.size = mem.align_forward_int(size, align);
    assert(t.size % align == 0);
    t.align = align;
    t.magic = TYPE_MAGIC;
    t.id = cast(TypeID)len(all_types);
    append(&all_types, t);

    return cast(^T)t;
}

make_type_struct :: proc(fields: []Field, loc := #caller_location) -> ^Type_Struct {
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
    if size == 0 do size = 1;
    return make_type(Type_Struct{fields, offsets}, size, largest_alignment, loc);
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

typecheck_scope :: proc(scope: ^Ast_Scope) {
    for node in scope.nodes {
        typecheck_node(node);
    }
}

typecheck_node :: proc(node: ^Ast_Node) {
    switch kind in &node.kind {
        case Ast_Scope:          typecheck_scope(&kind);
        case Ast_Var:            typecheck_var(&kind);        assert(kind.type != nil);
        case Ast_Proc:           typecheck_proc(&kind);       assert(kind.type != nil);
        case Ast_Struct:         typecheck_struct(&kind);     assert(kind.type != nil);
        case Ast_If:             typecheck_if(&kind);
        case Ast_While:          typecheck_while(&kind);
        case Ast_For:            typecheck_for(&kind);
        case Ast_Return:         typecheck_return(&kind);
        case Ast_Expr_Statement: typecheck_expr(kind.expr, nil);
        case Ast_Assign:         typecheck_assign(&kind);
        case Ast_Defer:          typecheck_defer(&kind);
        case Ast_Identifier:     assert(kind.resolved_declaration != nil);
        case Ast_Include:        // do nothing
        case Ast_Continue:       // do nothing
        case Ast_Break:          // do nothing
        case Ast_Expr:     panic("there should be no Ast_Exprs here, only Ast_Expr_Statements");
        case: panic(tprint(node));
    }
}

/*
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
*/

typecheck_var :: proc(var: ^Ast_Var) {
    typespec_type: ^Type;
    expr_type: ^Type;
    if var.typespec != nil {
        typecheck_typespec(var.typespec);
        assert(var.typespec.type != nil);
        typespec_type = var.typespec.type;
    }
    if var.expr != nil {
        typecheck_expr(var.expr, typespec_type);
        assert(var.expr.type != nil);
        expr_type = var.expr.type;
    }
    if typespec_type == nil && expr_type == nil {
        panic("Must supply either an expression or a type for a var decl");
    }
    if typespec_type != nil && expr_type != nil {
        assert(typespec_type == expr_type); // todo(josh): we'll need a routine for checking if types are compatible at some point
    }
    if typespec_type != nil do var.type = typespec_type;
    if expr_type     != nil do var.type = expr_type;
    assert(var.type != nil);

    if var.is_const {
        assert(var.expr != nil);
        assert(var.expr.constant_value != nil);
        var.constant_value = var.expr.constant_value;

        if var.type == type_typeid {
            var.is_type_alias_for = all_types[var.expr.constant_value.(TypeID)];
        }
    }
}

typecheck_typespec :: proc(typespec: ^Expr_Typespec) {
    switch kind in &typespec.kind {
        case Typespec_Identifier: {
            assert(kind.ident != nil);
            assert(kind.ident.resolved_declaration != nil);
            #partial
            switch decl in kind.ident.resolved_declaration.kind {
                case Decl_Type:   typespec.type = decl.type;
                case Decl_Struct: typespec.type = TYPE(decl.structure.type);
                case Decl_Var: {
                    if decl.var.is_type_alias_for != nil {
                        typespec.type = decl.var.is_type_alias_for;
                    }
                    else {
                        panic(fmt.tprint(decl, "used as a type when it is not a type"));
                    }
                }
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
            typecheck_expr(kind.length, type_int);
            assert(kind.length.type != nil);
            assert(kind.length.constant_value != nil);
            constant_size := kind.length.constant_value.(i64);
            typespec.type = TYPE(get_or_make_type_array_of(kind.array_of.type, cast(int)constant_size)); // todo(josh): remove this cast!!!!
        }
        case: panic(tprint(typespec));
    }
    assert(typespec.type != nil);
    expr := EXPR(typespec);
    expr.mode = .Constant;
    expr.constant_value = typespec.type.id;
    expr.type = type_typeid;
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
    assert(procedure.type != nil);
}

typecheck_return :: proc(return_statement: ^Ast_Return) {
    if return_statement.expr != nil {
        declared_return_type := NODE(return_statement).enclosing_procedure.type;
        assert(declared_return_type != nil);
        typecheck_expr(return_statement.expr, TYPE(declared_return_type.return_type));
        assert(return_statement.expr.type != nil);
        assert(NODE(return_statement).enclosing_procedure.return_typespec.type == return_statement.expr.type);
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
    typecheck_expr(if_statement.condition, type_bool);
    assert(if_statement.condition.type != nil);
    assert(if_statement.condition.type == type_bool);
    typecheck_scope(if_statement.body);
    if if_statement.else_stmt != nil {
        typecheck_node(if_statement.else_stmt);
    }
}

typecheck_while :: proc(while_loop: ^Ast_While) {
    typecheck_expr(while_loop.condition, type_bool);
    assert(while_loop.condition.type != nil);
    assert(while_loop.condition.type == type_bool);
    typecheck_scope(while_loop.body);
}

typecheck_for :: proc(for_loop: ^Ast_For) {
    typecheck_node(for_loop.pre_statement);
    typecheck_expr(for_loop.condition, type_bool);
    typecheck_node(for_loop.post_statement);
    assert(for_loop.condition.type != nil);
    assert(for_loop.condition.type == type_bool);
    typecheck_scope(for_loop.body);
}

typecheck_assign :: proc(assign: ^Ast_Assign) {
    typecheck_expr(assign.lhs, nil); assert(assign.lhs.type != nil);
    typecheck_expr(assign.rhs, assign.lhs.type); assert(assign.rhs.type != nil);
    assert(assign.lhs.type == assign.rhs.type);
    assert(assign.lhs.mode == .LValue);
    assert(assign.rhs.mode != .No_Value);
}

typecheck_defer :: proc(defer_statement: ^Ast_Defer) {
    assert(defer_statement.stmt != nil);
    typecheck_node(defer_statement.stmt);
}

typecheck_expr :: proc(expr: ^Ast_Expr, expected_type: ^Type) {
    switch kind in &expr.kind {
        case Expr_Binary: {
            typecheck_expr(kind.lhs, nil); // todo(josh): should we pass the expected_type through here? I think so.
            typecheck_expr(kind.rhs, nil); // todo(josh): should we pass the expected_type through here? I think so.
            assert(kind.lhs.mode != .No_Value);
            assert(kind.rhs.mode != .No_Value);
            lhs_type := kind.lhs.type;
            rhs_type := kind.rhs.type;
            assert(lhs_type != nil);
            assert(lhs_type == rhs_type);

            switch kind.op {
                case .Multiply: {
                    expr.type = lhs_type;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val * kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val * kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Divide: {
                    expr.type = lhs_type;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val / kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val / kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Mod: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val % kind.rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Mod_Mod: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val %% kind.rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Shift_Left: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        // todo(josh): constant values
                    }
                }
                case .Shift_Right: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        // todo(josh): constant values
                    }
                }
                case .Plus: {
                    expr.type = lhs_type;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val + kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val + kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Minus: {
                    expr.type = lhs_type;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val - kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val - kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Bit_Xor: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val ~ kind.rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Bit_And: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val & kind.rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Bit_Or: {
                    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val | kind.rhs.constant_value.(i64);
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Equal_To: { // true == false
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val == kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val == kind.rhs.constant_value.(f64);
                            case string: expr.constant_value = val == kind.rhs.constant_value.(string);
                            case bool:   expr.constant_value = val == kind.rhs.constant_value.(bool);
                            case TypeID: expr.constant_value = val == kind.rhs.constant_value.(TypeID);
                        }
                    }
                }
                case .Not_Equal: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val != kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val != kind.rhs.constant_value.(f64);
                            case string: expr.constant_value = val != kind.rhs.constant_value.(string);
                            case bool:   expr.constant_value = val != kind.rhs.constant_value.(bool);
                            case TypeID: expr.constant_value = val != kind.rhs.constant_value.(TypeID);
                        }
                    }
                }
                case .Less: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val < kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val < kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Greater: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val > kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val > kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Less_Equal: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val <= kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val <= kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Greater_Equal: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    expr.constant_value = val >= kind.rhs.constant_value.(i64);
                            case f64:    expr.constant_value = val >= kind.rhs.constant_value.(f64);
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .And: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    panic("wat");
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   expr.constant_value = val && kind.rhs.constant_value.(bool);
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Or: {
                    expr.type = type_bool;
                    if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                        switch val in kind.lhs.constant_value {
                            case i64:    panic("wat");
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   expr.constant_value = val || kind.rhs.constant_value.(bool);
                            case TypeID: panic("wat");
                        }
                    }
                }
                case .Not: panic("no unary ops here");
                case .Bit_Not: panic("no unary here");
                case: unimplemented(fmt.tprint(kind.op));
            }

            if kind.lhs.constant_value != nil && kind.rhs.constant_value != nil {
                assert(expr.constant_value != nil);
                expr.mode = .Constant;
            }
            else {
                expr.mode = .RValue;
            }
        }
        case Expr_Address_Of: {
            typecheck_expr(kind.rhs, nil); // todo(josh): should we pass an expected type here?
            assert(kind.rhs.type != nil);
            assert(kind.rhs.mode == .LValue);
            rhs_type := kind.rhs.type;
            expr.type = TYPE(get_or_make_type_ptr_to(rhs_type));
            expr.mode = .RValue;
        }
        case Expr_Dereference: {
            typecheck_expr(kind.lhs, nil); // todo(josh): should we pass an expected type here?
            lhs_type := kind.lhs.type;
            ptr, ok := lhs_type.kind.(Type_Ptr);
            assert(ok);
            assert(ptr.ptr_to != nil);
            expr.type = ptr.ptr_to;
            expr.mode = .LValue;
        }
        case Expr_Cast: {
            // todo(josh): constant values

            typecheck_typespec(kind.typespec);
            assert(kind.typespec.type != nil);
            typecheck_expr(kind.rhs, nil);
            assert(kind.rhs.type != nil);
            if is_pointer_type(kind.typespec.type) && is_pointer_type(kind.rhs.type) {
            }
            else if is_numeric_type(kind.typespec.type) && is_numeric_type(kind.rhs.type) {
            }
            else {
                assert(false, "invalid cast");
            }

            expr.type = kind.typespec.type;
            expr.mode = .RValue;
        }
        case Expr_Unary: {
            typecheck_expr(kind.rhs, nil); // todo(josh): should we pass an expected type here?
            rhs_type := kind.rhs.type;
            assert(rhs_type != nil);
            #partial
            switch kind.op {
                case .Not: { // !
                    assert(rhs_type == type_bool);
                    expr.type = type_bool;
                    if kind.rhs.constant_value != nil {
                        expr.constant_value = !kind.rhs.constant_value.(bool);
                    }
                }
                case .Minus: {
                    expr.type = rhs_type;
                    if kind.rhs.constant_value != nil {
                        #partial
                        switch val in kind.rhs.constant_value {
                            case i64: expr.constant_value = -val;
                            case f64: expr.constant_value = -val;
                        }
                    }
                }
                case .Plus: {
                    expr.type = rhs_type;
                    expr.constant_value = kind.rhs.constant_value;
                }
                case .Bit_Not: {
                    expr.type = rhs_type;
                    if kind.rhs.constant_value != nil {
                        switch val in kind.rhs.constant_value {
                            case i64:    expr.constant_value = ~val;
                            case f64:    panic("wat");
                            case string: panic("wat");
                            case bool:   panic("wat");
                            case TypeID: panic("wat");
                        }
                    }
                }
                case: unimplemented(fmt.tprint(kind.op));
            }

            if kind.rhs.constant_value != nil {
                assert(expr.constant_value != nil);
                expr.mode = .Constant;
            }
            else {
                expr.mode = .RValue;
            }
        }
        case Expr_Number: {
            if expected_type != nil {
                assert(is_numeric_type(expected_type));
                expr.type = expected_type;
                switch {
                    case is_float_type  (expected_type): expr.constant_value = kind.float_value;
                    case is_integer_type(expected_type): expr.constant_value = cast(i64)kind.int_value;
                    case: panic("wat");
                }
            }
            else {
                if kind.has_a_dot {
                    expr.type = type_float;
                    expr.constant_value = kind.float_value;
                }
                else {
                    expr.type = type_int;
                    expr.constant_value = cast(i64)kind.int_value;
                }
            }
            assert(expr.constant_value != nil);
            expr.mode = .Constant;
        }
        case Expr_Size_Of: {
            typecheck_expr(kind.thing_to_get_the_size_of, nil);
            size: int;
            #partial
            switch size_of_kind in kind.thing_to_get_the_size_of.kind {
                case Expr_Typespec: {
                    size = size_of_kind.type.size;
                }
                case Expr_Identifier: {
                    switch decl_kind in size_of_kind.ident.resolved_declaration.kind {
                        case Decl_Type: size = decl_kind.type.size;
                        case Decl_Struct: size = TYPE(decl_kind.structure.type).size;
                        case Decl_Proc: size = type_rawptr.size;
                        case Decl_Var: {
                            if decl_kind.var.is_type_alias_for != nil {
                                size = decl_kind.var.is_type_alias_for.size;
                            }
                            else {
                                size = decl_kind.var.type.size;
                            }
                        }
                        case: panic(tprint(size_of_kind.ident.resolved_declaration));
                    }
                }
                case: {
                    panic(tprint(kind.thing_to_get_the_size_of));
                }
            }

            expr.type = type_int;
            expr.mode = .Constant;
            expr.constant_value = cast(i64)size;
        }
        case Expr_Selector: {
            typecheck_expr(kind.lhs, nil); // todo(josh): should we pass an expected type here?
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
            // todo(josh): constant values

            typecheck_expr(kind.lhs, nil); // todo(josh): should we pass an expected type here?
            typecheck_expr(kind.index, type_int); // todo(josh): should we pass an expected type here?
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
            expr.mode = .Constant;
            expr.constant_value = kind.str;
        }
        case Expr_Call: {
            typecheck_expr(kind.procedure_expr, nil); // todo(josh): should we pass an expected type here?
            assert(kind.procedure_expr.type != nil);
            proc_type, ok := kind.procedure_expr.type.kind.(Type_Proc);
            assert(ok);
            assert(len(proc_type.param_types) == len(kind.params));
            for param, idx in kind.params {
                target_type := proc_type.param_types[idx];
                assert(target_type != nil);

                typecheck_expr(param, target_type);
                assert(param.type != nil);
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
            switch decl in kind.ident.resolved_declaration.kind {
                case Decl_Type:   expr.type = type_typeid; expr.mode = .Constant; expr.constant_value = decl.type.id;
                case Decl_Struct: expr.type = type_typeid; expr.mode = .Constant; expr.constant_value = TYPE(decl.structure.type).id;
                case Decl_Var: {
                    assert(decl.var.type != nil);
                    expr.type = decl.var.type;
                    if decl.var.is_const {
                        assert(decl.var.constant_value != nil);
                        expr.constant_value = decl.var.constant_value;
                        expr.mode = .Constant;
                    }
                    else {
                        expr.mode = .LValue;
                    }
                }
                case Decl_Proc: {
                    assert(decl.procedure.type != nil);
                    expr.type = TYPE(decl.procedure.type);
                    expr.mode = .RValue;
                }
                case: panic(tprint(kind.ident));
            }
            assert(expr.type != nil);
            assert(expr.mode != .Invalid);
        }
        case Expr_Typespec: {
            typecheck_typespec(&kind);
        }
        case Expr_Null: {
            expr.mode = .Constant;
            unimplemented();
        }
        case Expr_True:  expr.type = type_bool; expr.mode = .Constant; expr.constant_value = true;
        case Expr_False: expr.type = type_bool; expr.mode = .Constant; expr.constant_value = false;
        case Expr_Paren: {
            typecheck_expr(kind.expr, expected_type);
            assert(kind.expr != nil);
            expr.type = kind.expr.type;
            expr.mode = kind.expr.mode;
            expr.constant_value = kind.expr.constant_value;
        }
        case: panic(tprint(expr));
    }

    if expected_type != nil && expr.type != nil && expected_type != expr.type {
        fmt.println("-------------------------------");
        fmt.println(expr.kind);
        fmt.println(expr.type);
        fmt.println(expected_type);
        panic("expr.type didn't match expected_type:");
    }
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



TYPE_MAGIC :: 789162976;
Type :: struct {
    kind: union {
        Type_Primitive,
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
}

Type_Primitive :: struct {

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