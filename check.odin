package main

import "core:fmt"

type_int: ^Type;
type_bool: ^Type;
type_float: ^Type;

all_types: [dynamic]^Type;

init_types :: proc() {
	assert(current_scope != nil);
	assert(global_scope == current_scope);

	type_int = TYPE(make_type(Type_Primitive{}, 8));
	register_declaration(global_scope, "int", Decl_Type{type_int});

	type_float = TYPE(make_type(Type_Primitive{}, 4));
	register_declaration(global_scope, "float", Decl_Type{type_float});

	type_bool = TYPE(make_type(Type_Primitive{}, 1));
	register_declaration(global_scope, "bool", Decl_Type{type_bool});
}

typecheck_node :: proc(node: ^Ast_Node) {
	switch kind in &node.kind {
		case Ast_File:       typecheck_file(kind);
		case Ast_Scope:      typecheck_scope(kind);
		case Ast_Identifier: typecheck_identifier(kind); assert(kind.type != nil);
		case Ast_Var:        typecheck_var(kind);        assert(kind.type != nil);
		case Ast_Proc:       typecheck_proc(kind);       assert(kind.type != nil);
		case Ast_Struct:     typecheck_struct(kind);     assert(kind.type != nil);
		case Ast_Expr:       typecheck_expr(kind);       assert(kind.type != nil);
		case Ast_Typespec:   typecheck_typespec(kind);   assert(kind.type != nil);
		case Ast_Assign: {
			assert(kind.op == .Assign); // todo(josh): handle +=, -=, <<=, etc
			typecheck_expr(kind.lhs); assert(kind.lhs.type != nil);
			typecheck_expr(kind.rhs); assert(kind.rhs.type != nil);
			assert(kind.lhs.type == kind.rhs.type);
		}
	}
}

typecheck_file :: proc(file: ^Ast_File) {
	typecheck_scope(file.block);
}

typecheck_scope :: proc(scope: ^Ast_Scope) {
	for node in scope.nodes {
		typecheck_node(node);
	}
}

typecheck_identifier :: proc(ident: ^Ast_Identifier) {
	switch decl in ident.resolved_declaration.kind {
		case Decl_Type:   ident.type = decl.type;
		case Decl_Struct: ident.type = TYPE(decl.structure.type);
		case Decl_Proc:   ident.type = TYPE(decl.procedure.type);
		case Decl_Var:    ident.type = decl.var.type;
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
				case: {
					panic(fmt.tprint(decl, "used as a type when it is not a type"));
				}
			}
		}
		case Typespec_Ptr: {
			typecheck_typespec(kind.ptr_to);
			assert(kind.ptr_to.type != nil);
			typespec.type = TYPE(make_or_get_type_ptr_to(kind.ptr_to.type));
		}
		case Typespec_Slice: {
			typecheck_typespec(kind.slice_of);
			assert(kind.slice_of.type != nil);
			typespec.type = TYPE(make_or_get_type_slice_of(kind.slice_of.type));
		}
		case Typespec_Array: {
			unimplemented();
			// return make_or_get_type_array_of(kind.ptr_to, ?); // todo(josh) array lengths
		}
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

	typecheck_scope(procedure.block);
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

typecheck_expr :: proc(expr: ^Ast_Expr) {
	switch kind in expr.kind {
		case Expr_Binary: {
			typecheck_expr(kind.lhs);
			typecheck_expr(kind.rhs);
			lhs_type := kind.lhs.type;
			rhs_type := kind.rhs.type;
			assert(lhs_type != nil);
			assert(lhs_type == rhs_type);
			#partial
			switch kind.op {
			    case .Multiply:      expr.type = lhs_type;
			    case .Divide:        expr.type = lhs_type;
			    case .Mod:           expr.type = lhs_type; // todo(josh): make sure left and right are both integers
			    case .Mod_Mod:       expr.type = lhs_type; // todo(josh): make sure left and right are both integers
			    case .Ampersand:     expr.type = lhs_type; // todo(josh): make sure left and right are both integers
			    case .Shift_Left:    expr.type = lhs_type; // todo(josh): make sure left and right are both integers
			    case .Shift_Right:   expr.type = lhs_type; // todo(josh): make sure left and right are both integers

			    case .Plus:          expr.type = lhs_type;
			    case .Minus:         expr.type = lhs_type;
			    case .Bit_Xor:       expr.type = lhs_type; // todo(josh): make sure left and right are both integers
			    case .Bit_Or:        expr.type = lhs_type; // todo(josh): make sure left and right are both integers

			    case .Equal_To:      expr.type = type_bool;
			    case .Not_Equal:     expr.type = type_bool;
			    case .Less:          expr.type = type_bool;
			    case .Greater:       expr.type = type_bool;
			    case .Less_Equal:    expr.type = type_bool;
			    case .Greater_Equal: expr.type = type_bool;
			    case .And:           expr.type = type_bool;
			    case .Or:            expr.type = type_bool;
			    case: {
			    	unimplemented(fmt.tprint(kind.op));
			    }
			}
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
				case .Ampersand: expr.type = TYPE(make_or_get_type_ptr_to(rhs_type));
				case: {
					unimplemented(fmt.tprint(kind.op));
				}
			}
		}
		case Expr_Number: {
			// todo(josh): support more than just ints
			expr.type = type_int;
		}
		case Expr_String: {
			unimplemented();
		}
		case Expr_Identifier: {
			typecheck_identifier(kind.ident);
			assert(kind.ident.type != nil);
			expr.type = kind.ident.type;
		}
		case Expr_Null: {
			unimplemented();
		}
		case Expr_Paren: {
			typecheck_expr(kind.expr);
			assert(kind.expr != nil);
			expr.type = kind.expr.type;
		}
	}
	assert(expr.type != nil);
}

get_type_through_declaration :: proc(decl: ^Declaration) -> ^Type {
	switch decl in decl.kind {
		case Decl_Type:   return decl.type;
		case Decl_Var:    return decl.var.type;
		case Decl_Proc:   return TYPE(decl.procedure.type);
		case Decl_Struct: return TYPE(decl.structure.type);
	}
	unreachable();
	return {};
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

make_or_get_type_ptr_to :: proc(type: ^Type) -> ^Type_Ptr {
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

make_or_get_type_slice_of :: proc(type: ^Type) -> ^Type_Slice {
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

make_type :: proc(kind: $T, size: int) -> ^T {
	t := new(Type);
	t.kind = kind;
	t.size = size;
	t.magic = TYPE_MAGIC;
	append(&all_types, t);
	return cast(^T)t;
}

TYPE :: proc(k: ^$T) -> ^Type {
	t := cast(^Type)k;
	assert(t.magic == TYPE_MAGIC);
	return t;
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