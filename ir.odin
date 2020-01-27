package main

import "core:fmt"

IR_Result :: struct {
	procedures: [dynamic]^IR_Proc,
	global_storage_size: int,
}

IR_Proc :: struct {
	stack_frame_size: int,
	statements: [dynamic]^IR_Statement,
	num_temporaries: int,
}

IR_Storage :: union {
	Stack_Frame_Storage,
	Global_Storage,
}
Stack_Frame_Storage :: struct {
	offset: int,
}
Global_Storage :: struct {
	offset: int,
}

IR_Statement :: struct {
	kind: union {
		IR_Load,
		IR_Store,
		IR_Binop,
		IR_Unary,
		IR_Load_Immediate,
	},
}
IR_Binop :: struct {
	op: Token_Kind,
	dst: ^Temporary,
	lhs, rhs: ^Temporary,
}
IR_Unary :: struct {
	op: Token_Kind,
	dst: ^Temporary,
	rhs: ^Temporary,
}
IR_Load :: struct {
	storage: IR_Storage,
	dst: ^Temporary,
}
IR_Load_Immediate :: struct {
	dst: ^Temporary,
	imm: int,
}
IR_Store :: struct {
	storage: IR_Storage,
	value: ^Temporary,
}

Temporary :: struct {
	register: int,
}

gen_ir :: proc() -> IR_Result {
	ir: IR_Result;
	for file_node in global_scope.nodes {
		file, ok := file_node.kind.(Ast_File);
		assert(ok);
		for node in file.block.nodes {
			#partial
			switch kind in &node.kind {
				case Ast_Var: {
					assert(kind.type.size > 0);
					kind.storage = Global_Storage{ir.global_storage_size};
					ir.global_storage_size += kind.type.size;
				}
				case Ast_Proc: {
					ir_proc := gen_ir_proc(kind);
					append(&ir.procedures, ir_proc);
				}
				case: unimplemented(fmt.tprint(kind));
			}
		}
	}
	return ir;
}

gen_ir_proc :: proc(procedure: ^Ast_Proc) -> ^IR_Proc {
	ir_proc := new(IR_Proc);
	assert(len(procedure.variables) >= len(procedure.params), "Procedure parameters should be included in the procedure.variables list");
	for var in procedure.variables {
		assert(var.type.size > 0);
		var.storage = Stack_Frame_Storage{ir_proc.stack_frame_size};
		ir_proc.stack_frame_size += var.type.size;
	}

	for node in procedure.block.nodes {
		fmt.println("-----------------------------------------");
		#partial
		switch kind in node.kind {
			case Ast_Var: {
				if kind.expr != nil {
					result := gen_ir_expr(ir_proc, kind.expr);
					assert(kind.storage != nil);
					ir_store(ir_proc, kind.storage, result);
				}
			}
			case Ast_Assign: {
				storage: IR_Storage;
				#partial
				switch kind in kind.lhs.kind {
					case Expr_Identifier: {
						#partial
						switch decl in kind.ident.resolved_declaration.kind {
							case Decl_Var: {
								assert(decl.var.storage != nil);
								storage = decl.var.storage;
							}
							case: {
								unimplemented(fmt.tprint(decl));
							}
						}
					}
					case: {
						unimplemented(fmt.tprint(kind));
					}
				}
				assert(storage != nil);
				rhs := gen_ir_expr(ir_proc, kind.rhs);
				ir_store(ir_proc, storage, rhs);
			}
			case: {
				unimplemented(fmt.tprint(kind));
			}
		}
	}

	return ir_proc;
}

gen_ir_expr :: proc(procedure: ^IR_Proc, expr: ^Ast_Expr) -> ^Temporary {
	result: ^Temporary;
	switch kind in expr.kind {
		case Expr_Binary: {
			lhs := gen_ir_expr(procedure, kind.lhs);
			rhs := gen_ir_expr(procedure, kind.rhs);
			result = ir_binop(procedure, kind.op, lhs, rhs);
		}
		case Expr_Unary: {
			rhs := gen_ir_expr(procedure, kind.rhs);
			result = ir_unary(procedure, kind.op, rhs);
		}
		case Expr_Number: {
			result = ir_load_immediate(procedure, kind.int_value);
		}
		case Expr_String: {
			unimplemented();
		}
		case Expr_Identifier: {
			#partial
			switch decl in kind.ident.resolved_declaration.kind {
				case Decl_Var: {
					assert(decl.var.storage != nil); // todo(josh): handle global vars
					result = ir_load(procedure, decl.var.storage); // todo(josh): make sure we handle nested procs properly and don't touch varables in a parent procedure
				}
				case: {
					unimplemented(fmt.tprint(decl));
				}
			}
		}
		case Expr_Null: {
			result = ir_load_immediate(procedure, 0);
		}
		case Expr_Paren: {
			result = gen_ir_expr(procedure, kind.expr);
		}
		case: {
			unimplemented(fmt.tprint(kind));
		}
	}
	assert(result != nil);
	return result;
}

ir_binop :: proc(procedure: ^IR_Proc, op: Token_Kind, lhs: ^Temporary, rhs: ^Temporary) -> ^Temporary { // todo(josh): make a separate Operator enum so we don't have to use Token_Kind
	dst := make_temporary(procedure);
	ir_statement(procedure, IR_Binop{op, dst, lhs, rhs});
	return dst;
}

ir_unary :: proc(procedure: ^IR_Proc, op: Token_Kind, rhs: ^Temporary) -> ^Temporary {
	dst := make_temporary(procedure);
	ir_statement(procedure, IR_Unary{op, dst, rhs});
	return dst;
}

ir_load :: proc(procedure: ^IR_Proc, storage: IR_Storage) -> ^Temporary {
	dst := make_temporary(procedure);
	ir_statement(procedure, IR_Load{storage, dst});
	return dst;
}
ir_load_immediate :: proc(procedure: ^IR_Proc, imm: int) -> ^Temporary {
	dst := make_temporary(procedure);
	ir_statement(procedure, IR_Load_Immediate{dst, imm});
	return dst;
}

ir_store :: proc(procedure: ^IR_Proc, storage: IR_Storage, value: ^Temporary) {
	ir_statement(procedure, IR_Store{storage, value});
}

ir_statement :: proc(procedure: ^IR_Proc, kind: $T) {
	stmt := new_clone(IR_Statement{kind});
	fmt.println(stmt.kind);
	append(&procedure.statements, stmt); // todo(josh): do statements have to be allocated? I would suspect not
}

make_temporary :: proc(procedure: ^IR_Proc) -> ^Temporary {
	t := new(Temporary);
	t.register = procedure.num_temporaries;
	procedure.num_temporaries += 1;
	return t;
}