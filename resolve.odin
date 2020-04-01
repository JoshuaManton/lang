package main

import "core:fmt"

unresolved_identifiers: [dynamic]^Ast_Identifier;

queue_identifier_for_resolving :: proc(ident: ^Ast_Identifier) {
	append(&unresolved_identifiers, ident);
}

register_declaration :: proc(scope: ^Ast_Scope, name: string, decl: Declaration_Kind) {
	// todo(josh): check for shadowing
	append(&scope.declarations, new_clone(Declaration{name, decl}));
}

resolve_identifiers :: proc() {
	ident_loop:
	for ident in unresolved_identifiers {
		base := cast(^Ast_Node)ident;
		current := base.enclosing_scope;
		for current != nil {
			defer current = current.parent;
			for decl in current.declarations {
				if decl.name == ident.name {
					ident.resolved_declaration = decl;
					continue ident_loop;
				}
			}
		}

		panic(fmt.tprint("Unresolved identifier:", ident));
	}
}