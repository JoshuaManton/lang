package main

import "core:fmt"

unresolved_identifiers: [dynamic]^Ast_Identifier;

queue_identifier_for_resolving :: proc(ident: ^Ast_Identifier) {
    append(&unresolved_identifiers, ident);
}

register_declaration :: proc(scope: ^Ast_Scope, name: string, deck_kind: Declaration_Kind) -> ^Declaration {
    // todo(josh): check for shadowing and collisions!!!!
    decl := new_clone(Declaration{name, deck_kind});
    if _, ok := decl.kind.(Decl_Struct); ok {
        structure := &decl.kind.(Decl_Struct);
        structure.structure.type = make_incomplete_type(cast(^Ast_Node)structure.structure);
    }
    append(&scope.declarations, decl);
    return decl;
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

        panic(twrite("Unresolved identifier:", ident));
    }
}