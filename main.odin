package main

import "core:fmt"
import "core:strconv"
import "core:os"

import "shared:wb/logging"

main :: proc() {
    if len(os.args) < 2 {
        fmt.println("Usage:\n  lang <filename>");
        return;
    }

    init_parser();
    init_types();

    file_data, ok := os.read_entire_file(os.args[1]);
    defer delete(file_data);
    assert(ok);
    lexer := make_lexer(transmute(string)file_data);
    fmt.println("Parsing...");
    file := parse_file(&lexer, os.args[1]);
    fmt.println("Resolving identifiers...");
    resolve_identifiers();
    fmt.println("Checking types...");
    typecheck_node(NODE(global_scope));
    fmt.println("Generating IR...");
    ir := generate_ir();
    vm := translate_ir_to_vm(ir);
    execute_vm(vm);

    // fmt.println("Outputting AST...");
    // output_graphviz(NODE(file));
}

/*
output_graphviz :: proc(node: ^Ast_Node) {
    sb: strings.Builder;
    fmt.sbprint(&sb, "digraph g {\n");
    gv_node(node, &sb);
    fmt.sbprint(&sb, "}");
    os.write_entire_file("ast.dot", transmute([]byte)strings.to_string(sb));
}

gv_node :: proc(node: ^Ast_Node, sb: ^strings.Builder) {
    switch kind in node.kind {
        case Ast_File: {
            gv_edge(node, NODE(kind.block), sb);
        }
        case Ast_Scope: {
            for other in kind.nodes {
                gv_edge(node, other, sb);
            }
        }
        case Ast_Var: {
            // if kind.typespec != nil do gv_edge(node, NODE(kind.typespec), sb);
            if kind.expr     != nil do gv_edge(node, NODE(kind.expr),     sb);
        }
        case Ast_Assign: {
            gv_edge(node, NODE(kind.lhs), sb);
            gv_edge(node, NODE(kind.rhs), sb);
        }
        case Ast_Proc: {
            for param in kind.params {
                gv_edge(node, NODE(param), sb);
            }
            gv_edge(node, NODE(kind.block), sb);
        }
        case Ast_Struct: {
            gv_edge(node, NODE(kind.block), sb);
        }
        case Ast_Expr: {
            switch expr in kind.kind {
                case Expr_Binary: {
                    gv_edge(node, NODE(expr.lhs), sb);
                    gv_edge(node, NODE(expr.rhs), sb);
                }
                case Expr_Unary: {
                    gv_edge(node, NODE(expr.rhs), sb);
                }
                case Expr_Number: {

                }
                case Expr_String: {

                }
                case Expr_Identifier: {

                }
                case Expr_Null: {

                }
                case Expr_Paren: {
                    gv_edge(node, NODE(expr.expr), sb);
                }
            }
        }
        case Ast_Typespec: {

        }
        case Ast_Identifier: {

        }
    }
}

gv_edge :: proc(lhs, rhs: ^Ast_Node, sb: ^strings.Builder) {
    fmt.sbprint(sb, "    ", gv_name(lhs), " -> ", gv_name(rhs), "\n");
    gv_node(rhs, sb);
}

gv_name :: proc(node: ^Ast_Node) -> string {
    name: strings.Builder;
    fmt.sbprint(&name, "\"", node.s, " ");

    gv_name_without_quotes(node, &name);

    gv_name_without_quotes :: proc(node: ^Ast_Node, sb: ^strings.Builder) {
        switch kind in &node.kind {
            case Ast_File:  fmt.sbprint(sb, kind.name);
            case Ast_Scope: fmt.sbprint(sb, "scope");
            case Ast_Var: {
                fmt.sbprint(sb, "var ", kind.name);
                if kind.typespec != nil {
                    fmt.sbprint(sb, ": ");
                    gv_name_without_quotes(NODE(kind.typespec), sb);
                }
            }
            case Ast_Identifier: fmt.sbprint(sb, kind.name);
            case Ast_Proc:       fmt.sbprint(sb, "proc ", kind.name);
            case Ast_Struct:     fmt.sbprint(sb, "struct ", kind.name);
            case Ast_Assign:     fmt.sbprint(sb, kind.op);
            case Ast_Expr: {
                switch expr in kind.kind {
                    case Expr_Binary:     fmt.sbprint(sb, expr.op);
                    case Expr_Unary:      fmt.sbprint(sb, expr.op);
                    case Expr_Number:     fmt.sbprint(sb, expr.int_value);
                    case Expr_String:     fmt.sbprint(sb, expr.str);
                    case Expr_Identifier: fmt.sbprint(sb, expr.ident.name);
                    case Expr_Null:       fmt.sbprint(sb, "null");
                    case Expr_Paren:      fmt.sbprint(sb, "paren");
                }
            }
            case Ast_Typespec: {
                current := kind;
                type_loop: for {
                    switch type in current.kind {
                        case Typespec_Identifier: fmt.sbprint(sb, type.ident.name); break type_loop;
                        case Typespec_Ptr:        fmt.sbprint(sb, "^"); current = type.ptr_to;
                        case Typespec_Slice:      fmt.sbprint(sb, "[]"); current = type.slice_of;
                        case Typespec_Array:      fmt.sbprint(sb, "[?]"); current = type.array_of; // todo(josh): array length
                    }
                }
            }
        }
    }

    fmt.sbprint(&name, '"');
    return strings.to_string(name);
}
*/

logln :: logging.logln;
logf :: logging.logf;

println :: fmt.println;
tprint :: fmt.tprint;

Maybe :: union(T: typeid) {
    T,
}

getval :: inline proc(m: ^Maybe($T)) -> (^T, bool) {
    if _, ok := m.(T); !ok do return nil, false;
    return &m.(T), true;
}