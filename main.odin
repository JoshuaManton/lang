package main

import "core:fmt"
import "core:strconv"
import "core:strings"
import "core:os"

import "shared:wb/logging"

main :: proc() {
    if len(os.args) < 2 {
        fmt.println("Usage:\n  lang <filename>");
        return;
    }

    init_parser();
    init_types();

    fmt.println("Parsing...");
    root_file := parse_file(os.args[1]);
    fmt.println("Resolving identifiers...");
    resolve_identifiers();
    fmt.println("Checking types...");
    begin_typechecking();
    fmt.println("Generating IR...");
    ir := generate_ir();
    fmt.println("Translating IR to bytecode...");
    vm := translate_ir_to_vm(ir);
    fmt.println("Executing bytecode...");
    execute_vm(vm);

    fmt.println("Outputting AST...");
    output_graphviz(NODE(root_file));
}

output_graphviz :: proc(node: ^Ast_Node) {
    labels: strings.Builder;
    cx: strings.Builder;
    gv_node(node, &labels, &cx);

    sb: strings.Builder;
    sbwrite(&sb, "digraph g {\n");
    sbwrite(&sb, strings.to_string(labels));
    sbwrite(&sb, strings.to_string(cx));
    sbwrite(&sb, "}");
    os.write_entire_file("ast.dot", transmute([]byte)strings.to_string(sb));
}

gv_node :: proc(node: ^Ast_Node, labels, cx: ^strings.Builder) {
    sbwrite(labels, "    ", gv_name(node), "\n");
    // logln("---------------------------------------");
    // logln(node.kind);
    switch kind in node.kind {
        case Ast_File: {
            gv_edge(node, NODE(kind.scope), labels, cx);
        }
        case Ast_Scope: {
            for other in kind.nodes {
                gv_edge(node, other, labels, cx);
            }
        }
        case Ast_Var: {
            if kind.typespec != nil do gv_edge(node, NODE(kind.typespec), labels, cx);
            if kind.expr     != nil do gv_edge(node, NODE(kind.expr),     labels, cx);
        }
        case Ast_Assign: {
            gv_edge(node, NODE(kind.lhs), labels, cx);
            gv_edge(node, NODE(kind.rhs), labels, cx);
        }
        case Ast_Proc: {
            for param in kind.header.params {
                gv_edge(node, NODE(param), labels, cx);
            }
            if kind.header.return_typespec != nil {
                gv_edge(node, NODE(kind.header.return_typespec), labels, cx);
            }
            if !kind.is_foreign {
                assert(kind.block != nil);
                gv_edge(node, NODE(kind.block), labels, cx);
            }
            else {
                assert(kind.block == nil);
            }
        }
        case Ast_Proc_Header: {

        }
        case Ast_Struct: {
            for field in kind.fields {
                gv_edge(node, NODE(field), labels, cx);
            }
        }
        case Ast_Identifier: {

        }
        case Ast_Include: {
            gv_edge(node, NODE(kind.file), labels, cx);
        }
        case Ast_If: {
            gv_edge(node, NODE(kind.condition), labels, cx);
            gv_edge(node, NODE(kind.body), labels, cx);
            if kind.else_stmt != nil {
                gv_edge(node, NODE(kind.else_stmt), labels, cx);
            }
        }
        case Ast_While: {
            gv_edge(node, NODE(kind.condition), labels, cx);
            gv_edge(node, NODE(kind.body), labels, cx);
        }
        case Ast_For: {
            gv_edge(node, NODE(kind.pre_statement), labels, cx);
            gv_edge(node, NODE(kind.condition), labels, cx);
            gv_edge(node, NODE(kind.post_statement), labels, cx);
            gv_edge(node, NODE(kind.body), labels, cx);
        }
        case Ast_Expr_Statement: {
            gv_edge(node, NODE(kind.expr), labels, cx);
        }
        case Ast_Return: {
            if kind.expr != nil {
                gv_edge(node, NODE(kind.expr), labels, cx);
            }
        }
        case Ast_Defer: {
            gv_edge(node, NODE(kind.stmt), labels, cx);
        }
        case Ast_Continue: {

        }
        case Ast_Break: {

        }
        case Ast_Expr: {
            switch expr in kind.kind {
                case Expr_Binary: {
                    gv_edge(node, NODE(expr.lhs), labels, cx);
                    gv_edge(node, NODE(expr.rhs), labels, cx);
                }
                case Expr_Unary: {
                    gv_edge(node, NODE(expr.rhs), labels, cx);
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
                    gv_edge(node, NODE(expr.expr), labels, cx);
                }
                case Expr_Selector: {
                    gv_edge(node, NODE(expr.lhs), labels, cx);
                    gv_edge(node, NODE(expr.ident), labels, cx);
                }
                case Expr_Subscript: {
                    gv_edge(node, NODE(expr.lhs), labels, cx);
                    gv_edge(node, NODE(expr.index), labels, cx);
                }
                case Expr_Call: {
                    gv_edge(node, NODE(expr.procedure_expr), labels, cx);
                    for param in expr.params {
                        gv_edge(node, NODE(param), labels, cx);
                    }
                }
                case Expr_Cast: {
                    gv_edge(node, NODE(expr.typespec), labels, cx);
                    gv_edge(node, NODE(expr.rhs), labels, cx);
                }
                case Expr_True: {

                }
                case Expr_False: {

                }
                case Expr_Size_Of: {
                    gv_edge(node, NODE(expr.thing_to_get_the_size_of), labels, cx);
                }
                case Expr_Type_Of: {
                    gv_edge(node, NODE(expr.thing_to_get_the_type_of), labels, cx);
                }
                case Expr_Address_Of: {
                    gv_edge(node, NODE(expr.rhs), labels, cx);
                }
                case Expr_Dereference: {
                    gv_edge(node, NODE(expr.lhs), labels, cx);
                }
                case Expr_Typespec: {
                    switch type in expr.kind {
                        case Typespec_Identifier:
                        case Typespec_Ptr:        gv_edge(node, NODE(type.ptr_to), labels, cx);
                        case Typespec_Slice:      gv_edge(node, NODE(type.slice_of), labels, cx);
                        case Typespec_Array:      gv_edge(node, NODE(type.array_of), labels, cx);
                    }
                }
            }
        }
    }
}

gv_edge :: proc(lhs, rhs: ^Ast_Node, labels, cx: ^strings.Builder) {
    sbwrite(cx, "    ", lhs.s, " -> ", rhs.s, "\n");
    gv_node(rhs, labels, cx);
}

gv_name :: proc(node: ^Ast_Node) -> string {
    name: strings.Builder;
    sbwrite(&name, node.s, " [label=\"");
    gv_name_without_quotes(node, &name);

    gv_name_without_quotes :: proc(node: ^Ast_Node, sb: ^strings.Builder) {
        switch kind in &node.kind {
            case Ast_File:           sbwrite(sb, "file ", kind.name);
            case Ast_Scope:          sbwrite(sb, "scope");
            case Ast_Var:            sbwrite(sb, "var ", kind.name);
            case Ast_Identifier:     sbwrite(sb, kind.name);
            case Ast_Proc:           sbwrite(sb, "proc ", kind.header.name);
            case Ast_Proc_Header:
            case Ast_Struct:         sbwrite(sb, "struct ", kind.name);
            case Ast_Assign: {
                #partial
                switch kind.op {
                    case .Assign:          sbwrite(sb, "=");
                    case .Plus_Assign:     sbwrite(sb, "+=");
                    case .Minus_Assign:    sbwrite(sb, "-=");
                    case .Multiply_Assign: sbwrite(sb, "*=");
                    case .Divide_Assign:   sbwrite(sb, "/=");
                    case: panic(twrite(kind.op));
                }
            }
            case Ast_Include:        sbwrite(sb, "include ", kind.file.name);
            case Ast_If:             sbwrite(sb, "if");
            case Ast_While:          sbwrite(sb, "while");
            case Ast_For:            sbwrite(sb, "for");
            case Ast_Expr_Statement: sbwrite(sb, "expr statement");
            case Ast_Return:         sbwrite(sb, "return");
            case Ast_Defer:          sbwrite(sb, "defer");
            case Ast_Continue:       sbwrite(sb, "continue");
            case Ast_Break:          sbwrite(sb, "break");
            case Ast_Expr: {
                switch expr in &kind.kind {
                    case Expr_Number: {
                        switch {
                            case is_float_type(kind.checked.type):   sbwrite(sb, "number ", expr.float_value);
                            case is_integer_type(kind.checked.type): sbwrite(sb, "number ", expr.int_value);
                            case: panic(twrite(kind.checked.type.kind));
                        }
                    }
                    case Expr_Identifier:  sbwrite(sb, expr.ident.name);
                    case Expr_Binary:      sbwrite(sb, operator_strings[expr.op]);
                    case Expr_Unary:       sbwrite(sb, operator_strings[expr.op]);
                    case Expr_String:      sbwrite(sb, "string ", expr.str);
                    case Expr_Null:        sbwrite(sb, "null");
                    case Expr_Paren:       sbwrite(sb, "paren");
                    case Expr_Selector:    sbwrite(sb, "selector");
                    case Expr_Subscript:   sbwrite(sb, "subscript");
                    case Expr_Call:        sbwrite(sb, "call");
                    case Expr_Cast:        sbwrite(sb, "cast");
                    case Expr_True:        sbwrite(sb, "true");
                    case Expr_False:       sbwrite(sb, "false");
                    case Expr_Size_Of:     sbwrite(sb, "sizeof");
                    case Expr_Type_Of:     sbwrite(sb, "typeof");
                    case Expr_Address_Of:  sbwrite(sb, "address of");
                    case Expr_Dereference: sbwrite(sb, "dereference");
                    case Expr_Typespec: {
                        current := &expr;
                        type_loop: for {
                            switch type in current.kind {
                                case Typespec_Identifier: sbwrite(sb, type.ident.name); break type_loop;
                                case Typespec_Ptr:        sbwrite(sb, "^"); current = type.ptr_to;
                                case Typespec_Slice:      sbwrite(sb, "[]"); current = type.slice_of;
                                case Typespec_Array:      sbwrite(sb, "[", type.length.checked.constant_value.(i64), "]"); current = type.array_of;
                            }
                        }
                    }
                }
            }
        }
    }

    sbwrite(&name, "\"]");
    return strings.to_string(name);
}

logln :: logging.logln;
logf :: logging.logf;
pretty_print :: logging.pretty_print;

println :: fmt.println;

Maybe :: union(T: typeid) {
    T,
}

getval :: inline proc(m: ^Maybe($T)) -> (^T, bool) {
    if _, ok := m.(T); !ok do return nil, false;
    return &m.(T), true;
}

twrite :: inline proc(args: ..any) -> string {
    return fmt.tprint(args=args, sep="");
}

sbwrite :: inline proc(buf: ^strings.Builder, args: ..any) -> string {
    return fmt.sbprint(buf=buf, args=args, sep="");
}

awrite :: inline proc(args: ..any) -> string {
    return fmt.aprint(args=args, sep="");
}