package main

import "core:fmt"
import "core:strconv"

current_scope: ^Ast_Scope;
global_scope: ^Ast_Scope;
current_procedure: ^Ast_Proc;

init_parser :: proc() {
    global_scope = make_node(Ast_Scope);
    assert(current_scope == nil);
    current_scope = global_scope;
}

parse_file :: proc(lexer: ^Lexer, filename: string) -> ^Ast_File {
    assert(global_scope != nil);
    scope := parse_scope(lexer);
    file := make_node(Ast_File);
    file.name = filename;
    file.block = scope;
    append(&global_scope.nodes, NODE(file));
    return file;
}

parse_scope :: proc(lexer: ^Lexer) -> ^Ast_Scope {
    scope := make_node(Ast_Scope);
    scope.parent = current_scope;
    old_scope := current_scope;
    current_scope = scope;
    defer current_scope = old_scope;

    nodes: [dynamic]^Ast_Node;
    node_loop: for {
        token, ok := peek(lexer);
        if !ok do break;

        node: ^Ast_Node;
        #partial
        switch token.kind {
            case .Var:    node = NODE(parse_var(lexer, true));
            case .Proc:   node = NODE(parse_proc(lexer));
            case .Struct: node = NODE(parse_struct(lexer));
            case .Line_Comment: {
                get_next_token(lexer);
                continue node_loop;
            }
            case .RCurly: break node_loop;
            case: {
                expr := parse_expr(lexer);
                token, ok := peek(lexer);
                assert(ok);
                #partial
                switch token.kind {
                    case .Assign: {
                        get_next_token(lexer);
                        lhs := expr;
                        rhs := parse_expr(lexer);
                        assign := make_node(Ast_Assign);
                        assign^ = Ast_Assign{token.kind, lhs, rhs};
                        expr = cast(^Ast_Expr)assign;
                    }
                    case: {
                        unimplemented(fmt.tprint(token.kind));
                    }
                }
                expect(lexer, .Semicolon);
                node = NODE(expr);
            }
        }
        assert(node != nil);
        append(&nodes, node);
    }
    scope.nodes = nodes;
    return scope;
}

parse_var :: proc(lexer: ^Lexer, require_semicolon: bool) -> ^Ast_Var {
    expect(lexer, .Var);
    name_token := expect(lexer, .Identifier);
    expect(lexer, .Colon);

    typespec := parse_typespec(lexer);

    expr: ^Ast_Expr;
    {
        assign, ok := peek(lexer);
        assert(ok);
        if assign.kind == .Assign {
            get_next_token(lexer);
            expr = parse_expr(lexer);
        }
    }

    if require_semicolon {
        expect(lexer, .Semicolon);
    }

    var := make_node(Ast_Var);
    var.name = name_token.slice;
    var.typespec = typespec;
    var.expr = expr;

    if current_procedure != nil {
        append(&current_procedure.variables, var);
    }

    register_declaration(current_scope, var.name, Decl_Var{var});
    return var;
}

parse_typespec :: proc(lexer: ^Lexer) -> ^Ast_Typespec {
    token, _, ok := get_next_token(lexer);
    assert(ok);
    typespec := make_node(Ast_Typespec);
    #partial
    switch token.kind {
        case .Identifier: {
            ident := make_node(Ast_Identifier);
            ident.name = token.slice;
            typespec.kind = Typespec_Identifier{ident};
            queue_identifier_for_resolving(ident);
        }
        case .Caret: typespec.kind = Typespec_Ptr{parse_typespec(lexer)};
        case .LSquare: {
            next, ok := peek(lexer);
            assert(ok);
            #partial
            switch next.kind {
                case .RSquare: {
                    get_next_token(lexer);
                    typespec.kind = Typespec_Slice{parse_typespec(lexer)};
                }
                case: {
                    length := parse_expr(lexer);
                    expect(lexer, .RSquare);
                    typespec.kind = Typespec_Array{parse_typespec(lexer)};
                }
            }
        }
        case: unimplemented(fmt.tprint(token.kind));
    }
    assert(typespec.kind != nil);
    return typespec;
}

parse_proc :: proc(lexer: ^Lexer) -> ^Ast_Proc {
    procedure := make_node(Ast_Proc);

    old_proc := current_procedure;
    current_procedure = procedure;
    defer current_procedure = old_proc;

    expect(lexer, .Proc);
    name_token := expect(lexer, .Identifier);
    expect(lexer, .LParen);

    params: [dynamic]^Ast_Var;
    for {
        if t, ok := peek(lexer); ok {
            if t.kind == .RParen {
                get_next_token(lexer);
                break;
            }
        }
        else {
            assert(false, "End of text from within procedure param list");
        }

        param := parse_var(lexer, false);
        append(&params, param);
    }

    return_typespec: ^Ast_Typespec;
    {
        token, ok := peek(lexer);
        assert(ok);
        if token.kind != .LCurly {
            return_typespec = parse_typespec(lexer);
        }
    }

    body := parse_body(lexer);

    procedure.name = name_token.slice;
    procedure.params = params[:];
    procedure.block = body;

    register_declaration(current_scope, procedure.name, Decl_Proc{procedure});

    return procedure;
}

parse_body :: proc(lexer: ^Lexer) -> ^Ast_Scope {
    expect(lexer, .LCurly);
    block := parse_scope(lexer);
    expect(lexer, .RCurly);
    return block;
}

parse_struct :: proc(lexer: ^Lexer) -> ^Ast_Struct {
    structure := make_node(Ast_Struct);

    expect(lexer, .Struct);
    name_token := expect(lexer, .Identifier);
    block := parse_body(lexer);
    for node in block.nodes {
        if _, ok := node.kind.(Ast_Var); !ok {
            assert(false, "Only vars are allowed in struct bodies");
        }
        var := &node.kind.(Ast_Var);
        assert(var != nil);
        append(&structure.fields, var);
    }

    structure.name = name_token.slice;
    structure.block = block;

    register_declaration(current_scope, structure.name, Decl_Struct{structure});

    return structure;
}

parse_expr :: inline proc(lexer: ^Lexer, loc := #caller_location) -> ^Ast_Expr {
    return parse_or_expr(lexer);
}

parse_or_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);
    expr := parse_and_expr(lexer);
    for is_or_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);
        assert(op.kind == .Or);
        lhs := expr;
        rhs := parse_and_expr(lexer);
        expr = make_node(Ast_Expr);
        expr.kind = Expr_Binary{op.kind, lhs, rhs};
    }
    return expr;
}

parse_and_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);
    expr := parse_cmp_expr(lexer);
    for is_and_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);
        assert(op.kind == .And);
        lhs := expr;
        rhs := parse_cmp_expr(lexer);
        expr = make_node(Ast_Expr);
        expr.kind = Expr_Binary{op.kind, lhs, rhs};
    }
    return expr;
}

parse_cmp_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);
    expr := parse_add_expr(lexer);
    for is_cmp_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);
        lhs := expr;
        rhs := parse_add_expr(lexer);
        expr = make_node(Ast_Expr);
        expr.kind = Expr_Binary{op.kind, lhs, rhs};
    }
    return expr;
}

parse_add_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);
    expr := parse_mul_expr(lexer);
    for is_add_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);
        lhs := expr;
        rhs := parse_mul_expr(lexer);
        expr = make_node(Ast_Expr);
        expr.kind = Expr_Binary{op.kind, lhs, rhs};
    }
    return expr;
}

parse_mul_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);
    expr := parse_unary_expr(lexer);
    for is_mul_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);
        lhs := expr;
        rhs := parse_unary_expr(lexer);
        expr = make_node(Ast_Expr);
        expr.kind = Expr_Binary{op.kind, lhs, rhs};
    }
    return expr;
}

parse_unary_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    expr: ^Ast_Expr;
    if is_unary_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);

        rhs := parse_unary_expr(lexer);
        expr = make_node(Ast_Expr);
        expr.kind = Expr_Unary{op.kind, rhs};
    }
    // todo(josh)
    // else if is_token(.Cast) {
    //     cast_keyword := next_token();
    //     expect(.Left_Paren);
    //     target_type := parse_typespec(ws);
    //     expect(.Right_Paren);
    //     rhs := parse_unary_expr(ws);
    //     node := node(ws, cast_keyword, Ast_Cast{{}, target_type, rhs});
    //     depend(ws, node, rhs);
    //     depend(ws, node, target_type);
    //     return node.base;
    // }

    return parse_postfix_expr(lexer);
}

parse_postfix_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);

    base_expr := parse_base_expr(lexer);

    // todo(josh)
    // for is_postfix_op(lexer) {
    //     op, _, ok := get_next_token(lexer);
    //     next_expr: ^Ast_Node;
    //     switch op.kind {
    //         case .Period: {
    //             field_token := expect(lexer, .Identifier);
    //             selector := node(ws, token, Ast_Selector{{}, current_expr, sym_token.text});
    //             depend(ws, selector, current_expr);
    //             next_expr = selector.base;
    //         }
    //         case .Left_Paren: {
    //             parameters: [dynamic]^Ast_Node;
    //             for !is_token(Right_Paren) {
    //                 param := parse_expr(ws);
    //                 append(&parameters, param);

    //                 if is_token(Comma) {
    //                     next_token();
    //                 }
    //             }
    //             expect(Right_Paren);
    //             next_expr = node(ws, token, Ast_Call{{}, current_expr, parameters[:]}).base;

    //             depend(ws, next_expr, current_expr);

    //             // todo: factor into the loop above
    //             for p in parameters {
    //                 depend(ws, next_expr, p);
    //             }
    //         }
    //         case .Left_Square: {
    //             expression := parse_expr(ws);
    //             next_expr = node(ws, token, Ast_Subscript{{}, current_expr, expression}).base;
    //             depend(ws, next_expr, current_expr);
    //             expect(Right_Square);
    //         }
    //         case: {
    //             err := aprintln("is_postfix_op() returned true, but we must be missing a case in the switch for", op.kind);
    //             assert(false, err);
    //         }
    //     }

    //     assert(next_expr != nil);
    //     current_expr = next_expr;
    // }

    return base_expr;
}

parse_base_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, _, ok := get_next_token(lexer);
    expr := make_node(Ast_Expr);
    #partial
    switch token.kind {
        case .Null: {
            expr.kind = Expr_Null{};
        }
        case .Identifier: {
            ident := make_node(Ast_Identifier);
            ident.name = token.slice;
            expr.kind = Expr_Identifier{ident};
            queue_identifier_for_resolving(ident);
        }
        case .Number: {
            expr.kind = Expr_Number{strconv.parse_int(token.slice)};
        }
        case .String: {
            expr.kind = Expr_String{unescape_string(token.slice)};
        }
        case .LParen: {
            nested := parse_expr(lexer);
            expr.kind = Expr_Paren{nested};
            expect(lexer, .RParen);
        }
        // case .Sizeof: {
        //     expect(Left_Paren);
        //     typespec := parse_typespec(ws);
        //     expect(Right_Paren);
        //     expr := node(ws, token, Ast_Sizeof{{}, typespec});
        //     depend(ws, expr, typespec);
        //     return expr.base;
        // }
        case: {
            unimplemented(fmt.tprint(token));
        }
    }

    assert(expr != nil);
    assert(expr.kind != nil);
    return expr;
}

unescape_string :: proc(str: string) -> string {
    unimplemented();
    return {};
}

is_or_op      :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .Or:  return true; } return false; }
is_and_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .And: return true; } return false; }
is_cmp_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .CMP_BEGIN...CMP_END: return true; } return false; }
is_add_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .ADD_BEGIN...ADD_END: return true; } return false; }
is_mul_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .MUL_BEGIN...MUL_END: return true; } return false; }
is_unary_op   :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .Minus, .Plus, .Ampersand:  return true; } return false; }
is_postfix_op :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .LParen, .LSquare, .Period: return true; } return false; }

NODE_MAGIC :: 273628378;
Ast_Node :: struct {
    kind: union {
        Ast_File,
        Ast_Scope,
        Ast_Var,
        Ast_Proc,
        Ast_Struct,
        Ast_Expr,
        Ast_Typespec,
        Ast_Identifier,
        Ast_Assign,
    },
    magic: int,
    s: int,
    enclosing_scope: ^Ast_Scope,
}

last_node_serial: int;
make_node :: proc($T: typeid) -> ^T {
    last_node_serial += 1;
    node := new(Ast_Node);
    node.kind = T{};
    node.magic = NODE_MAGIC;
    node.s = last_node_serial;
    node.enclosing_scope = current_scope;
    return cast(^T)node;
}

NODE :: proc(k: ^$T) -> ^Ast_Node {
    n := cast(^Ast_Node)k;
    assert(n.magic == NODE_MAGIC);
    return n;
}

Ast_File :: struct {
    name: string,
    block: ^Ast_Scope,
}

Ast_Scope :: struct {
    parent: ^Ast_Scope,
    nodes: [dynamic]^Ast_Node,
    declarations: [dynamic]^Declaration,
}

Ast_Var :: struct {
    name: string,
    typespec: ^Ast_Typespec,
    expr: ^Ast_Expr,
    type: ^Type,
    storage: IR_Storage,
}

Ast_Proc :: struct {
    name: string,
    params: []^Ast_Var,
    return_typespec: ^Ast_Typespec,
    block: ^Ast_Scope,
    variables: [dynamic]^Ast_Var,
    type: ^Type_Proc,
}

Ast_Struct :: struct {
    name: string,
    block: ^Ast_Scope,
    fields: [dynamic]^Ast_Var,
    type: ^Type_Struct,
}

Ast_Assign :: struct {
    op: Token_Kind,
    lhs, rhs: ^Ast_Expr,
}

Ast_Expr :: struct {
    kind: union {
        Expr_Binary,
        Expr_Unary,
        Expr_Number,
        Expr_String,
        Expr_Identifier,
        Expr_Null,
        Expr_Paren,
    },
    type: ^Type,
}
Expr_Binary :: struct {
    op: Token_Kind,
    lhs, rhs: ^Ast_Expr,
}
Expr_Unary :: struct {
    op: Token_Kind,
    rhs: ^Ast_Expr,
}
Expr_Number :: struct {
    // todo(josh): handle floats, etc
    int_value: int,
}
Expr_String :: struct {
    str: string,
}
Expr_Paren :: struct {
    expr: ^Ast_Expr,
}
Expr_Null :: struct {

}
Expr_Identifier :: struct {
    ident: ^Ast_Identifier,
}

Ast_Typespec :: struct {
    kind: union {
        Typespec_Identifier,
        Typespec_Ptr,
        Typespec_Slice,
        Typespec_Array,
    },
    type: ^Type,
}
Typespec_Identifier :: struct {
    ident: ^Ast_Identifier,
}
Typespec_Ptr :: struct {
    ptr_to: ^Ast_Typespec,
}
Typespec_Slice :: struct {
    slice_of: ^Ast_Typespec,
}
Typespec_Array :: struct {
    array_of: ^Ast_Typespec,
}

Ast_Identifier :: struct {
    name: string,
    resolved_declaration: ^Declaration,
    type: ^Type,
}

Declaration :: struct {
    name: string,
    kind: Declaration_Kind,
}

Declaration_Kind :: union {
    Decl_Type,
    Decl_Var,
    Decl_Struct,
    Decl_Proc,
}
Decl_Type :: struct {
    type: ^Type,
}
Decl_Var :: struct {
    var: ^Ast_Var,
}
Decl_Struct :: struct {
    structure: ^Ast_Struct,
}
Decl_Proc :: struct {
    procedure: ^Ast_Proc,
}

Operator :: enum {
    Plus,
    Minus,

}