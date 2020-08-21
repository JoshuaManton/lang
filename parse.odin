package main

import "core:fmt"
import "core:strings"
import "core:strconv"

global_scope: ^Ast_Scope;
all_global_variables: [dynamic]^Ast_Var;
current_scope: ^Ast_Scope;
current_procedure: ^Ast_Proc;
current_loop_scope: ^Ast_Scope; // todo(josh): put this in Ast_Scope? Ast_Proc _would_ work but #run can exist outside of procedures

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

parse_scope :: proc(lexer: ^Lexer, push_loop_scope := false) -> ^Ast_Scope {
    scope := make_node(Ast_Scope);

    old_loop_scope := current_loop_scope;
    if push_loop_scope do current_loop_scope = scope;
    defer if push_loop_scope do current_loop_scope = old_loop_scope;

    PUSH_SCOPE(scope);

    statements: [dynamic]^Ast_Node;
    for {
        statement := parse_single_statement(lexer);
        if statement == nil do break;
        append(&statements, statement);
    }
    scope.nodes = statements;
    return scope;
}

@(deferred_out=pop_scope)
PUSH_SCOPE :: proc(scope: ^Ast_Scope) -> ^Ast_Scope {
    scope.parent = current_scope;
    old := current_scope;
    current_scope = scope;
    return old;
}
pop_scope :: proc(old: ^Ast_Scope) {
    current_scope = old;
}

parse_single_statement :: proc(lexer: ^Lexer) -> ^Ast_Node {
    statement_loop: for {
        token, ok := peek(lexer);
        if !ok do return nil;

        #partial
        switch token.kind {
            case .Var:    return NODE(parse_var(lexer, true));
            case .Const:  return NODE(parse_var(lexer, true));

            case .Proc:   return NODE(parse_proc(lexer));
            case .Struct: return NODE(parse_struct(lexer));
            case .Return: return NODE(parse_return(lexer));
            case .If:     return NODE(parse_if(lexer));
            case .While:  return NODE(parse_while(lexer));
            case .For:    return NODE(parse_for(lexer));
            case .Defer:  return NODE(parse_defer(lexer));
            case .LCurly: return NODE(parse_body(lexer));
            case .RCurly: return nil;
            case .Line_Comment: {
                get_next_token(lexer);
                continue statement_loop;
            }
            case .Continue: {
                get_next_token(lexer);
                expect(lexer, .Semicolon);
                continue_node := make_node(Ast_Continue);
                assert(current_loop_scope != nil);
                continue_node.scope_to_continue = current_loop_scope;
                return NODE(continue_node);
            }
            case .Break: {
                get_next_token(lexer);
                expect(lexer, .Semicolon);
                break_node := make_node(Ast_Break);
                assert(current_loop_scope != nil);
                break_node.scope_to_break = current_loop_scope;
                return NODE(break_node);
            }
            case: {
                root_expr := parse_expr(lexer);
                token, ok := peek(lexer);
                assert(ok);
                #partial
                switch token.kind {
                    // todo(josh): the rest of the assignment variants, <<=, >>=, %=, etc
                    case .Assign, .Plus_Assign, .Minus_Assign, .Multiply_Assign, .Divide_Assign: {
                        lhs := root_expr;
                        get_next_token(lexer);
                        rhs := parse_expr(lexer);
                        assign := make_node(Ast_Assign);
                        assign^ = Ast_Assign{token.kind, lhs, rhs};
                        expect(lexer, .Semicolon);
                        return NODE(assign);
                    }
                    case .Semicolon: {
                        get_next_token(lexer);
                        expr_stmt := make_node(Ast_Expr_Statement);
                        expr_stmt.expr = root_expr;
                        return NODE(expr_stmt);
                    }
                    case: {
                        unimplemented(fmt.tprint(token.kind));
                    }
                }
            }
        }
    }

    unreachable();
}

parse_var :: proc(lexer: ^Lexer, require_semicolon: bool) -> ^Ast_Var {
    is_const := false;
    if _, ok := peek_kind(lexer, .Var); ok {
        get_next_token(lexer);
    }
    else if _, ok := peek_kind(lexer, .Const); ok {
        get_next_token(lexer);
        is_const = true;
    }

    name_token := expect(lexer, .Identifier);

    typespec: ^Expr_Typespec;
    if _, ok := peek_kind(lexer, .Colon); ok {
        expect(lexer, .Colon);
        typespec = parse_typespec(lexer);
    }

    expr: ^Ast_Expr;
    if _, ok := peek_kind(lexer, .Assign); ok {
        get_next_token(lexer);
        expr = parse_expr(lexer);
    }

    if require_semicolon {
        expect(lexer, .Semicolon);
    }

    var := make_node(Ast_Var);
    var.name = name_token.slice;
    var.typespec = typespec;
    var.expr = expr;
    var.is_const = is_const;

    if current_procedure != nil {
        append(&current_procedure.variables, var);
    }
    else {
        append(&all_global_variables, var);
    }

    register_declaration(current_scope, var.name, Decl_Var{var});
    return var;
}

parse_typespec :: proc(lexer: ^Lexer) -> ^Expr_Typespec {
    token, _, ok := get_next_token(lexer);
    assert(ok);
    typespec: Expr_Typespec;
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
                    typespec.kind = Typespec_Array{parse_typespec(lexer), length};
                }
            }
        }
        case: unimplemented(fmt.tprint(token.kind));
    }
    assert(typespec.kind != nil);

    expr := make_node(Ast_Expr);
    expr.kind = typespec;
    return &expr.kind.(Expr_Typespec);
}

parse_proc :: proc(lexer: ^Lexer) -> ^Ast_Proc {
    procedure := make_node(Ast_Proc);

    old_proc := current_procedure;
    current_procedure = procedure;
    defer current_procedure = old_proc;

    // name
    expect(lexer, .Proc);
    name_token := expect(lexer, .Identifier);
    procedure.name = name_token.slice;
    register_declaration(current_scope, procedure.name, Decl_Proc{procedure});

    // a procedure has it's own scope that the parameters live in, then there is another scope for the procedure block
    procedure.proc_scope = make_node(Ast_Scope);
    PUSH_SCOPE(procedure.proc_scope);

    // params
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
        param.is_parameter = true;
        append(&params, param);

        if c, ok := peek(lexer); ok {
            if c.kind == .Comma {
                get_next_token(lexer);
            }
        }
    }
    procedure.params = params[:];

    // return value
    return_typespec: ^Expr_Typespec;
    {
        token, ok := peek(lexer);
        assert(ok);

        if token.kind == .Colon {
            get_next_token(lexer);
            return_typespec = parse_typespec(lexer);
        }
    }
    procedure.return_typespec = return_typespec;

    // directives
    directive_loop:
    for {
        if directive, ok := peek(lexer); ok {
            #partial
            switch directive.kind {
                case .Directive_Foreign: {
                    get_next_token(lexer);
                    procedure.is_foreign = true;
                }
                case: {
                    break directive_loop;
                }
            }
        }
    }

    // body
    if semicolon, ok := peek(lexer); ok && semicolon.kind == .Semicolon {
        assert(procedure.is_foreign); // todo(josh): should this assert be here? can non-foreign procs not have bodies?
        t, _, ok := get_next_token(lexer);
    }
    else {
        assert(!procedure.is_foreign);
        body := parse_body(lexer);
        procedure.block = body;
    }

    return procedure;
}

parse_body :: proc(lexer: ^Lexer, push_loop_scope := false) -> ^Ast_Scope {
    expect(lexer, .LCurly);
    block := parse_scope(lexer, push_loop_scope);
    expect(lexer, .RCurly);
    return block;
}

parse_struct :: proc(lexer: ^Lexer) -> ^Ast_Struct {
    structure := make_node(Ast_Struct);

    expect(lexer, .Struct);
    name_token := expect(lexer, .Identifier);
    structure.name = name_token.slice;
    register_declaration(current_scope, structure.name, Decl_Struct{structure});

    expect(lexer, .LCurly);
    field_loop: for {
        token, ok := peek(lexer);
        assert(ok);
        #partial
        switch token.kind {
            case .RCurly: {
                get_next_token(lexer);
                break field_loop;
            }
            case: {
                var := parse_var(lexer, true);
                append(&structure.fields, var);
            }
        }
    }

    return structure;
}

parse_if :: proc(lexer: ^Lexer) -> ^Ast_If {
    expect(lexer, .If);
    expect(lexer, .LParen);
    cond := parse_expr(lexer);
    expect(lexer, .RParen);
    body := parse_body(lexer);
    if_statement := make_node(Ast_If);
    if_statement.condition = cond;
    if_statement.body = body;

    if _, ok := peek_kind(lexer, .Else); ok {
        get_next_token(lexer);
        if_statement.else_stmt = parse_single_statement(lexer);
    }

    return if_statement;
}

parse_while :: proc(lexer: ^Lexer) -> ^Ast_While {
    expect(lexer, .While);
    expect(lexer, .LParen);
    condition := parse_expr(lexer);
    expect(lexer, .RParen);
    body := parse_body(lexer, true);
    while_loop := make_node(Ast_While);
    while_loop.condition = condition;
    while_loop.body = body;
    return while_loop;
}

parse_for :: proc(lexer: ^Lexer) -> ^Ast_For {
    expect(lexer, .For);
    expect(lexer, .LParen);
    pre_statement := parse_single_statement(lexer);
    condition := parse_expr(lexer);
    expect(lexer, .Semicolon);
    post_statement := parse_single_statement(lexer);
    expect(lexer, .RParen);
    body := parse_body(lexer, true);
    for_loop := make_node(Ast_For);
    for_loop.pre_statement = pre_statement;
    for_loop.condition = condition;
    for_loop.post_statement = post_statement;
    for_loop.body = body;
    return for_loop;
}

parse_defer :: proc(lexer: ^Lexer) -> ^Ast_Defer {
    expect(lexer, .Defer);
    stmt := parse_single_statement(lexer);
    defer_stmt := make_node(Ast_Defer);
    defer_stmt.stmt = stmt;
    append(&current_scope.all_defers, defer_stmt);
    return defer_stmt;
}

parse_return :: proc(lexer: ^Lexer) -> ^Ast_Return {
    return_statement := make_node(Ast_Return);
    return_statement.matching_proc = current_procedure;

    expect(lexer, .Return);
    if _, ok := peek_kind(lexer, .Semicolon); !ok {
        expr := parse_expr(lexer);
        return_statement.expr = expr;
    }
    expect(lexer, .Semicolon);

    return return_statement;
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
        expr.kind = Expr_Binary{binary_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{binary_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{binary_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{binary_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{binary_operator(op.kind), lhs, rhs};
    }
    return expr;
}

parse_unary_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    expr: ^Ast_Expr;
    for is_unary_op(lexer) {
        expr = make_node(Ast_Expr);

        op, _, ok := get_next_token(lexer);
        assert(ok);

        #partial
        switch op.kind {
            case .Cast: {
                expect(lexer, .LParen);
                typespec := parse_typespec(lexer);
                expect(lexer, .RParen);
                rhs := parse_unary_expr(lexer);
                expr.kind = Expr_Cast{typespec, rhs};
            }
            case .Size_Of: {
                expect(lexer, .LParen);
                thing_to_get_the_size_of := parse_expr(lexer);
                expect(lexer, .RParen);
                expr.kind = Expr_Size_Of{thing_to_get_the_size_of};
            }
            case .Ampersand: {
                rhs := parse_unary_expr(lexer);
                expr.kind = Expr_Address_Of{rhs};
            }
            case .Minus, .Plus, .Not: {
                rhs := parse_unary_expr(lexer);
                expr.kind = Expr_Unary{unary_operator(op.kind), rhs};
            }
            case: {
                panic(tprint("Unknown unary op: ", op.kind));
            }
        }
    }

    if expr != nil {
        return expr;
    }
    return parse_postfix_expr(lexer);
}

parse_postfix_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);

    base_expr := parse_base_expr(lexer);

    for is_postfix_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);

        #partial
        switch op.kind {
            case .LParen: {
                // proc call
                params: [dynamic]^Ast_Expr;
                first := true;
                for {
                    defer first = false;
                    token, ok := peek(lexer);
                    assert(ok);
                    if token.kind != .RParen {
                        if !first do expect(lexer, .Comma);
                        param := parse_expr(lexer);
                        append(&params, param);
                    }
                    else {
                        break;
                    }
                }
                expect(lexer, .RParen);

                call := make_node(Ast_Expr);
                call.kind = Expr_Call{base_expr, params[:]};
                base_expr = call;
            }
            case .LSquare: {
                index := parse_expr(lexer);
                expect(lexer, .RSquare);
                subscript := make_node(Ast_Expr);
                subscript.kind = Expr_Subscript{base_expr, index};
                base_expr = subscript;
            }
            case .Caret: {
                deref := make_node(Ast_Expr);
                deref.kind = Expr_Dereference{base_expr};
                base_expr = deref;
            }
            case .Period: {
                name := expect(lexer, .Identifier);
                assert(ok);
                selector := make_node(Ast_Expr);
                selector.kind = Expr_Selector{base_expr, name.slice};
                base_expr = selector;
            }
            case: panic(tprint(op.kind));
        }
    }

    return base_expr;
}

parse_base_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    token, ok := peek(lexer);
    assert(ok);
    #partial
    switch token.kind {
        case .Null:  get_next_token(lexer); return EXPR(make_expr(Expr_Null{}));
        case .True:  get_next_token(lexer); return EXPR(make_expr(Expr_True{}));
        case .False: get_next_token(lexer); return EXPR(make_expr(Expr_False{}));
        case .Identifier: {
            get_next_token(lexer);
            ident := make_node(Ast_Identifier);
            ident.name = token.slice;
            expr := make_expr(Expr_Identifier{ident});
            queue_identifier_for_resolving(ident);
            return EXPR(expr);
        }
        case .Number: {
            get_next_token(lexer);
            i64_val, ok1 := strconv.parse_i64(token.slice); assert(ok1);
            f64_val, ok2 := strconv.parse_f64(token.slice); assert(ok2);
            u64_val, ok3 := strconv.parse_u64(token.slice); assert(ok3);
            return EXPR(make_expr(Expr_Number{strings.contains(token.slice, "."), i64_val, f64_val, u64_val}));
        }
        case .String: {
            get_next_token(lexer);
            str, length := unescape_string(token.slice);
            return EXPR(make_expr(Expr_String{str, length}));
        }
        case .LParen: {
            get_next_token(lexer);
            nested := parse_expr(lexer);
            expect(lexer, .RParen);
            return EXPR(make_expr(Expr_Paren{nested}));
        }
        case .LSquare, .Caret: {
            return EXPR(parse_typespec(lexer)); // todo(josh): this stomps on the `expr := make_node(Ast_Expr);` above @Leak
        }
        case: {
            unimplemented(fmt.tprint(token));
        }
    }

    unreachable();
}

unescape_string :: proc(str: string) -> (string, int) {
    str := str;

    // trim out quotes
    assert(str[0] == '"');
    assert(str[len(str)-1] == '"');
    str = str[1:len(str)-1];

    length := len(str);

    escape := false;
    sb: strings.Builder;
    text_loop: for c in str {
        if !escape {
            switch c {
                case '\\': escape = true; length -= 1;
                case: fmt.sbprint(&sb, cast(rune)c);
            }
        }
        else {
            escape = false;
            switch c {
                case '"':  fmt.sbprint(&sb, "\\\"");
                case '\\': fmt.sbprint(&sb, "\\\\");
                case 'b':  fmt.sbprint(&sb, "\\b");
                case 'f':  fmt.sbprint(&sb, "\\f");
                case 'n':  fmt.sbprint(&sb, "\\n");
                case 'r':  fmt.sbprint(&sb, "\\r");
                case 't':  fmt.sbprint(&sb, "\\t");
                // case 'u':  fmt.sbprint(&sb, '\u'); // todo(josh): unicode
                case: panic(fmt.tprint("Unexpected escape character: ", c));
            }
        }
    }
    assert(escape == false, "end of string from within escape sequence");

    escaped := strings.to_string(sb);
    return escaped, length;
}

is_or_op      :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .Or:                                                return true; } return false; }
is_and_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .And:                                               return true; } return false; }
is_cmp_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .CMP_BEGIN...CMP_END:                               return true; } return false; }
is_add_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .ADD_BEGIN...ADD_END:                               return true; } return false; }
is_mul_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .MUL_BEGIN...MUL_END:                               return true; } return false; }
is_unary_op   :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .Minus, .Plus, .Ampersand, .Cast, .Size_Of, .Not:   return true; } return false; }
is_postfix_op :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .LParen, .LSquare, .Period, .Caret:                 return true; } return false; }

binary_operator :: proc(t: Token_Kind, loc := #caller_location) -> Operator {
    #partial
    switch t {
        case .Multiply:      return .Multiply;
        case .Divide:        return .Divide;
        case .Mod:           return .Mod;
        case .Mod_Mod:       return .Mod_Mod;
        case .Shift_Left:    return .Shift_Left;
        case .Shift_Right:   return .Shift_Right;
        case .Tilde:         return .Bit_Xor;
        case .Bar:           return .Bit_Or;
        case .Equal_To:      return .Equal_To;
        case .Not_Equal:     return .Not_Equal;
        case .Less:          return .Less;
        case .Greater:       return .Greater;
        case .Less_Equal:    return .Less_Equal;
        case .Greater_Equal: return .Greater_Equal;
        case .And:           return .And;
        case .Or:            return .Or;
        case .Plus:          return .Plus;
        case .Minus:         return .Minus;
        case: panic(tprint("invalid binary operator: ", t, " caller: ", loc));
    }
    unreachable();
}

unary_operator :: proc(t: Token_Kind, loc := #caller_location) -> Operator {
    #partial
    switch t {
        case .Tilde: return .Bit_Not;
        case .Plus:  return .Plus;
        case .Minus: return .Minus;
        case .Not:   return .Not;
        case: panic(tprint("invalid unary operator: ", t, " caller: ", loc));
    }
    unreachable();
}

NODE_MAGIC :: 273628378;
Ast_Node :: struct {
    kind: union {
        Ast_File,
        Ast_Scope,
        Ast_Var,
        Ast_Proc,
        Ast_Struct,
        Ast_If,
        Ast_While,
        Ast_For,
        Ast_Expr,
        Ast_Expr_Statement,
        Ast_Identifier,
        Ast_Assign,
        Ast_Return,
        Ast_Defer,
        Ast_Continue,
        Ast_Break,
    },
    magic: int,
    s: int,
    enclosing_scope: ^Ast_Scope,
    enclosing_procedure: ^Ast_Proc,
}

last_node_serial: int;
make_node :: proc($T: typeid) -> ^T {
    last_node_serial += 1;
    node := new(Ast_Node);
    node.kind = T{};
    node.magic = NODE_MAGIC;
    node.s = last_node_serial;
    node.enclosing_scope = current_scope;
    node.enclosing_procedure = current_procedure;
    when T == Ast_Expr {
        expr := &node.kind.(Ast_Expr);
        expr.magic = EXPR_MAGIC;
    }
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
    all_defers: [dynamic]^Ast_Defer,
    defer_stack: [dynamic]^Ast_Defer,
}

Ast_Var :: struct {
    name: string,
    typespec: ^Expr_Typespec,
    expr: ^Ast_Expr,
    type: ^Type,
    is_type_alias_for: ^Type,
    is_const: bool,
    is_parameter: bool,
    constant_value: Constant_Value,
    storage: ^IR_Storage,
}

Ast_Proc :: struct {
    name: string,
    params: []^Ast_Var,
    return_typespec: ^Expr_Typespec,
    proc_scope: ^Ast_Scope, // note(josh): proc_scope is one scope above `block` and holds the parameters
    block: ^Ast_Scope,
    variables: [dynamic]^Ast_Var, // note(josh): contains the procedures parameters and all vars defined in the body
    type: ^Type_Proc,
    is_foreign: bool,
}

Ast_Struct :: struct {
    name: string,
    fields: [dynamic]^Ast_Var,
    type: ^Type_Struct,
}

Ast_If :: struct {
    condition: ^Ast_Expr,
    body: ^Ast_Scope,
    else_stmt: ^Ast_Node,
}

Ast_While :: struct {
    condition: ^Ast_Expr,
    body: ^Ast_Scope,
}

Ast_For :: struct {
    pre_statement: ^Ast_Node,
    condition: ^Ast_Expr,
    post_statement: ^Ast_Node,
    body: ^Ast_Scope,
}

Ast_Assign :: struct {
    op: Token_Kind,
    lhs, rhs: ^Ast_Expr,
}

Ast_Return :: struct {
    expr: ^Ast_Expr, // note(josh): can be nil
    matching_proc: ^Ast_Proc,
}

Ast_Continue :: struct {
    scope_to_continue: ^Ast_Scope,
}

Ast_Break :: struct {
    scope_to_break: ^Ast_Scope,
}

Ast_Defer :: struct {
    stmt: ^Ast_Node,
}

Ast_Expr_Statement :: struct {
    expr: ^Ast_Expr,
}



Addressing_Mode :: enum {
    Invalid,
    No_Value,
    LValue,
    RValue,
    Constant,
}

EXPR_MAGIC :: 728376328;
Ast_Expr :: struct {
    kind: union {
        Expr_Binary,
        Expr_Unary,
        Expr_Number,
        Expr_String,
        Expr_Selector,
        Expr_Subscript,
        Expr_Identifier,
        Expr_Call,
        Expr_Cast,
        Expr_Null,
        Expr_True,
        Expr_False,
        Expr_Paren,
        Expr_Size_Of,
        Expr_Address_Of,
        Expr_Dereference,
        Expr_Typespec,
    },
    magic: int,
    type: ^Type,
    mode: Addressing_Mode,
    constant_value: Constant_Value,
}

make_expr :: proc(k: $T) -> ^T {
    e := make_node(Ast_Expr);
    e.kind = k;
    return &e.kind.(T);
}

EXPR :: proc(k: ^$T) -> ^Ast_Expr {
    e := cast(^Ast_Expr)k;
    assert(e.magic == EXPR_MAGIC);
    return e;
}

Expr_Binary :: struct {
    op: Operator,
    lhs, rhs: ^Ast_Expr,
}
Expr_Unary :: struct {
    op: Operator,
    rhs: ^Ast_Expr,
}
Expr_Size_Of :: struct {
    thing_to_get_the_size_of: ^Ast_Expr,
}
Expr_Address_Of :: struct {
    rhs: ^Ast_Expr,
}
Expr_Dereference :: struct {
    lhs: ^Ast_Expr,
}
Expr_Number :: struct {
    has_a_dot: bool,
    int_value: i64,
    float_value: f64,
    uint_value: u64,
}
Expr_String :: struct {
    str: string,
    length: int, // note(josh): not the same as len(str) because of escaped characters
}
Expr_Selector :: struct {
    lhs: ^Ast_Expr,
    field: string,
}
Expr_Subscript :: struct {
    lhs: ^Ast_Expr,
    index: ^Ast_Expr,
}
Expr_Paren :: struct {
    expr: ^Ast_Expr,
}
Expr_Null :: struct { }
Expr_True :: struct { }
Expr_False :: struct { }
Expr_Identifier :: struct {
    ident: ^Ast_Identifier,
}
Expr_Call :: struct {
    procedure_expr: ^Ast_Expr,
    params: []^Ast_Expr,
}
Expr_Cast :: struct {
    typespec: ^Expr_Typespec,
    rhs: ^Ast_Expr,
}

Expr_Typespec :: struct {
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
    ptr_to: ^Expr_Typespec,
}
Typespec_Slice :: struct {
    slice_of: ^Expr_Typespec,
}
Typespec_Array :: struct {
    array_of: ^Expr_Typespec,
    length: ^Ast_Expr,
}

Ast_Identifier :: struct {
    name: string,
    resolved_declaration: ^Declaration,
}

Constant_Value :: union {
    i64, f64, string, bool, TypeID,
}
TypeID :: distinct int;

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
    Multiply,
    Divide,
    Mod,
    Mod_Mod,
    Shift_Left,
    Shift_Right,
    Plus,
    Minus,
    Bit_Xor,
    Bit_Or,
    Bit_And,
    Bit_Not,
    Not,
    Equal_To,
    Not_Equal,
    Less,
    Greater,
    Less_Equal,
    Greater_Equal,
    And,
    Or,
}