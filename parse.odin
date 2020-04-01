package main

import "core:fmt"
import "core:strings"
import "core:strconv"

global_scope: ^Ast_Scope;
current_scope: ^Ast_Scope;
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
            case .Return: {
                get_next_token(lexer);
                if _, ok := peek_kind(lexer, .Semicolon); ok {
                    return_node := make_node(Ast_Return);
                    node = NODE(return_node);
                }
                else {
                    expr := parse_expr(lexer);
                    return_node := make_node(Ast_Return);
                    return_node.expr = expr;
                    node = NODE(return_node);
                }
                expect(lexer, .Semicolon);
            }
            case .RCurly: break node_loop;
            case: {
                root_expr := parse_expr(lexer);
                token, ok := peek(lexer);
                assert(ok);
                #partial
                switch token.kind {
                    case .Assign: {
                        lhs := root_expr;
                        get_next_token(lexer); // todo(josh): handle +=, -=, etc
                        rhs := parse_expr(lexer);
                        assign := make_node(Ast_Assign);
                        assign^ = Ast_Assign{token.kind, lhs, rhs};
                        node = NODE(assign);
                        expect(lexer, .Semicolon);
                    }
                    case .Semicolon: {
                        get_next_token(lexer);
                        expr_stmt := make_node(Ast_Expr_Statement);
                        expr_stmt.expr = root_expr;
                        node = NODE(expr_stmt);
                    }
                    case: {
                        unimplemented(fmt.tprint(token.kind));
                    }
                }
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
                    typespec.kind = Typespec_Array{parse_typespec(lexer), length};
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

    // name
    expect(lexer, .Proc);
    name_token := expect(lexer, .Identifier);
    procedure.name = name_token.slice;

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
        append(&params, param);
    }
    procedure.params = params[:];

    // return value
    return_typespec: ^Ast_Typespec;
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

    if semicolon, ok := peek(lexer); ok && semicolon.kind == .Semicolon {
        assert(procedure.is_foreign); // todo(josh): should this assert be here? can non-foreign procs not have bodies?
        t, _, ok := get_next_token(lexer);
    }
    else {
        assert(!procedure.is_foreign);
        // body
        body := parse_body(lexer);
        procedure.block = body;
    }

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
        expr.kind = Expr_Binary{token_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{token_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{token_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{token_operator(op.kind), lhs, rhs};
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
        expr.kind = Expr_Binary{token_operator(op.kind), lhs, rhs};
    }
    return expr;
}

parse_unary_expr :: proc(lexer: ^Lexer) -> ^Ast_Expr {
    expr: ^Ast_Expr;
    for is_unary_op(lexer) {
        op, _, ok := get_next_token(lexer);
        assert(ok);

        rhs := parse_unary_expr(lexer);
        expr = make_node(Ast_Expr);

        #partial
        switch op.kind {
            case .Ampersand:  expr.kind = Expr_Address_Of{rhs};
            case: expr.kind = Expr_Unary{token_operator(op.kind), rhs};
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
    token, _, ok := get_next_token(lexer);
    expr := make_node(Ast_Expr);
    #partial
    switch token.kind {
        case .Null:  expr.kind = Expr_Null{};
        case .True:  expr.kind = Expr_True{};
        case .False: expr.kind = Expr_False{};
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
            str, length := unescape_string(token.slice);
            expr.kind = Expr_String{str, length};
        }
        case .LParen: {
            nested := parse_expr(lexer);
            expr.kind = Expr_Paren{nested};
            expect(lexer, .RParen);
        }
        case: {
            unimplemented(fmt.tprint(token));
        }
    }

    assert(expr != nil);
    assert(expr.kind != nil);
    return expr;
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

is_or_op      :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .Or:                                return true; } return false; }
is_and_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .And:                               return true; } return false; }
is_cmp_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .CMP_BEGIN...CMP_END:               return true; } return false; }
is_add_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .ADD_BEGIN...ADD_END:               return true; } return false; }
is_mul_op     :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .MUL_BEGIN...MUL_END:               return true; } return false; }
is_unary_op   :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .Minus, .Plus, .Ampersand:          return true; } return false; }
is_postfix_op :: proc(lexer: ^Lexer) -> bool { token, ok := peek(lexer); assert(ok); #partial switch token.kind { case .LParen, .LSquare, .Period, .Caret: return true; } return false; }

token_operator :: proc(t: Token_Kind, loc := #caller_location) -> Operator {
    #partial
    switch t {
        case .Multiply:      return .Multiply;
        case .Divide:        return .Divide;
        case .Mod:           return .Mod;
        case .Mod_Mod:       return .Mod_Mod;
        case .Shift_Left:    return .Shift_Left;
        case .Shift_Right:   return .Shift_Right;
        case .Bit_Or:        return .Bit_Or;
        case .Caret:         return .Bit_Xor;
        case .Bit_Not:       return .Bit_Not;
        case .Equal_To:      return .Equal_To;
        case .Not_Equal:     return .Not_Equal;
        case .Less:          return .Less;
        case .Greater:       return .Greater;
        case .Less_Equal:    return .Less_Equal;
        case .Greater_Equal: return .Greater_Equal;
        case .Not:           return .Not;
        case .And:           return .And;
        case .Or:            return .Or;
        case .Plus:          return .Plus;
        case .Minus:         return .Minus;
        case: panic(tprint(t, " caller: ", loc));
    }
    unreachable();
    return {};
}

NODE_MAGIC :: 273628378;
Ast_Node :: struct {
    kind: union {
        Ast_File,
        Ast_Scope,
        Ast_Var,
        Ast_Proc,
        Ast_Struct,
        Ast_Expr,
        Ast_Expr_Statement,
        Ast_Typespec,
        Ast_Identifier,
        Ast_Assign,
        Ast_Return,
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
}

Ast_Proc :: struct {
    name: string,
    params: []^Ast_Var,
    return_typespec: ^Ast_Typespec,
    block: ^Ast_Scope,
    variables: [dynamic]^Ast_Var,
    type: ^Type_Proc,
    is_foreign: bool,
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

Ast_Return :: struct {
    expr: ^Ast_Expr, // note(josh): can be nil
}

Ast_Expr_Statement :: struct {
    expr: ^Ast_Expr,
}

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
        Expr_Null,
        Expr_True,
        Expr_False,
        Expr_Paren,
        Expr_Address_Of,
        Expr_Dereference,
    },
    type: ^Type,
    mode: Addressing_Mode,
}
Expr_Binary :: struct {
    op: Operator,
    lhs, rhs: ^Ast_Expr,
}
Expr_Unary :: struct {
    op: Operator,
    rhs: ^Ast_Expr,
}
Expr_Address_Of :: struct {
    rhs: ^Ast_Expr,
}
Expr_Dereference :: struct {
    lhs: ^Ast_Expr,
}
Expr_Number :: struct {
    // todo(josh): handle floats, etc
    int_value: int,
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

Addressing_Mode :: enum {
    No_Value,
    LValue,
    RValue,
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
    length: ^Ast_Expr,
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