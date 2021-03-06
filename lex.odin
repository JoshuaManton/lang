package main

import "core:fmt"

make_lexer :: proc(text: string) -> Lexer {
    return Lexer{text, 0};
}

get_next_token :: proc(lexer: ^Lexer) -> (Token, int, bool) {
    for len(lexer.text) > 0 && is_whitespace(lexer.text[0]) do lexer.text = lexer.text[1:];

    if len(lexer.text) == 0 do return {}, lexer.num_tokens-1, false;

    token: Token;
    switch lexer.text[0] {
        case '"': {
            token.slice = scan_string(lexer);
            assert(token.slice[len(token.slice)-1] == '"', "End of text from within string");
            token.kind = .String;
        }
        case '0'..'9': {
            token.slice = scan_number(lexer);
            token.kind = .Number;
        }
        case 'a'..'z', 'A'..'Z', '_': {
            token.slice = scan_identifier(lexer);
            token.kind = .Identifier;
            for keyword in keyword_mapping {
                if token.slice == keyword.text {
                    token.kind = keyword.keyword;
                    break;
                }
            }
        }
        case ';': token = {";", .Semicolon};
        case ':': token = {":", .Colon};
        case ',': token = {",", .Comma};
        case '.': token = {".", .Period};
        case '^': token = {"^", .Caret};

        case '+': token = tokens(lexer, {"+", .Plus},     {"+=", .Plus_Assign});
        case '-': token = tokens(lexer, {"-", .Minus},    {"-=", .Minus_Assign});
        case '*': token = tokens(lexer, {"*", .Multiply}, {"*=", .Multiply_Assign});
        case '/': {
            token = tokens(lexer, {"/", .Divide}, {"/=", .Divide_Assign}, {"//", .Line_Comment});
            if token.kind == .Line_Comment {
                cur := 0;
                for cur < len(lexer.text) && lexer.text[cur] != '\n' {
                    cur += 1;
                }
                token.slice = lexer.text[:cur];
            }
        }
        case '%': token = tokens(lexer, {"%", .Mod},       {"%%", .Mod_Mod});
        case '!': token = tokens(lexer, {"!", .Not},       {"!=", .Not_Equal});
        case '=': token = tokens(lexer, {"=", .Assign},    {"==", .Equal_To});
        case '<': token = tokens(lexer, {"<", .Less},      {"<=", .Less_Equal},    {"<<", .Shift_Left});
        case '>': token = tokens(lexer, {">", .Greater},   {">=", .Greater_Equal}, {">>", .Shift_Right});
        case '&': token = tokens(lexer, {"&", .Ampersand}, {"&&", .And});
        case '|': token = tokens(lexer, {"|", .Bar},       {"||", .Or});
        case '~': token = {"~", .Tilde};

        case '(': token = {"(", .LParen};
        case ')': token = {")", .RParen};
        case '{': token = {"{", .LCurly};
        case '}': token = {"}", .RCurly};
        case '[': token = {"[", .LSquare};
        case ']': token = {"]", .RSquare};
        case '#': {
            token = tokens(lexer,
                {"#foreign", .Directive_Foreign},
                {"#include", .Directive_Include},
            );
        }
        case: {
            unimplemented(fmt.tprint(rune(lexer.text[0])));
        }
    }

    lexer.text = lexer.text[len(token.slice):];
    lexer.num_tokens += 1;
    return token, lexer.num_tokens-1, true;
}

peek :: proc(lexer: ^Lexer) -> (Token, bool) {
    cpy := lexer^;
    token, _, ok := get_next_token(lexer);
    lexer^ = cpy;
    return token, ok;
}

peek_kind :: proc(lexer: ^Lexer, kind: Token_Kind) -> (Token, bool) {
    cpy := lexer^;
    token, _, ok := get_next_token(lexer);
    lexer^ = cpy;
    if !ok do return {}, false;
    return token, token.kind == kind;
}

expect :: proc(lexer: ^Lexer, kind: Token_Kind, loc := #caller_location) -> Token {
    token, _, ok := get_next_token(lexer);
    if !ok {
        assert(false, fmt.tprint("Unexpected end of text from: ", loc));
    }
    if token.kind != kind {
        assert(false, fmt.tprint("Unexpected token: ", token.slice, " expected: ", kind, " from: ", loc));
    }
    return token;
}

tokens :: proc(lexer: ^Lexer, tokens: ..Token) -> Token {
    longest := tokens[0];
    token_loop: for t in tokens {
        // if len(t.slice) <= len(longest.slice) do continue;
        for i in 0..<len(t.slice) {
            if lexer.text[i] != t.slice[i] do continue token_loop;
        }
        longest = t;
    }
    return longest;
}

scan_number :: proc(lexer: ^Lexer) -> string {
    end := 0;
    if lexer.text[0] == '0' {
        end += 1;
    }
    else {
        digit_loop1: for end < len(lexer.text) {
            switch lexer.text[end] {
                case '0'..'9': {
                    end += 1;
                }
                case: {
                    break digit_loop1;
                }
            }
        }
    }

    if end < len(lexer.text) {
        if lexer.text[end] == '.' {
            end += 1;
            digit_loop2: for end < len(lexer.text) {
                switch lexer.text[end] {
                    case '0'..'9': {
                        end += 1;
                    }
                    case: {
                        break digit_loop2;
                    }
                }
            }
        }
    }

    number := lexer.text[:end];
    return number;
}

scan_identifier :: proc(lexer: ^Lexer) -> string {
    end := 1;
    ident_loop: for end < len(lexer.text) {
        switch lexer.text[end] {
            case 'a'..'z', 'A'..'Z', '_', '0'..'9': {
                end += 1;
            }
            case: {
                break ident_loop;
            }
        }
    }
    ident := lexer.text[:end];
    return ident;
}

scan_string :: proc(lexer: ^Lexer) -> string {
    assert(lexer.text[0] == '"');
    end := 1;
    escape := false;
    for end < len(lexer.text)-1 {
        if !escape {
            if lexer.text[end] == '\\' do escape = true;
            else if lexer.text[end] == '"' do break;
        }
        else {
            escape = false;
        }
        end += 1;
    }
    end += 1;
    str := lexer.text[:end];
    return str;
}

is_whitespace :: proc(c: byte) -> bool {
    switch c {
        case ' ', '\t', '\r', '\n': return true;
    }
    return false;
}

Lexer :: struct {
    text: string,
    num_tokens: int,
}

Token :: struct {
    slice: string,
    kind: Token_Kind,
}

Token_Kind :: enum {
    If,
    Else,
    While,
    For,
    Defer,

    Var,
    Const,
    Proc,
    Return,
    Continue,
    Break,
    Struct,
    Switch,
    Enum,
    Null,
    True,
    False,
    Cast,
    Size_Of,
    Type_Of,

    Identifier,
    String,
    Number,

    Directive_Foreign,
    Directive_Include,

    Assign,
    Plus_Assign,
    Minus_Assign,
    Multiply_Assign,
    Divide_Assign,
    Semicolon,
    Colon,
    Comma,
    Period,

    LParen,
    RParen,
    LSquare,
    RSquare,
    LCurly,
    RCurly,

    Line_Comment,

    Multiply, MUL_BEGIN = Multiply,
    Divide,
    Mod,
    Mod_Mod,
    Ampersand, // & serves double-duty as binary bitwise AND and unary address-of
    Shift_Left,
    Shift_Right, MUL_END = Shift_Right,

    Plus, ADD_BEGIN = Plus,
    Minus,
    Tilde, // ~ serves double-duty as binary bitwise XOR and unary bitwise NOT
    Caret, // unary postfix dereference
    Bar, ADD_END = Bar,

    Equal_To, CMP_BEGIN = Equal_To,
    Not_Equal,
    Less,
    Greater,
    Less_Equal,
    Greater_Equal, CMP_END = Greater_Equal,

    Not, // !

    And, // &&
    Or,  // ||
}

Keyword_Mapping :: struct {
    text: string,
    keyword: Token_Kind,
}

keyword_mapping := [?]Keyword_Mapping {
    {"if",       .If},
    {"else",     .Else},
    {"while",    .While},
    {"for",      .For},
    {"defer",    .Defer},
    {"cast",     .Cast},
    {"sizeof",   .Size_Of},
    {"typeof",   .Type_Of},
    {"var",      .Var},
    {"const",    .Const},
    {"proc",     .Proc},
    {"return",   .Return},
    {"continue", .Continue},
    {"break",    .Break},
    {"struct",   .Struct},
    {"enum",     .Enum},
    {"switch",   .Switch},
    {"null",     .Null},
    {"true",     .True},
    {"false",    .False},
};