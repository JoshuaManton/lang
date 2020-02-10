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

        case '+': token = {"+", .Plus};
        case '-': token = {"-", .Minus};
        case '*': token = {"*", .Multiply};
        case '/': {
            token = tokens(lexer, {"/", .Divide}, {"//", .Line_Comment});
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
        case '|': token = tokens(lexer, {"|", .Bit_Or},    {"||", .Or});
        case '~': token = {"~", .Bit_Xor};

        case '(': token = {"(", .LParen};
        case ')': token = {")", .RParen};
        case '{': token = {"{", .LCurly};
        case '}': token = {"}", .RCurly};
        case '[': token = {"[", .LSquare};
        case ']': token = {"]", .RSquare};
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

peek_kind :: proc(lexer: ^Lexer, kind: Token_Kind) -> bool {
    cpy := lexer^;
    token, _, ok := get_next_token(lexer);
    lexer^ = cpy;
    if !ok do return false;
    return token.kind == kind;
}

expect :: proc(lexer: ^Lexer, kind: Token_Kind) -> Token {
    token, _, ok := get_next_token(lexer);
    if !ok {
        assert(false, fmt.tprint("Unexpected end of text"));
    }
    if token.kind != kind {
        assert(false, fmt.tprint("Unexpected token: ", token.slice));
    }
    return token;
}

tokens :: proc(lexer: ^Lexer, tokens: ..Token) -> Token {
    longest := tokens[0];
    token_loop: for t in tokens {
        if len(t.slice) <= len(longest.slice) do continue;
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
    for end < len(lexer.text)-1 && lexer.text[end] != '"' {
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
    Var,
    Proc,
    Return,
    Struct,
    Switch,
    Enum,
    Null,

    Identifier,
    String,
    Number,

    Assign,
    Semicolon,
    Colon,
    Comma,
    Period,
    Caret,

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
    Ampersand, // & bit AND
    Shift_Left,
    Shift_Right, MUL_END = Shift_Right,

    Plus, ADD_BEGIN = Plus,
    Minus,
    Bit_Xor, // ~ bit XOR
    Bit_Or, ADD_END = Bit_Or, // | bit OR

    Equal_To, CMP_BEGIN = Equal_To,
    Not_Equal,
    Less,
    Greater,
    Less_Equal,
    Greater_Equal, CMP_END = Greater_Equal,

    Not, // !

    And, // &&
    Or, // ||
}

Keyword_Mapping :: struct {
    text: string,
    keyword: Token_Kind,
}

keyword_mapping := [?]Keyword_Mapping {
    {"var",    .Var},
    {"proc",   .Proc},
    {"return", .Return},
    {"struct", .Struct},
    {"enum",   .Enum},
    {"switch", .Switch},
    {"null",   .Null},
};