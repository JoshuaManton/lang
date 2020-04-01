package main

import "core:fmt"
import "core:strings"

C_PREAMBLE :: `#include <stdint.h>
#include <assert.h>

typedef int8_t  i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;
static_assert(sizeof(int)==4, "Assertion failed: sizeof(int)==4");

typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef uint32_t uint;
static_assert(sizeof(uint)==4, "Assertion failed: sizeof(uint)==4");

typedef float  float32;
typedef double float64;
static_assert(sizeof(float)==4, "Assertion failed: sizeof(float)==4");

typedef u8 bool;
#define false 0
#define true  1

typedef struct {
    char *data;
    int length;
} String;

bool string_eq(String str1, String str2) {
    if (str1.length != str2.length) return false;
    if (str1.data == str2.data) return true;
    for (int i = 0; i < str1.length; i++) {
        if (str1.data[i] != str2.data[i]) {
            return false;
        }
    }
    return true;
}

void print_string(String str) {
    for (int i = 0; i < str.length; i++) {
        printf("%c", str.data[i]);
    }
    printf("\n");
}
void print_int(int i) {
    printf("%d\n", i);
}
void print_float(float f) {
    printf("%f\n", f);
}



// -------------------------------------------



`;

gen_c :: proc() -> string {
    sb: strings.Builder;

    sbprint(&sb, C_PREAMBLE);

    c_print_node(&sb, NODE(global_scope));

    return strings.to_string(sb);
}

c_indent_level: int;

indent :: proc(sb: ^strings.Builder) {
    for i in 0..<c_indent_level {
        sbprint(sb, "    ");
    }
}

c_print_node :: proc(sb: ^strings.Builder, node: ^Ast_Node, semicolon_and_newline := true) {
    switch kind in &node.kind {
        case Ast_File:       c_print_file  (sb, &kind);
        case Ast_Scope:      c_print_scope (sb, &kind);
        case Ast_Var:        c_print_var   (sb, &kind, semicolon_and_newline);
        case Ast_Proc:       c_print_proc  (sb, &kind);
        case Ast_Return:     c_print_return(sb, &kind);
        case Ast_Struct:     c_print_struct(sb, &kind);
        case Ast_If:         c_print_if    (sb, &kind);
        case Ast_While:      c_print_while (sb, &kind);
        case Ast_For:        c_print_for   (sb, &kind);
        case Ast_Assign:     c_print_assign(sb, &kind, semicolon_and_newline);
        case Ast_Identifier: sbprint(sb, kind.name);
        case Ast_Typespec:   panic("shouldn't have typespec here");
        case Ast_Expr:       panic("shouldn't get in here with an Ast_Expr, only Ast_Expr_Statement");
        case Ast_Expr_Statement: {
            c_print_expr(sb, kind.expr);
            if semicolon_and_newline do sbprint(sb, ";\n");
        }
        case: panic(tprint(kind));
    }
}

c_print_file :: proc(sb: ^strings.Builder, file: ^Ast_File) {
    c_print_scope(sb, file.block);
}

c_print_scope :: proc(sb: ^strings.Builder, scope: ^Ast_Scope) {
    for node in scope.nodes {
        indent(sb);
        c_print_node(sb, node);
    }
}

c_print_var :: proc(sb: ^strings.Builder, var: ^Ast_Var, semicolon_and_newline: bool) {
    sbprint(sb, c_print_typespec(var.typespec, var.name));
    sbprint(sb, " = ");
    if var.expr != nil {
        c_print_expr(sb, var.expr);
    }
    else {
        sbprint(sb, "{0}");
    }
    if semicolon_and_newline do sbprint(sb, ";\n");
}

c_print_proc :: proc(sb: ^strings.Builder, procedure: ^Ast_Proc) {
    if procedure.is_foreign do return;

    do_space := true;
    if procedure.return_typespec != nil {
        if _, is_array := procedure.return_typespec.type.kind.(Type_Array); is_array {
            panic("Returning arrays is not currently supported because C.");
        }
    }

    sbprint(sb, c_print_typespec(procedure.return_typespec, procedure.name));
    sbprint(sb, "(");
    comma := "";
    for param in procedure.params {
        sbprint(sb, comma);
        comma = ", ";
        c_print_var(sb, param, false);
    }
    sbprint(sb, ") {\n");
    c_indent_level += 1;
    c_print_scope(sb, procedure.block);
    c_indent_level -= 1;
    indent(sb);
    sbprint(sb, "}\n\n");
}

c_print_return :: proc(sb: ^strings.Builder, return_statement: ^Ast_Return) {
    sbprint(sb, "return");
    if return_statement.expr != nil {
        sbprint(sb, " ");
        c_print_expr(sb, return_statement.expr);
    }
    sbprint(sb, ";\n");
}

c_print_struct :: proc(sb: ^strings.Builder, structure: ^Ast_Struct) {
    sbprint(sb, "typedef struct {\n");
    for field in structure.fields {
        c_print_var(sb, field, true);
    }
    sbprint(sb, "} ", structure.name, ";\n\n");
}

c_print_if :: proc(sb: ^strings.Builder, if_statement: ^Ast_If) {
    sbprint(sb, "if (");
    c_print_expr(sb, if_statement.condition);
    sbprint(sb, ") {\n");
    c_indent_level += 1;
    c_print_scope(sb, if_statement.body);
    c_indent_level -= 1;
    indent(sb);
    sbprint(sb, "}\n");

    for else_if in if_statement.else_ifs {
        indent(sb);
        sbprint(sb, "else ");
        c_print_if(sb, else_if);
    }

    if if_statement.else_body != nil {
        indent(sb);
        sbprint(sb, "else {\n");
        c_indent_level += 1;
        c_print_scope(sb, if_statement.else_body);
        c_indent_level -= 1;
        indent(sb);
        sbprint(sb, "}\n");
    }
}

c_print_while :: proc(sb: ^strings.Builder, while_loop: ^Ast_While) {
    sbprint(sb, "while (");
    c_print_expr(sb, while_loop.condition);
    sbprint(sb, ") {\n");
    c_indent_level += 1;
    c_print_scope(sb, while_loop.body);
    c_indent_level -= 1;
    indent(sb);
    sbprint(sb, "}\n\n");
}

c_print_for :: proc(sb: ^strings.Builder, for_loop: ^Ast_For) {
    sbprint(sb, "for (");
    c_print_node(sb, for_loop.pre_statement, false);
    sbprint(sb, "; ");
    c_print_expr(sb, for_loop.condition);
    sbprint(sb, "; ");
    c_print_node(sb, for_loop.post_statement, false);
    sbprint(sb, ") {\n");
    c_indent_level += 1;
    c_print_scope(sb, for_loop.body);
    c_indent_level -= 1;
    indent(sb);
    sbprint(sb, "}\n\n");
}

c_print_expr :: proc(sb: ^strings.Builder, expr: ^Ast_Expr) {
    switch kind in expr.kind {
        case Expr_Binary: {
            if kind.lhs.type == type_string {
                assert(kind.rhs.type == type_string);
                assert(kind.op == .Equal_To || kind.op == .Not_Equal);
                if kind.op == .Not_Equal {
                    sbprint(sb, "!");
                }
                sbprint(sb, "string_eq(");
                c_print_expr(sb, kind.lhs);
                sbprint(sb, ", ");
                c_print_expr(sb, kind.rhs);
                sbprint(sb, ")");
            }
            else {
                c_print_expr(sb, kind.lhs);
                c_print_op(sb, kind.op, true);
                c_print_expr(sb, kind.rhs);
            }
        }
        case Expr_Selector: {
            c_print_expr(sb, kind.lhs);
            sbprint(sb, ".");
            sbprint(sb, kind.field);
        }
        case Expr_Subscript: {
            c_print_expr(sb, kind.lhs);
            sbprint(sb, "[");
            c_print_expr(sb, kind.index);
            sbprint(sb, "]");
        }
        case Expr_Address_Of: {
            sbprint(sb, "&");
            c_print_expr(sb, kind.rhs);
        }
        case Expr_Dereference: {
            sbprint(sb, "*");
            c_print_expr(sb, kind.lhs);
        }
        case Expr_Unary: {
            c_print_op(sb, kind.op, false);
            c_print_expr(sb, kind.rhs);
        }
        case Expr_Number: {
            sbprint(sb, kind.int_value); // todo(josh): handle more numeric types
        }
        case Expr_String: {
            sbprint(sb, "(String){\"", kind.str, "\", ", kind.length, "}");
        }
        case Expr_Identifier: {
            sbprint(sb, kind.ident.name);
        }
        case Expr_Call: {
            c_print_expr(sb, kind.procedure_expr);
            sbprint(sb, "(");
            comma := "";
            for param in kind.params {
                sbprint(sb, comma);
                comma = ", ";
                c_print_expr(sb, param);
            }
            sbprint(sb, ")");
        }
        case Expr_Null:  sbprint(sb, "NULL");
        case Expr_True:  sbprint(sb, "true");
        case Expr_False: sbprint(sb, "false");
        case Expr_Paren: {
            sbprint(sb, "(");
            c_print_expr(sb, kind.expr);
            sbprint(sb, ")");
        }
        case: panic(tprint(kind));
    }
}

c_print_typespec :: proc(typespec: ^Ast_Typespec, var_name: string) -> string {
    if typespec == nil {
        return aprint("void ", var_name);
    }
    var_name := var_name;
    assert(typespec.type != nil);

    switch kind in typespec.kind {
        case Typespec_Identifier: {
            if typespec.type == type_string {
                return aprint("String ", var_name);
            }
            return aprint(kind.ident.name, " ", var_name);
        }
        case Typespec_Ptr: {
            var_name = aprint("*", var_name);
            do_parens := true;
            if _, ok := kind.ptr_to.kind.(Typespec_Identifier); ok {
                do_parens = false;
            }

            if do_parens {
                var_name = aprint("(", var_name, ")");
            }
            return c_print_typespec(kind.ptr_to, var_name);
        }
        case Typespec_Array: {
            sb: strings.Builder;
            c_print_expr(&sb, kind.length);

            var_name = aprint(var_name, "[", strings.to_string(sb), "]");
            do_parens := true;
            if _, ok := kind.array_of.kind.(Typespec_Identifier); ok {
                do_parens = false;
            }

            if do_parens {
                var_name = aprint("(", var_name, ")");
            }
            return c_print_typespec(kind.array_of, var_name);
        }
        case Typespec_Slice: {
            unimplemented();
            // sbprint(sb, "*");
            // c_print_identifier(sb, kind.ptr_to);
        }
    }

    unreachable();
    return {};
}

c_print_assign_op :: proc(sb: ^strings.Builder, assign_op: Token_Kind, with_spaces: bool) {
    if with_spaces do sbprint(sb, " ");
    #partial
    switch assign_op {
        case .Assign: sbprint(sb, "=");
        case: panic(tprint(assign_op));
    }
    if with_spaces do sbprint(sb, " ");
}

c_print_op :: proc(sb: ^strings.Builder, op: Operator, with_spaces: bool) {
    if with_spaces do sbprint(sb, " ");
    switch op {
        case .Multiply:      sbprint(sb, "*");
        case .Divide:        sbprint(sb, "/");
        case .Mod:           sbprint(sb, "%");
        case .Mod_Mod:       sbprint(sb, "%%");
        case .Shift_Left:    sbprint(sb, "<<");
        case .Shift_Right:   sbprint(sb, ">>");
        case .Plus:          sbprint(sb, "+");
        case .Minus:         sbprint(sb, "-");
        case .Bit_Xor:       sbprint(sb, "^");
        case .Bit_And:       sbprint(sb, "&");
        case .Bit_Or:        sbprint(sb, "|");
        case .Bit_Not:       sbprint(sb, "~");
        case .Not:           sbprint(sb, "!");
        case .Equal_To:      sbprint(sb, "==");
        case .Not_Equal:     sbprint(sb, "!=");
        case .Less:          sbprint(sb, "<");
        case .Greater:       sbprint(sb, ">");
        case .Less_Equal:    sbprint(sb, "<=");
        case .Greater_Equal: sbprint(sb, ">=");
        case .And:           sbprint(sb, "&&");
        case .Or:            sbprint(sb, "||");
    }
    if with_spaces do sbprint(sb, " ");
}

c_print_assign :: proc(sb: ^strings.Builder, assign: ^Ast_Assign, semicolon_and_newline: bool) {
    c_print_expr(sb, assign.lhs);
    c_print_assign_op(sb, assign.op, true);
    c_print_expr(sb, assign.rhs);
    if semicolon_and_newline do sbprint(sb, ";\n");
}

sbprint :: fmt.sbprint;
aprint :: fmt.aprint;