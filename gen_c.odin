package main

import "core:fmt"
import "core:strings"

/*

C_PREAMBLE :: `#include <stdint.h>
#include <stdlib.h>
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

    print_to_buf(&sb, C_PREAMBLE);

    c_print_scope(&sb, global_scope, false);

    return strings.to_string(sb);
}

c_indent_level: int;

indent :: proc(sb: ^strings.Builder) {
    for i in 0..<c_indent_level {
        print_to_buf(sb, "    ");
    }
}

c_print_file :: proc(sb: ^strings.Builder, file: ^Ast_File) {
    c_print_scope(sb, file.block, false);
}

c_print_scope :: proc(sb: ^strings.Builder, scope: ^Ast_Scope, do_curlies: bool) {
    if do_curlies {
        print_to_buf(sb, "{\n");
        c_indent_level += 1;
    }
    for node in scope.nodes {
        if _, ok := node.kind.(Ast_Defer); ok {
            defer_stmt := &node.kind.(Ast_Defer);
            append(&scope.defer_stack, defer_stmt);
            continue;
        }

        if var, ok := node.kind.(Ast_Var); ok && var.is_const {
            continue;
        }

        if do_curlies do indent(sb);
        c_print_node(sb, node);
    }

    emit_defers_from_scope_to_scope(sb, scope, scope);

    if do_curlies {
        c_indent_level -= 1;
        indent(sb);
        print_to_buf(sb, "}\n");
    }
}

emit_defers_from_scope_to_scope :: proc(sb: ^strings.Builder, from: ^Ast_Scope, to: ^Ast_Scope, indent_first_element := true) {
    current := from;
    for {
        for idx := len(current.defer_stack)-1; idx >= 0; idx -= 1 {
            defer_stmt := current.defer_stack[idx];
            if idx != len(current.defer_stack)-1 || indent_first_element do indent(sb);
            c_print_node(sb, defer_stmt.stmt);
        }

        if current == to {
            return;
        }

        current = current.parent;
    }
}

c_print_node :: proc(sb: ^strings.Builder, node: ^Ast_Node, semicolon_and_newline := true) {
    switch kind in &node.kind {
        case Ast_File:       c_print_file  (sb, &kind);
        case Ast_Scope:      c_print_scope (sb, &kind, true);
        case Ast_Var:        c_print_var   (sb, &kind, semicolon_and_newline, true);
        case Ast_Proc:       c_print_proc  (sb, &kind);
        case Ast_Return:     c_print_return(sb, &kind);
        case Ast_Struct:     c_print_struct(sb, &kind);
        case Ast_If:         c_print_if    (sb, &kind);
        case Ast_While:      c_print_while (sb, &kind);
        case Ast_For:        c_print_for   (sb, &kind);
        case Ast_Assign:     c_print_assign(sb, &kind, semicolon_and_newline);
        case Ast_Identifier: print_to_buf(sb, kind.name);
        case Ast_Continue:   emit_defers_from_scope_to_scope(sb, node.enclosing_scope, kind.scope_to_continue, false); indent(sb); print_to_buf(sb, "continue;\n");
        case Ast_Break:      emit_defers_from_scope_to_scope(sb, node.enclosing_scope, kind.scope_to_break, false);    indent(sb); print_to_buf(sb, "break;\n");
        case Ast_Defer:      panic("shouldn't have defer here");
        case Ast_Expr:       panic("shouldn't get in here with an Ast_Expr, only Ast_Expr_Statement");
        case Ast_Expr_Statement: {
            c_print_expr(sb, kind.expr);
            if semicolon_and_newline do print_to_buf(sb, ";\n");
        }
        case Ast_Include: {
            unimplemented();
        }
        case: panic(tprint(kind));
    }
}

c_print_var :: proc(sb: ^strings.Builder, var: ^Ast_Var, semicolon_and_newline: bool, zero_initialize: bool) {
    if var.is_const {
        return;
    }

    print_to_buf(sb, c_print_typespec(var.typespec, var.name));
    if var.expr != nil {
        print_to_buf(sb, " = ");
        c_print_expr(sb, var.expr);
    }
    else {
        if zero_initialize {
            print_to_buf(sb, " = {0}");
        }
    }
    if semicolon_and_newline do print_to_buf(sb, ";\n");
}

c_print_proc :: proc(sb: ^strings.Builder, procedure: ^Ast_Proc) {
    if procedure.is_foreign do return;

    do_space := true;
    if procedure.return_typespec != nil {
        if _, is_array := procedure.return_typespec.type.kind.(Type_Array); is_array {
            panic("Returning arrays is not currently supported because C.");
        }
    }

    print_to_buf(sb, c_print_typespec(procedure.return_typespec, procedure.name));
    print_to_buf(sb, "(");
    comma := "";
    for param in procedure.params {
        print_to_buf(sb, comma);
        comma = ", ";
        c_print_var(sb, param, false, false);
    }
    print_to_buf(sb, ") ");
    c_print_scope(sb, procedure.block, true);
    print_to_buf(sb, "\n");
}

c_print_return :: proc(sb: ^strings.Builder, return_statement: ^Ast_Return) {
    if return_statement.expr != nil {
        print_to_buf(sb, c_print_typespec(return_statement.matching_proc.return_typespec, aprint("__temp_", NODE(return_statement).s)), " = ");
        c_print_expr(sb, return_statement.expr);
        print_to_buf(sb, ";\n");
    }
    emit_defers_from_scope_to_scope(sb, NODE(return_statement).enclosing_scope, return_statement.matching_proc.block, false);
    indent(sb);
    print_to_buf(sb, "return");
    if return_statement.expr != nil {
        print_to_buf(sb, " __temp_", NODE(return_statement).s);
    }
    print_to_buf(sb, ";\n");
}

c_print_struct :: proc(sb: ^strings.Builder, structure: ^Ast_Struct) {
    print_to_buf(sb, "typedef struct {\n");
    c_indent_level += 1;
    for field in structure.fields {
        indent(sb);
        c_print_var(sb, field, true, false);
    }
    c_indent_level -= 1;
    indent(sb);
    print_to_buf(sb, "} ", structure.name, ";\n\n");
}

c_print_if :: proc(sb: ^strings.Builder, if_statement: ^Ast_If) {
    print_to_buf(sb, "if (");
    c_print_expr(sb, if_statement.condition);
    print_to_buf(sb, ") ");
    c_print_scope(sb, if_statement.body, true);

    if if_statement.else_stmt != nil {
        indent(sb);
        print_to_buf(sb, "else ");
        c_print_node(sb, if_statement.else_stmt);
        print_to_buf(sb, "\n"); // note(josh): this causes extra newlines to happen sometimes
    }
    else {
        print_to_buf(sb, "\n");
    }
}

c_print_while :: proc(sb: ^strings.Builder, while_loop: ^Ast_While) {
    print_to_buf(sb, "while (");
    c_print_expr(sb, while_loop.condition);
    print_to_buf(sb, ") ");
    c_print_scope(sb, while_loop.body, true);
    print_to_buf(sb, "\n");
}

c_print_for :: proc(sb: ^strings.Builder, for_loop: ^Ast_For) {
    print_to_buf(sb, "for (");
    c_print_node(sb, for_loop.pre_statement, false);
    print_to_buf(sb, "; ");
    c_print_expr(sb, for_loop.condition);
    print_to_buf(sb, "; ");
    c_print_node(sb, for_loop.post_statement, false);
    print_to_buf(sb, ") ");
    c_print_scope(sb, for_loop.body, true);
    print_to_buf(sb, "\n");
}

c_print_assign :: proc(sb: ^strings.Builder, assign: ^Ast_Assign, semicolon_and_newline: bool) {
    c_print_expr(sb, assign.lhs);
    #partial
    switch assign.op {
        case .Assign:          print_to_buf(sb, " = ");
        case .Plus_Assign:     print_to_buf(sb, " += ");
        case .Minus_Assign:    print_to_buf(sb, " -= ");
        case .Multiply_Assign: print_to_buf(sb, " *= ");
        case .Divide_Assign:   print_to_buf(sb, " /= ");
        case: panic(tprint(assign.op));
    }
    c_print_expr(sb, assign.rhs);
    if semicolon_and_newline do print_to_buf(sb, ";\n");
}

c_print_expr :: proc(sb: ^strings.Builder, expr: ^Ast_Expr) {
    if expr.constant_value != nil {
        switch kind in expr.constant_value {
            case i64:    print_to_buf(sb, kind); return;
            case f64:    print_to_buf(sb, kind); return;
            case bool:   print_to_buf(sb, kind); return;
            case TypeID: print_to_buf(sb, "/* TypeID */", kind); return;
            case string: // we still need our special string stuff
        }
    }

    switch kind in expr.kind {
        case Expr_Binary: {
            if kind.lhs.type == type_string {
                assert(kind.rhs.type == type_string);
                assert(kind.op == .Equal_To || kind.op == .Not_Equal);
                if kind.op == .Not_Equal {
                    print_to_buf(sb, "!");
                }
                print_to_buf(sb, "string_eq(");
                c_print_expr(sb, kind.lhs);
                print_to_buf(sb, ", ");
                c_print_expr(sb, kind.rhs);
                print_to_buf(sb, ")");
            }
            else {
                c_print_expr(sb, kind.lhs);
                c_print_op(sb, kind.op, true);
                c_print_expr(sb, kind.rhs);
            }
        }
        case Expr_Size_Of: {
            constant_size := expr.constant_value.(i64);
            print_to_buf(sb, constant_size);
        }
        case Expr_Cast: {
            print_to_buf(sb, "(", c_print_typespec(kind.typespec, ""), ")");
            c_print_expr(sb, kind.rhs);
        }
        case Expr_Selector: {
            c_print_expr(sb, kind.lhs);
            print_to_buf(sb, ".");
            print_to_buf(sb, kind.field);
        }
        case Expr_Subscript: {
            c_print_expr(sb, kind.lhs);
            print_to_buf(sb, "[");
            c_print_expr(sb, kind.index);
            print_to_buf(sb, "]");
        }
        case Expr_Address_Of: {
            print_to_buf(sb, "&");
            c_print_expr(sb, kind.rhs);
        }
        case Expr_Dereference: {
            print_to_buf(sb, "(*");
            c_print_expr(sb, kind.lhs);
            print_to_buf(sb, ")");
        }
        case Expr_Unary: {
            c_print_op(sb, kind.op, false);
            c_print_expr(sb, kind.rhs);
        }
        case Expr_Number: {
            print_to_buf(sb, kind.int_value); // todo(josh): handle more numeric types
        }
        case Expr_String: {
            print_to_buf(sb, "(String){\"", kind.str, "\", ", kind.length, "}");
        }
        case Expr_Identifier: {
            print_to_buf(sb, kind.ident.name);
        }
        case Expr_Call: {
            c_print_expr(sb, kind.procedure_expr);
            print_to_buf(sb, "(");
            comma := "";
            for param in kind.params {
                print_to_buf(sb, comma);
                comma = ", ";
                c_print_expr(sb, param);
            }
            print_to_buf(sb, ")");
        }
        case Expr_Null:  print_to_buf(sb, "NULL");
        case Expr_True:  print_to_buf(sb, "true");
        case Expr_False: print_to_buf(sb, "false");
        case Expr_Paren: {
            print_to_buf(sb, "(");
            c_print_expr(sb, kind.expr);
            print_to_buf(sb, ")");
        }
        case Expr_Typespec: {
            panic("Should probably never get here?");
        }
        case: panic(tprint(kind));
    }
}

c_print_typespec :: proc(typespec: ^Expr_Typespec, var_name: string) -> string {
    if typespec == nil {
        return aprint("void ", var_name);
    }
    var_name := var_name;
    assert(typespec.type != nil);

    switch kind in typespec.kind {
        case Typespec_Identifier: {
            switch typespec.type {
                case type_string: return aprint("String ", var_name);
                case type_rawptr: return aprint("void *", var_name);
                case: return aprint(kind.ident.name, " ", var_name);
            }
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
}

c_print_op :: proc(sb: ^strings.Builder, op: Operator, with_spaces: bool) {
    if with_spaces do print_to_buf(sb, " ");
    switch op {
        case .Multiply:      print_to_buf(sb, "*");
        case .Divide:        print_to_buf(sb, "/");
        case .Mod:           print_to_buf(sb, "%");
        case .Mod_Mod:       print_to_buf(sb, "%%");
        case .Shift_Left:    print_to_buf(sb, "<<");
        case .Shift_Right:   print_to_buf(sb, ">>");
        case .Plus:          print_to_buf(sb, "+");
        case .Minus:         print_to_buf(sb, "-");
        case .Bit_Xor:       print_to_buf(sb, "^");
        case .Bit_And:       print_to_buf(sb, "&");
        case .Bit_Or:        print_to_buf(sb, "|");
        case .Bit_Not:       print_to_buf(sb, "~");
        case .Not:           print_to_buf(sb, "!");
        case .Equal_To:      print_to_buf(sb, "==");
        case .Not_Equal:     print_to_buf(sb, "!=");
        case .Less:          print_to_buf(sb, "<");
        case .Greater:       print_to_buf(sb, ">");
        case .Less_Equal:    print_to_buf(sb, "<=");
        case .Greater_Equal: print_to_buf(sb, ">=");
        case .And:           print_to_buf(sb, "&&");
        case .Or:            print_to_buf(sb, "||");
    }
    if with_spaces do print_to_buf(sb, " ");
}

print_to_buf :: proc(sb: ^strings.Builder, args: ..any) {
    for arg in args {
        fmt.sbprint(sb, arg);
    }
}

*/