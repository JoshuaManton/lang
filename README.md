# lang

This compiler implements a recursive-descent parser to parse source code into a syntax tree, typechecks the syntax tree and enforces the semantic rules of the language, generates an intermediate representation of the instruction stream, translates this intermediate representation to bytecode, and executes the bytecode in a virtual machine.

## Factorial

```c
#include "basic.lang" // contains VM intrinsics for print() and assert()

proc factorial(n: int) : int {
    if (n == 1) {
        return 1;
    }
    return n * factorial(n-1);
}

proc main() {
    var x: int = factorial(5); // the `int` is optional, as the type can be inferred based on the return type of `factorial()`
    print(x);
    assert(x == 120);
}
```

## Demo

```c
#include "basic.lang"

var aa: int;
var bb: int;
var cc: int;

struct Vector3 {
    x: int;
    y: int;
    z: int;
}

proc factorial(n: int) : int {
    if (n == 1) {
        return 1;
    }
    return n * factorial(n-1);
}

proc things() {
    var v: Vector3;
    v.x = 1;
    v.y = 4;
    v.z = 9;
    assert(v.x == 1);
    assert(v.y == 4);
    assert(v.z == 9);

    aa = 5;
    aa = factorial(aa);

    const SIX = 6;
    bb = factorial(SIX);

    cc = aa + bb;

    var x = factorial(10);

    assert(aa == 120);
    aa += 5;
    assert(aa == 125);
    aa -= 3;
    assert(aa == 122);
    aa *= 2;
    assert(aa == 244);
    // todo(josh): divide
    // aa /= 4;
    // assert(aa == 61);

    assert(bb == 720);
    assert(cc == 840);
    assert(x == 3628800);

    var foozlebarzle = 123;
    assert(foozlebarzle == 123);
}

proc int_sizes() {
    var a: i64;
    var b: i32;
    var c: i16;
    var d: i8 ;

    // todo(josh): need untyped types
    // a = 123;
    // b = 123;
    // c = 123;
    // d = 123;

    assert(sizeof(i64) == 8);
    assert(sizeof(i32) == 4);
    assert(sizeof(i16) == 2);
    assert(sizeof(i8 ) == 1);

    assert(sizeof(a) == 8);
    assert(sizeof(b) == 4);
    assert(sizeof(c) == 2);
    assert(sizeof(d) == 1);

    assert(sizeof(^int) == 8);
    assert(sizeof([]int) == 16);
}

proc type_alias() {
    const My_Int = int;
    var a: My_Int = 12;
    a += a + 12;
    assert(a == 36);

    const My_Vec = Vector3;
    var v: My_Vec;
    v.x = 1;
    v.y = 4;
    v.z = 9;
    assert(v.x == 1);
    assert(v.y == 4);
    assert(v.z == 9);
}

proc bool_stuff() {
    var t = 1 == 1;
    assert(typeof(t) == bool);
    assert(t == true);
    assert(t);

    var f = 1 == 2;
    assert(typeof(t) == typeof(f));
    assert(f == false);
    assert(!f);

    var thing: typeof(1==1) = true;
    assert(thing);

    if (!t) {
        panic();
    }
    if (f) {
        panic();
    }
}

var global_var: int;

proc pointers() {
    var some_int = 123;
    assert(some_int == 123);

    (&some_int)^ = 442;
    assert(some_int == 442);

    var thing = (&some_int)^;
    assert(thing == some_int);

    var ptr = &some_int;
    assert(ptr^ == some_int);

    ptr^ = 321;
    assert(some_int == 321);
    assert(some_int == ptr^);

    var ptr_ptr = &ptr;
    ptr_ptr^^ = 112;
    assert(some_int == 112);
    assert(some_int == ptr_ptr^^);

    var global_ptr = &global_var;
    global_ptr^ += 13;
    assert(global_var == 13);
    assert(global_var == global_ptr^);

    var v: Vector3;
    var y_ptr = &v.y;
    y_ptr^ = 149;
    assert(v.y == 149);
}

var global_var_with_init = 21;
var v: Vector3;

proc main() {
    assert(global_var_with_init == 21);
    v.z = 123;
    assert(v.z == 123);

    things();
    int_sizes();
    type_alias();
    bool_stuff();
    pointers();
    print(123);
}
```
