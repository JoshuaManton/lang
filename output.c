#include <stdint.h>
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



void variables() {
    print_string((String){"\n----- variables -----", 22});
    int x = 123;
    int y = 321;
    print_int(x);
    print_int(y);
    assert(x != y);
    y = 123;
    assert(x == y);
    int some_int = 123;
    float some_float = 321.000;
    print_float(some_float);
    some_float = (float )some_int;
    print_float(some_float);
    assert(true);
    print_string((String){"", 0});
    print_int(some_int);
    some_int += 2;
    print_int(some_int);
    some_int -= 2;
    print_int(some_int);
    some_int *= 2;
    print_int(some_int);
    some_int /= 2;
    print_int(some_int);
}

void basic_stuff() {
    print_string((String){"\n----- basic stuff -----", 24});
    int foo = 5;
    if (foo > 2) {
        print_string((String){"foo is greater than 2", 21});
    }

    if (foo < 2) {
        assert(false);
        print_string((String){"foo is less than 2", 18});
    }
    else if (foo > 10) {
        assert(false);
        print_string((String){"foo is greater than 10", 22});
    }
    else {
        print_string((String){"foo is greater than 2 and less than 10", 38});
    }


    print_string((String){"while loop:", 11});
    int x = 5;
    while (x >= 0) {
        print_int(x);
        x = x - 1;
    }

    print_string((String){"", 0});
    print_string((String){"for loop:", 9});
    for (int i = 0; i < 6; i += 1) {
        print_int(i);
    }

}

void pointers() {
    print_string((String){"\n----- pointers -----", 21});
    int x = 11111;
    print_int(x);
    int *ptr = &x;
    assert(x == 11111);
    (*ptr) = 44444;
    assert(x == 44444);
    print_int(x);
    int *(*ptr_to_ptr) = &ptr;
    (*(*ptr_to_ptr)) = 99999;
    assert(x == 99999);
    print_int(x);
}

void arrays() {
    print_string((String){"\n----- arrays -----", 19});
    int a[8] = {0};
    int b = 2;
    a[b] = 123;
    print_int(a[b]);
    int (*c)[8] = &a;
    (*c)[4] = 149;
    print_int(a[4]);
    int *(d[8]) = {0};
    int *((*e)[8]) = {0};
    int (*((*f)[8]))[16] = {0};
    int *(*(*x)) = {0};
    int ((y[6])[12])[3] = {0};
}

void strings() {
    print_string((String){"\n----- strings -----", 20});
    String str1 = (String){"Henlo, Sailor!", 14};
    String str2 = (String){"Henlo, Sailor!", 14};
    assert(string_eq(str1, str2));
    str2 = (String){"Hell no, Sailor!", 16};
    assert(!string_eq(str1, str2));
    String str3 = (String){"\n\r\t\"\\\b\f", 7};
    assert(str3.length == 7);
    print_string((String){"Hello, Sailor!", 14});
}

int foozle() {
    int a = 2;
    int b = 3;
    int __temp_543 = a + b;
    return __temp_543;
}

void procedures() {
    print_string((String){"\n----- procedures -----", 23});
    int result = foozle();
    assert(result == 5);
    print_int(result);
}

void defer_statements() {
    print_string((String){"\n----- defer -----", 18});
    int x = 111;
    assert(x == 111);
    {
        x = 123;
    }
    assert(x == 123);
    for (int i = 0; i < 4; i += 1) {
        int other = 123;
        while (other < 128) {
            other += 1;
            if (other < 125) {
                print_string((String){"Cool.", 5});
                continue;
            }

            if (other > 125) {
                print_string((String){"Cool.", 5});
                break;
            }

            print_string((String){"Cool.", 5});
        }

        if (true) {
            print_int(i);
            continue;
        }

        assert(false);
        print_int(i);
    }

    if (true) {
        print_string((String){"This defer should run!", 22});
        assert(x == 123);
        x = 222;
        assert(x == 222);
        return;
    }

    assert(false);
    print_string((String){"This defer should run!", 22});
    assert(x == 123);
    x = 222;
    assert(x == 222);
}

typedef struct {
    float x;
    float y;
    float z;
} Vector3;

void structs() {
    print_string((String){"\n----- structs -----", 20});
    Vector3 v = {0};
    v.x = 1.000;
    v.y = 4.000;
    v.z = 9.000;
    print_float(v.x);
    print_float(v.y);
    print_float(v.z);
}

void allocation() {
    print_string((String){"\n----- allocation -----", 23});
    void *thing = malloc(128);
}

void main() {
    variables();
    basic_stuff();
    pointers();
    arrays();
    strings();
    procedures();
    defer_statements();
    structs();
    allocation();
}

