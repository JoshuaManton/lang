#include <stdint.h>
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
    print_string((String){"\n\n----- variables -----\n", 24});
    int x = 123;
    int y = 321;
    print_int(x);
    print_int(y);
    assert(x != y);
    y = 123;
    assert(x == y);
}

void pointers() {
    print_string((String){"\n\n----- pointers -----\n", 23});
    int x = 11111;
    print_int(x);
    int *ptr = &x;
    assert(x == 11111);
    *ptr = 44444;
    assert(x == 44444);
    print_int(x);
    int *(*ptr_to_ptr) = &ptr;
    **ptr_to_ptr = 99999;
    assert(x == 99999);
    print_int(x);
}

void arrays() {
    print_string((String){"\n\n----- arrays -----\n", 21});
    int a[8] = {0};
    int b = 2;
    a[b] = 123;
    print_int(a[b]);
    int (*c)[8] = {0};
    int *(d[8]) = {0};
    int *((*e)[8]) = {0};
    int (*((*f)[8]))[16] = {0};
    int *(*(*x)) = {0};
    int ((y[1])[2])[3] = {0};
}

void strings() {
    print_string((String){"\n\n----- strings -----\n", 22});
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
    return a + b;
}

void procedures() {
    print_string((String){"\n\n----- procedures -----\n", 25});
    int result = foozle();
    print_int(result);
}

void main() {
    variables();
    pointers();
    arrays();
    strings();
    procedures();
}

