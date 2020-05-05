package main

import "core:fmt"
import "core:mem"
import "core:strings"

// todo(josh): graphical debugger

VM :: struct {
    instructions: [dynamic]Instruction,
    entry_point: u64,
    memory: []byte,
    registers: [Register]u64,
    persistent_storage_begin: u64,
    persistent_storage_watermark: int,

    label_mapping: map[string]u64,
    label_mapping_from_ip: map[u64]string,
}

Register :: enum {
    rsp, rfp, rip, ra, rt,
    rz,
    r1, r2, r3, r4,
    r5, r6, r7, r8
}

Instruction :: union {
    PUSH,
    POP,

    MOV,
    MOVI,

    ADD,
    ADDI,
    FADD,
    FADDI,

    SUB,
    FSUB,

    MUL,
    FMUL,

    SDIV,
    UDIV,
    FDIV,

    EQ,
    NEQ,
    LT,
    LTE,

    GOTO,
    GOTO_IP,
    GOTOIF,
    GOTOIF_IP,
    GOTOIFZ,
    GOTOIFZ_IP,
    JUMP,
    JUMP_IP,
    JUMPIF,
    JUMPIF_IP,
    JUMPIFZ,
    JUMPIFZ_IP,

    LOAD8,
    LOAD16,
    LOAD32,
    LOAD64,
    STORE8,
    STORE16,
    STORE32,
    STORE64,

    EXIT,
    TRAP,

    PRINT_INT,

    PRINT_REG,
}

PUSH :: struct {
    p1: Register,
}
POP :: struct {
    dst: Register,
}

MOV :: struct {
    dst, src: Register,
}
MOVI :: struct {
    dst: Register,
    imm: i64,
}

ADD :: struct {
    dst, p1, p2: Register,
}
FADD :: struct {
    dst, p1, p2: Register,
}
ADDI :: struct {
    dst, p1: Register,
    imm: i64,
}
FADDI :: struct {
    dst, p1: Register,
    imm: f64,
}
SUB :: struct {
    dst, p1, p2: Register,
}
FSUB :: struct {
    dst, p1, p2: Register,
}
MUL :: struct {
    dst, p1, p2: Register,
}
FMUL :: struct {
    dst, p1, p2: Register,
}
SDIV :: struct {
    dst, p1, p2: Register,
}
UDIV :: struct {
    dst, p1, p2: Register,
}
FDIV :: struct {
    dst, p1, p2: Register,
}

EQ :: struct {
    dst, p1, p2: Register,
}
NEQ :: struct {
    dst, p1, p2: Register,
}
LT :: struct {
    dst, p1, p2: Register,
}
LTE :: struct {
    dst, p1, p2: Register,
}

GOTO :: struct {
    label: string,
}
GOTO_IP :: struct {
    ip: u64,
}
GOTOIF :: struct {
    p1: Register,
    label: string,
}
GOTOIF_IP :: struct {
    p1: Register,
    ip: u64,
}
GOTOIFZ :: struct {
    p1: Register,
    label: string,
}
GOTOIFZ_IP :: struct {
    p1: Register,
    ip: u64,
}

JUMP :: struct {
    label: string,
}
JUMP_IP :: struct {
    ip: u64,
}
JUMPIF :: struct {
    p1: Register,
    label: string,
}
JUMPIF_IP :: struct {
    p1: Register,
    ip: u64,
}
JUMPIFZ :: struct {
    p1: Register,
    label: string,
}
JUMPIFZ_IP :: struct {
    p1: Register,
    ip: u64,
}

LOAD8   :: struct { dst, p1: Register, }
LOAD16  :: struct { dst, p1: Register, }
LOAD32  :: struct { dst, p1: Register, }
LOAD64  :: struct { dst, p1: Register, }
STORE8  :: struct { dst, p1: Register, }
STORE16 :: struct { dst, p1: Register, }
STORE32 :: struct { dst, p1: Register, }
STORE64 :: struct { dst, p1: Register, }

EXIT :: struct {

}



// Intrinsics

TRAP :: struct {

}

PRINT_INT :: struct {
    p1: Register,
}



PRINT_REG :: struct {
    p1: Register,
}

// division requires signed instructions

test_vm :: proc() {
    vm := make_vm();

    /*
    int factorial(int n) {
        if (n != 1) {
            return n * factorial(n-1);
        }
        return 1;
    }
    */

    {
        assert(false);
        // function_header(vm, "main");

        // save our things
        add_instruction(vm, PUSH{.rfp});
        add_instruction(vm, PUSH{.ra});

        // push a parameter
        add_instruction(vm, MOVI{.r1, 6});
        add_instruction(vm, PUSH{.r1});

        // call square
        call(vm, "factorial");

        // pop return value
        add_instruction(vm, POP{.r1});

        // pop saved registers
        add_instruction(vm, POP{.ra});
        add_instruction(vm, POP{.rfp});

        add_instruction(vm, PRINT_REG{.r1});

        // exit
        add_instruction(vm, EXIT{});
    }

    {
        assert(false);
        // function_header(vm, "factorial");

        add_instruction(vm, POP{.r1});           // pop param

        // if (n != 1)
        add_instruction(vm, MOVI{.r2, 1});
        add_instruction(vm, EQ{.r3, .r1, .r2});
        add_instruction(vm, GOTOIF{.r3, "base_case"});

        // n-1
        add_instruction(vm, ADDI{.r2, .r1, -1});

        // factorial()
        add_instruction(vm, PUSH{.r1});  // save our r1
        add_instruction(vm, PUSH{.rfp}); // save rfp and ra
        add_instruction(vm, PUSH{.ra});

        // push param
        add_instruction(vm, PUSH{.r2});
        call(vm, "factorial");

        add_instruction(vm, POP{.r2});
        add_instruction(vm, POP{.ra});
        add_instruction(vm, POP{.rfp});
        add_instruction(vm, POP{.r1});

        add_instruction(vm, MUL{.r1, .r1, .r2});
        add_instruction(vm, PUSH{.r1});          // push it as return value

        ret(vm);

        label(vm, "base_case");
        add_instruction(vm, PUSH{.r1});          // push it as return value
        ret(vm);
    }

    execute_vm(vm);
}

call :: proc(vm: ^VM, label: string) {
    add_instruction(vm, JUMP{label});
}

ret :: proc(vm: ^VM) {
    add_instruction(vm, MOV{.rip, .ra});
}

make_vm :: proc() -> ^VM {
    vm := new(VM);
    vm.memory = make([]byte, mem.megabytes(10));
    vm.persistent_storage_begin = transmute(u64)mem.megabytes(1);
    vm.registers[.rsp] = vm.persistent_storage_begin;
    vm.persistent_storage_watermark = cast(int)vm.persistent_storage_begin;
    return vm;
}

add_instruction :: proc(vm: ^VM, instruction: Instruction) {
    append(&vm.instructions, instruction);
}

label :: proc(vm: ^VM, name: string) {
    name := strings.clone(name);
    ip := cast(u64)len(vm.instructions);
    vm.label_mapping[name] = ip;
    vm.label_mapping_from_ip[ip] = name;
}

vm_allocate_static_storage :: proc(vm: ^VM, size: int) -> int {
    // todo(josh): make sure that the stack never writes to the place it starts at
    offset := vm.persistent_storage_watermark;
    offset = align_forward_int(offset, size_of(rawptr)*2); // todo(josh): real alignment
    vm.persistent_storage_watermark = offset + size;
    return offset;
}

execute_vm :: proc(vm: ^VM) {
    global_storage_start_index := vm_allocate_static_storage(vm, 4);
    vm.memory[global_storage_start_index] = 149;

    for instruction, idx in vm.instructions {
        // if cast(u64)idx in vm.label_mapping_from_ip {
        //     fmt.printf("%s:\n", vm.label_mapping_from_ip[cast(u64)idx]);
        // }
        // fmt.println("    ", vm.instructions[idx]);

        #partial
        switch kind in instruction {
            case GOTO:    ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = GOTO_IP{ip};
            case GOTOIF:  ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = GOTOIF_IP{kind.p1, ip};
            case GOTOIFZ: ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = GOTOIFZ_IP{kind.p1, ip};
            case JUMP:    ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = JUMP_IP{ip};
            case JUMPIF:  ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = JUMPIF_IP{kind.p1, ip};
            case JUMPIFZ: ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = JUMPIFZ_IP{kind.p1, ip};
        }
    }

    // fmt.println("-----------------------------------------");

    vm.registers[.rip] = vm.entry_point;
    instruction_loop:
    for vm.registers[.rip] < cast(u64)len(vm.instructions) {
        instruction := vm.instructions[vm.registers[.rip]];
        switch kind in instruction {
            case LOAD8:  vm.registers[kind.dst] = cast(u64)(cast(^u8 )&vm.memory[vm.registers[kind.p1]])^;
            case LOAD16: vm.registers[kind.dst] = cast(u64)(cast(^u16)&vm.memory[vm.registers[kind.p1]])^;
            case LOAD32: vm.registers[kind.dst] = cast(u64)(cast(^u32)&vm.memory[vm.registers[kind.p1]])^;
            case LOAD64: vm.registers[kind.dst] = cast(u64)(cast(^u64)&vm.memory[vm.registers[kind.p1]])^;
            case STORE8:  (cast(^u8 )&vm.memory[vm.registers[kind.dst]])^ = cast(u8 )vm.registers[kind.p1];
            case STORE16: (cast(^u16)&vm.memory[vm.registers[kind.dst]])^ = cast(u16)vm.registers[kind.p1];
            case STORE32: (cast(^u32)&vm.memory[vm.registers[kind.dst]])^ = cast(u32)vm.registers[kind.p1];
            case STORE64: (cast(^u64)&vm.memory[vm.registers[kind.dst]])^ = cast(u64)vm.registers[kind.p1];

            case PUSH: vm.registers[.rsp] -= 8; (cast(^u64)&vm.memory[vm.registers[.rsp]])^ = vm.registers[kind.p1];
            case POP:  vm.registers[kind.dst] = (cast(^u64)&vm.memory[vm.registers[.rsp]])^; mem.zero(&vm.memory[vm.registers[.rsp]], 8); vm.registers[.rsp] += 8;

            case MOV:  vm.registers[kind.dst] = vm.registers[kind.src];
            case MOVI: vm.registers[kind.dst] = transmute(u64)kind.imm;

            case ADD:   vm.registers[kind.dst] = vm.registers[kind.p1] + vm.registers[kind.p2];
            case ADDI:  vm.registers[kind.dst] = vm.registers[kind.p1] + transmute(u64)kind.imm;
            case FADD:  vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] + transmute(f64)vm.registers[kind.p2]);
            case FADDI: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] + kind.imm);

            case SUB:  vm.registers[kind.dst] = vm.registers[kind.p1] - vm.registers[kind.p2];
            case FSUB: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] - transmute(f64)vm.registers[kind.p2]);

            case MUL:  vm.registers[kind.dst] = vm.registers[kind.p1] * vm.registers[kind.p2];
            case FMUL: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] * transmute(f64)vm.registers[kind.p2]);

            case SDIV: vm.registers[kind.dst] = transmute(u64)(transmute(i64)vm.registers[kind.p1] / transmute(i64)vm.registers[kind.p2]);
            case UDIV: vm.registers[kind.dst] = vm.registers[kind.p1] / vm.registers[kind.p2];
            case FDIV: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] / transmute(f64)vm.registers[kind.p2]);

            case EQ:  vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] == vm.registers[kind.p2]);
            case NEQ: vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] != vm.registers[kind.p2]);
            case LT:  vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] <  vm.registers[kind.p2]);
            case LTE: vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] <= vm.registers[kind.p2]);

            case GOTO_IP:                                            vm.registers[.rip] = kind.ip-1;                                  // note(josh): depends on `rip += 1` being after the switch
            case GOTOIF_IP:                                          if vm.registers[kind.p1] != 0 do vm.registers[.rip] = kind.ip-1; // note(josh): depends on `rip += 1` being after the switch
            case GOTOIFZ_IP:                                         if vm.registers[kind.p1] == 0 do vm.registers[.rip] = kind.ip-1; // note(josh): depends on `rip += 1` being after the switch
            case JUMP_IP:    vm.registers[.ra] = vm.registers[.rip]; vm.registers[.rip] = kind.ip-1;                                  // note(josh): depends on `rip += 1` being after the switch
            case JUMPIF_IP:  vm.registers[.ra] = vm.registers[.rip]; if vm.registers[kind.p1] != 0 do vm.registers[.rip] = kind.ip-1; // note(josh): depends on `rip += 1` being after the switch
            case JUMPIFZ_IP: vm.registers[.ra] = vm.registers[.rip]; if vm.registers[kind.p1] == 0 do vm.registers[.rip] = kind.ip-1; // note(josh): depends on `rip += 1` being after the switch

            case GOTO:    panic("didn't remap goto");
            case GOTOIF:  panic("didn't remap gotoif");
            case GOTOIFZ: panic("didn't remap gotoifz");
            case JUMP:    panic("didn't remap jump");
            case JUMPIF:  panic("didn't remap jumpif");
            case JUMPIFZ: panic("didn't remap jumpifz");

            case EXIT: break instruction_loop;
            case TRAP: fmt.println("Crash!!!"); break instruction_loop;
            case PRINT_INT: fmt.println(transmute(i64)vm.registers[kind.p1]);

            case PRINT_REG: fmt.println("REGISTER", kind.p1, "=", vm.registers[kind.p1]);
            case: panic(tprint(kind));
        }

        // fmt.printf("| %d | %d | %d | %d |\n", vm.registers[.r1], vm.registers[.r2], vm.registers[.r3], vm.registers[.r4]);

        // for idx := vm.persistent_storage_begin; idx >= vm.registers[.rsp]-4; idx -= 1 {
        //     fmt.printf("| %d ", vm.memory[idx]);
        // }
        // fmt.printf("\n");

        vm.registers[.rip] += 1;
        vm.registers[.rz] = 0;
    }
}



is_power_of_two :: inline proc(x: uintptr) -> bool {
    if x <= 0 do return false;
    return (x & (x-1)) == 0;
}

align_forward :: inline proc(ptr: rawptr, align: uintptr) -> rawptr {
    return rawptr(align_forward_uintptr(uintptr(ptr), align));
}

align_forward_uintptr :: proc(ptr, align: uintptr) -> uintptr {
    assert(is_power_of_two(align));

    p := ptr;
    modulo := p & (align-1);
    if modulo != 0 do p += align - modulo;
    return p;
}

align_forward_int :: inline proc(ptr, align: int) -> int {
    return int(align_forward_uintptr(uintptr(ptr), uintptr(align)));
}
align_forward_uint :: inline proc(ptr, align: uint) -> uint {
    return uint(align_forward_uintptr(uintptr(ptr), uintptr(align)));
}