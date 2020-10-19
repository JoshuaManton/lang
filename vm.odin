package main

import "core:fmt"
import "core:mem"
import "core:strings"

// todo(josh): graphical debugger

VM_DEBUG_PRINT :: true;
VM_TOTAL_MEMORY :: 16 * 1024 * 1024; // 16 megabytes
VM_STACK_SIZE   ::  2 * 1024 * 1024; // 2 megabytes
VM_GLOBAL_STORAGE_BEGIN :: VM_STACK_SIZE;
VM :: struct {
    instructions: [dynamic]Instruction,
    entry_point: u64,
    memory: []byte,
    registers: [Register]u64,

    label_mapping: map[string]u64,
    label_mapping_from_ip: map[u64]string,

    ip_to_comment_mapping: map[u64][dynamic]string,
}

Register :: enum {
    rsp, rfp, rip, ra, rt,
    rz,
    r1, r2, r3, r4,
    r5, r6, r7, r8
}

Instruction :: union {
    LOAD8,
    LOAD16,
    LOAD32,
    LOAD64,
    STORE8,
    STORE16,
    STORE32,
    STORE64,

    PUSH,
    POP,

    MOV,
    MOVI,
    MOVIF,

    ADD,
    ADDI,
    ADDF,
    ADDIF,

    SUB,
    SUBF,

    MUL,
    MULF,

    DIVS,
    DIVU,
    DIVF,

    MOD,
    MODMOD,

    SHL,
    SHR,

    BWOR,
    BWAND,
    BWXOR,
    BWNOT,

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

    COPY,

    EXIT,
    TRAP,

    PRINT_INT,
    PRINT_FLOAT,

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
MOVIF :: struct {
    dst: Register,
    imm: f64,
}

ADD  :: struct { dst, p1, p2: Register, }
ADDF :: struct { dst, p1, p2: Register, }
ADDI :: struct {
    dst, p1: Register,
    imm: i64,
}
ADDIF :: struct {
    dst, p1: Register,
    imm: f64,
}
SUB  :: struct { dst, p1, p2: Register, }
SUBF :: struct { dst, p1, p2: Register, }
MUL  :: struct { dst, p1, p2: Register, }
MULF :: struct { dst, p1, p2: Register, }
DIVS :: struct { dst, p1, p2: Register, }
DIVU :: struct { dst, p1, p2: Register, }
DIVF :: struct { dst, p1, p2: Register, }

MOD    :: struct { dst, p1, p2: Register, }
MODMOD :: struct { dst, p1, p2: Register, }

SHL :: struct { dst, p1, p2: Register, }
SHR :: struct { dst, p1, p2: Register, }

BWOR  :: struct { dst, p1, p2: Register, }
BWAND :: struct { dst, p1, p2: Register, }
BWXOR :: struct { dst, p1, p2: Register, }
BWNOT :: struct { dst, p1: Register, }

EQ  :: struct { dst, p1, p2: Register, }
NEQ :: struct { dst, p1, p2: Register, }
LT  :: struct { dst, p1, p2: Register, }
LTE :: struct { dst, p1, p2: Register, }

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

COPY :: struct {
    dst: Register,
    src: Register,
    size: Register,
}

EXIT :: struct {

}



// Intrinsics

TRAP :: struct {

}

PRINT_INT   :: struct { p1: Register, }
PRINT_FLOAT :: struct { p1: Register, }



PRINT_REG :: struct {
    p1: Register,
}

call :: proc(vm: ^VM, label: string) {
    add_instruction(vm, JUMP{label});
}

ret :: proc(vm: ^VM) {
    add_instruction(vm, MOV{.rip, .ra});
}

make_vm :: proc() -> ^VM {
    vm := new(VM);
    vm.memory = make([]byte, VM_TOTAL_MEMORY);
    vm.registers[.rsp] = VM_GLOBAL_STORAGE_BEGIN;
    return vm;
}

add_instruction :: proc(vm: ^VM, instruction: Instruction) {
    append(&vm.instructions, instruction);
}

label :: proc(vm: ^VM, name: string) {
    name := strings.clone(name);
    ip := cast(u64)len(vm.instructions);
    assert(name not_in vm.label_mapping, "no duplicate label names");
    assert(ip not_in vm.label_mapping_from_ip, "not allowed multiple labels for same IP");
    vm.label_mapping[name] = ip;
    vm.label_mapping_from_ip[ip] = name;
}

vm_comment :: proc(vm: ^VM, comment: string) {
    ip := cast(u64)len(vm.instructions);
    if ip not_in vm.ip_to_comment_mapping {
        vm.ip_to_comment_mapping[ip] = {};
    }
    arr := &vm.ip_to_comment_mapping[ip];
    append(arr, comment);
}

vm_translate_global_storage_offset :: proc(offset: u64) -> u64 {
    return VM_GLOBAL_STORAGE_BEGIN + offset;
}

execute_vm :: proc(vm: ^VM) {
    for instruction, idx in vm.instructions {
        when VM_DEBUG_PRINT {
            if cast(u64)idx in vm.label_mapping_from_ip {
                fmt.printf("%s:\n", vm.label_mapping_from_ip[cast(u64)idx]);
            }
            if cast(u64)idx in vm.ip_to_comment_mapping {
                arr := vm.ip_to_comment_mapping[cast(u64)idx];
                for comment in arr {
                    fmt.printf("  ; %s\n", comment);
                }
            }
            switch kind in instruction {
                case PUSH:        fmt.printf("    push %v\n", kind.p1);
                case POP:         fmt.printf("    pop %v\n", kind.dst);
                case MOV:         fmt.printf("    mov %v %v\n", kind.dst, kind.src);
                case MOVI:        fmt.printf("    movi %v %v\n", kind.dst, kind.imm);
                case MOVIF:       fmt.printf("    movif %v %v\n", kind.dst, kind.imm);
                case ADD:         fmt.printf("    add %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case ADDI:        fmt.printf("    addi %v %v %v\n", kind.dst, kind.p1, kind.imm);
                case ADDF:        fmt.printf("    addf %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case ADDIF:       fmt.printf("    addif %v %v %v\n", kind.dst, kind.p1, kind.imm);
                case SUB:         fmt.printf("    sub %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case SUBF:        fmt.printf("    subf %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case MUL:         fmt.printf("    mul %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case MULF:        fmt.printf("    mulf %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case DIVS:        fmt.printf("    divs %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case DIVU:        fmt.printf("    divu %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case DIVF:        fmt.printf("    divf %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case MOD:         fmt.printf("    mod %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case MODMOD:      fmt.printf("    modmod %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case SHL:         fmt.printf("    shl %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case SHR:         fmt.printf("    shr %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case BWOR:        fmt.printf("    bwor %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case BWAND:       fmt.printf("    bwand %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case BWXOR:       fmt.printf("    bwxor %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case BWNOT:       fmt.printf("    bwnot %v %v\n", kind.dst, kind.p1);
                case EQ:          fmt.printf("    eq %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case NEQ:         fmt.printf("    neq %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case LT:          fmt.printf("    lt %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case LTE:         fmt.printf("    lte %v %v %v\n", kind.dst, kind.p1, kind.p2);
                case GOTO:        fmt.printf("    goto %v\n", kind.label);
                case GOTO_IP:     fmt.printf("    goto_ip %v\n", kind.ip);
                case GOTOIF:      fmt.printf("    gotoif %v %v\n", kind.p1, kind.label);
                case GOTOIF_IP:   fmt.printf("    gotoif_ip %v %v\n", kind.p1, kind.ip);
                case GOTOIFZ:     fmt.printf("    gotoifz %v %v\n", kind.p1, kind.label);
                case GOTOIFZ_IP:  fmt.printf("    gotoifz_ip %v %v\n", kind.p1, kind.ip);
                case JUMP:        fmt.printf("    jump %v\n", kind.label);
                case JUMP_IP:     fmt.printf("    jump_ip %v\n", kind.ip);
                case JUMPIF:      fmt.printf("    jumpif %v %v\n", kind.p1, kind.label);
                case JUMPIF_IP:   fmt.printf("    jumpif_ip %v %v\n", kind.p1, kind.ip);
                case JUMPIFZ:     fmt.printf("    jumpifz %v %v\n", kind.p1, kind.label);
                case JUMPIFZ_IP:  fmt.printf("    jumpifz_ip %v %v\n", kind.p1, kind.ip);
                case LOAD8:       fmt.printf("    load8 %v %v\n", kind.dst, kind.p1);
                case LOAD16:      fmt.printf("    load16 %v %v\n", kind.dst, kind.p1);
                case LOAD32:      fmt.printf("    load32 %v %v\n", kind.dst, kind.p1);
                case LOAD64:      fmt.printf("    load64 %v %v\n", kind.dst, kind.p1);
                case STORE8:      fmt.printf("    store8 %v %v\n", kind.dst, kind.p1);
                case STORE16:     fmt.printf("    store16 %v %v\n", kind.dst, kind.p1);
                case STORE32:     fmt.printf("    store32 %v %v\n", kind.dst, kind.p1);
                case STORE64:     fmt.printf("    store64 %v %v\n", kind.dst, kind.p1);
                case COPY:        fmt.printf("    copy %v %v %v\n", kind.dst, kind.src, kind.size);
                case EXIT:        fmt.printf("    exit\n");
                case TRAP:        fmt.printf("    trap\n");
                case PRINT_INT:   fmt.printf("    print_int %v\n", kind.p1);
                case PRINT_FLOAT: fmt.printf("    print_float %v\n", kind.p1);
                case PRINT_REG:   fmt.printf("    print_reg %v\n", kind.p1);
            }
        }

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

            case COPY: {
                length := vm.registers[kind.size];
                for i in 0..<length {
                    vm.memory[vm.registers[kind.dst]+i] = vm.memory[vm.registers[kind.src]+i];
                }
            }

            case PUSH: vm.registers[.rsp] -= 8; (cast(^u64)&vm.memory[vm.registers[.rsp]])^ = vm.registers[kind.p1];
            case POP:  vm.registers[kind.dst] = (cast(^u64)&vm.memory[vm.registers[.rsp]])^; mem.zero(&vm.memory[vm.registers[.rsp]], 8); vm.registers[.rsp] += 8;

            case MOV:   vm.registers[kind.dst] = vm.registers[kind.src];
            case MOVI:  vm.registers[kind.dst] = transmute(u64)kind.imm;
            case MOVIF: vm.registers[kind.dst] = transmute(u64)kind.imm;

            case ADD:   vm.registers[kind.dst] = vm.registers[kind.p1] + vm.registers[kind.p2];
            case ADDI:  vm.registers[kind.dst] = vm.registers[kind.p1] + transmute(u64)kind.imm;
            case ADDF:  vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] + transmute(f64)vm.registers[kind.p2]);
            case ADDIF: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] + kind.imm);

            case SUB:  vm.registers[kind.dst] = vm.registers[kind.p1] - vm.registers[kind.p2];
            case SUBF: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] - transmute(f64)vm.registers[kind.p2]);

            case MUL:  vm.registers[kind.dst] = vm.registers[kind.p1] * vm.registers[kind.p2];
            case MULF: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] * transmute(f64)vm.registers[kind.p2]);

            case DIVS: vm.registers[kind.dst] = transmute(u64)(transmute(i64)vm.registers[kind.p1] / transmute(i64)vm.registers[kind.p2]);
            case DIVU: vm.registers[kind.dst] = vm.registers[kind.p1] / vm.registers[kind.p2];
            case DIVF: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] / transmute(f64)vm.registers[kind.p2]);

            // todo(josh): test these extensively
            case MOD:    vm.registers[kind.dst] = vm.registers[kind.p1] %  vm.registers[kind.p2];
            case MODMOD: vm.registers[kind.dst] = vm.registers[kind.p1] %% vm.registers[kind.p2];

            case SHL: vm.registers[kind.dst] = vm.registers[kind.p1] << vm.registers[kind.p2];
            case SHR: vm.registers[kind.dst] = vm.registers[kind.p1] >> vm.registers[kind.p2];

            case BWOR:  vm.registers[kind.dst] = vm.registers[kind.p1] | vm.registers[kind.p2];
            case BWAND: vm.registers[kind.dst] = vm.registers[kind.p1] & vm.registers[kind.p2];
            case BWXOR: vm.registers[kind.dst] = vm.registers[kind.p1] ~ vm.registers[kind.p2];
            case BWNOT: vm.registers[kind.dst] = ~vm.registers[kind.p1];

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
            case PRINT_INT:   fmt.println(cast(i32)transmute(i64)vm.registers[kind.p1]);
            case PRINT_FLOAT: fmt.println(cast(f32)transmute(f64)vm.registers[kind.p1]);

            case PRINT_REG: fmt.println("REGISTER", kind.p1, "=", vm.registers[kind.p1]);
            case: panic(twrite(kind));
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