package main

import "core:fmt"
import "core:mem"
import "core:strings"

// todo(josh): graphical debugger

VM :: struct {
    instructions: [dynamic]Instruction,
    memory: []byte,
    registers: [Register]u64,
    data_segment: []byte,

    label_mapping: map[string]u64,
    label_mapping_from_ip: map[u64]string,
}

Register :: enum {
    rsp, rfp, rip, ra,
    rz,
    r1, r2, r3, r4,
    r5, r6, r7, r8
}

Instruction :: union {
    push,
    pop,

    mov,
    movi,

    add,
    addi,
    fadd,
    faddi,

    sub,
    fsub,

    mul,
    fmul,

    sdiv,
    udiv,
    fdiv,

    eq,
    lt,
    lte,

    goto,
    goto_ip,
    gotoif,
    gotoif_ip,
    jump,
    jump_ip,
    jumpif,
    jumpif_ip,

    load,
    store,

    exit,

    print_reg,
}

push :: struct {
    p1: Register,
}
pop :: struct {
    dst: Register,
}

mov :: struct {
    dst, src: Register,
}
movi :: struct {
    dst: Register,
    imm: int,
}

add :: struct {
    dst, p1, p2: Register,
}
fadd :: struct {
    dst, p1, p2: Register,
}
addi :: struct {
    dst, p1: Register,
    imm: int,
}
faddi :: struct {
    dst, p1: Register,
    imm: f64,
}
sub :: struct {
    dst, p1, p2: Register,
}
fsub :: struct {
    dst, p1, p2: Register,
}
mul :: struct {
    dst, p1, p2: Register,
}
fmul :: struct {
    dst, p1, p2: Register,
}
sdiv :: struct {
    dst, p1, p2: Register,
}
udiv :: struct {
    dst, p1, p2: Register,
}
fdiv :: struct {
    dst, p1, p2: Register,
}

eq :: struct {
    dst, p1, p2: Register,
}
lt :: struct {
    dst, p1, p2: Register,
}
lte :: struct {
    dst, p1, p2: Register,
}

goto :: struct {
    label: string,
}
goto_ip :: struct {
    ip: u64,
}
gotoif :: struct {
    p1: Register,
    label: string,
}
gotoif_ip :: struct {
    p1: Register,
    ip: u64,
}

jump :: struct {
    label: string,
}
jump_ip :: struct {
    ip: u64,
}
jumpif :: struct {
    p1: Register,
    label: string,
}
jumpif_ip :: struct {
    p1: Register,
    ip: u64,
}

load :: struct {
    dst, p1: Register,
}
store :: struct {
    dst, p1: Register,
}

exit :: struct {

}

print_reg :: struct {
    p1: Register,
}

// division requires signed instructions

test_vm :: proc() {
    vm := make_vm();

    /*
    label(vm, "main");
    {
        function_header(vm);

        // save our things
        add_instruction(vm, push{.rfp});
        add_instruction(vm, push{.ra});

        // push a parameter
        add_instruction(vm, movi{.r1, 6});
        add_instruction(vm, push{.r1});

        // call square
        call(vm, "square");

        // pop return value
        add_instruction(vm, pop{.r1});

        // pop saved registers
        add_instruction(vm, pop{.ra});
        add_instruction(vm, pop{.rfp});

        add_instruction(vm, print_reg{.r1});

        // exit
        add_instruction(vm, exit{});
    }

    label(vm, "square");
    {
        function_header(vm);

        add_instruction(vm, pop{.r5});           // pop param
        add_instruction(vm, mul{.r5, .r5, .r5}); // square it
        add_instruction(vm, print_reg{.r5});     // square it

        add_instruction(vm, push{.r5});          // push it as return value

        // return
        ret(vm);
    }
    */

    /*
    int factoria(int n) {
        if (n != 1) {
            return n * factorial(n-1);
        }
        return 1;
    }
    */

    label(vm, "main");
    {
        function_header(vm);

        // save our things
        add_instruction(vm, push{.rfp});
        add_instruction(vm, push{.ra});

        // push a parameter
        add_instruction(vm, movi{.r1, 6});
        add_instruction(vm, push{.r1});

        // call square
        call(vm, "factorial");

        // pop return value
        add_instruction(vm, pop{.r1});

        // pop saved registers
        add_instruction(vm, pop{.ra});
        add_instruction(vm, pop{.rfp});

        add_instruction(vm, print_reg{.r1});

        // exit
        add_instruction(vm, exit{});
    }

    label(vm, "factorial");
    {
        function_header(vm);

        add_instruction(vm, pop{.r1});           // pop param

        // if (n != 1)
        add_instruction(vm, movi{.r2, 1});
        add_instruction(vm, eq{.r3, .r1, .r2});
        add_instruction(vm, gotoif{.r3, "base_case"});

        // n-1
        add_instruction(vm, addi{.r2, .r1, -1});

        // factorial()
        add_instruction(vm, push{.r1});  // save our r1
        add_instruction(vm, push{.rfp}); // save rfp and ra
        add_instruction(vm, push{.ra});

        // push param
        add_instruction(vm, push{.r2});
        call(vm, "factorial");

        add_instruction(vm, pop{.r2});
        add_instruction(vm, pop{.ra});
        add_instruction(vm, pop{.rfp});
        add_instruction(vm, pop{.r1});

        add_instruction(vm, mul{.r1, .r1, .r2});
        add_instruction(vm, push{.r1});          // push it as return value

        ret(vm);

        label(vm, "base_case");
        add_instruction(vm, push{.r1});          // push it as return value
        ret(vm);
    }

    execute_vm(vm);
}

function_header :: proc(vm: ^VM) {
    add_instruction(vm, mov{.rfp, .rsp});
}

call :: proc(vm: ^VM, label: string) {
    add_instruction(vm, jump{label});
}

ret :: proc(vm: ^VM) {
    add_instruction(vm, mov{.rip, .ra});
}

make_vm :: proc() -> ^VM {
    vm := new(VM);
    vm.memory = make([]byte, mem.megabytes(10));
    vm.data_segment = make([]byte, mem.megabytes(5));
    vm.registers[.rsp] = transmute(u64)mem.megabytes(1);
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

execute_vm :: proc(vm: ^VM) {
    for instruction, idx in vm.instructions {
        if cast(u64)idx in vm.label_mapping_from_ip {
            fmt.printf("%s:\n", vm.label_mapping_from_ip[cast(u64)idx]);
        }
        fmt.println("    ", vm.instructions[idx]);

        #partial
        switch kind in instruction {
            case goto:   ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = goto_ip{ip};
            case gotoif: ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = gotoif_ip{kind.p1, ip};
            case jump:   ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = jump_ip{ip};
            case jumpif: ip, ok := vm.label_mapping[kind.label]; assert(ok, kind.label); vm.instructions[idx] = jumpif_ip{kind.p1, ip};
        }
    }

    instruction_loop:
    for vm.registers[.rip] < cast(u64)len(vm.instructions) {
        instruction := vm.instructions[vm.registers[.rip]];
        switch kind in instruction {
            case load:  vm.registers[kind.dst] = (cast(^u64)&vm.memory[vm.registers[kind.p1]])^;
            case store: (cast(^u64)&vm.memory[vm.registers[kind.dst]])^ = vm.registers[kind.p1];

            case push: (cast(^u64)&vm.memory[vm.registers[.rsp]])^ = vm.registers[kind.p1]; vm.registers[.rsp] -= 8;
            case pop:  vm.registers[.rsp] += 8; vm.registers[kind.dst] = (cast(^u64)&vm.memory[vm.registers[.rsp]])^; mem.zero(&vm.memory[vm.registers[.rsp]], 8);

            case mov:  vm.registers[kind.dst] = vm.registers[kind.src];
            case movi: vm.registers[kind.dst] = transmute(u64)kind.imm;

            case add:   vm.registers[kind.dst] = vm.registers[kind.p1] + vm.registers[kind.p2];
            case addi:  vm.registers[kind.dst] = vm.registers[kind.p1] + transmute(u64)kind.imm;
            case fadd:  vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] + transmute(f64)vm.registers[kind.p2]);
            case faddi: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] + kind.imm);

            case sub:  vm.registers[kind.dst] = vm.registers[kind.p1] - vm.registers[kind.p2];
            case fsub: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] - transmute(f64)vm.registers[kind.p2]);

            case mul:  vm.registers[kind.dst] = vm.registers[kind.p1] * vm.registers[kind.p2];
            case fmul: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] * transmute(f64)vm.registers[kind.p2]);

            case sdiv: vm.registers[kind.dst] = transmute(u64)(transmute(i64)vm.registers[kind.p1] / transmute(i64)vm.registers[kind.p2]);
            case udiv: vm.registers[kind.dst] = vm.registers[kind.p1] / vm.registers[kind.p2];
            case fdiv: vm.registers[kind.dst] = transmute(u64)(transmute(f64)vm.registers[kind.p1] / transmute(f64)vm.registers[kind.p2]);

            case eq:  vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] == vm.registers[kind.p2]);
            case lt:  vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] <  vm.registers[kind.p2]);
            case lte: vm.registers[kind.dst] = cast(u64)(vm.registers[kind.p1] <= vm.registers[kind.p2]);

            case goto_ip:                                           vm.registers[.rip] = kind.ip-1;                                  // note(josh): depends on `rip += 1` being after the switch
            case gotoif_ip:                                         if vm.registers[kind.p1] != 0 do vm.registers[.rip] = kind.ip-1; // note(josh): depends on `rip += 1` being after the switch
            case jump_ip:   vm.registers[.ra] = vm.registers[.rip]; vm.registers[.rip] = kind.ip-1;                                  // note(josh): depends on `rip += 1` being after the switch
            case jumpif_ip: vm.registers[.ra] = vm.registers[.rip]; if vm.registers[kind.p1] != 0 do vm.registers[.rip] = kind.ip-1; // note(josh): depends on `rip += 1` being after the switch

            case goto:   panic("didn't remap goto");
            case gotoif: panic("didn't remap gotoif");
            case jump:   panic("didn't remap jump");
            case jumpif: panic("didn't remap jumpif");

            case exit: break instruction_loop;

            case print_reg: fmt.println("REGISTER", kind.p1, "=", vm.registers[kind.p1]);
            case: panic(tprint(kind));
        }
        vm.registers[.rip] += 1;
        vm.registers[.rz] = 0;
    }
}
























/*

RZ :: 0;
RFP :: 1;
RSP :: 2;
RIP :: 3;
RDATA :: 4;
RUSER :: 5; // user-facing registers start here

STACK :: 0;
DATA :: 128;


VM :: struct {
    registers: [128]int,
    memory: [1024]byte,
    instructions: [dynamic]Instruction,
}

Instruction :: struct {
    kind: Instruction_Kind,
    p1, p2, p3: int,
}

Instruction_Kind :: enum {
    Move,              // reg_dst, reg_param
    Push,              // reg_param
    Pop,               // reg_dst
    Load,              // reg_dst, reg_ptr, imm_offset
    Load_Immediate,    // reg_dst, imm_param
    Store,             // reg_ptr, imm_offset, reg_param
    Add,               // reg_dst, reg_param1, reg_param2
    Add_Immediate,     // reg_dst, reg_param1
    Subtract,          // reg_dst, reg_param1, reg_param2
    Multiply,          // reg_dst, reg_param1, reg_param2
    Divide,            // reg_dst, reg_param1, reg_param2
    Jump_If_Zero,      // imm_jmp, reg_param
}

gen_vm :: proc(ir: IR_Result) -> ^VM {
    vm := new(VM);
    vm.registers[RDATA] = DATA;

    // todo(josh): generate data segment

    for procedure in ir.procedures {
        label_map: map[string]int;
        defer delete(label_map);

        inst(vm, .Push, RFP);
        inst(vm, .Move, RFP, RSP);
        if procedure.stack_frame_size > 0 {
            inst(vm, .Add_Immediate, RSP, procedure.stack_frame_size);
        }
        for stmt in procedure.statements {
            switch kind in stmt.kind {
                case IR_Load: {
                    switch storage in kind.storage.kind {
                        case Stack_Frame_Storage: inst(vm, .Load, user_reg(kind.dst.register), RFP, storage.offset);
                        case Global_Storage:      inst(vm, .Load, user_reg(kind.dst.register), RDATA, storage.offset);
                        case: unimplemented(fmt.tprint(kind));
                    }
                }
                case IR_Load_Immediate: inst(vm, .Load_Immediate, user_reg(kind.dst.register), kind.imm);
                case IR_Store: {
                    switch storage in kind.storage.kind {
                        case Stack_Frame_Storage: inst(vm, .Store, RFP,   storage.offset, user_reg(kind.value.register));
                        case Global_Storage:      inst(vm, .Store, RDATA, storage.offset, user_reg(kind.value.register));
                        case: unimplemented(fmt.tprint(kind));
                    }
                }
                case IR_Binop: {
                    #partial
                    switch kind.op {
                        case .Plus:     inst(vm, .Add,      user_reg(kind.dst.register), user_reg(kind.lhs.register), user_reg(kind.rhs.register));
                        case .Minus:    inst(vm, .Subtract, user_reg(kind.dst.register), user_reg(kind.lhs.register), user_reg(kind.rhs.register));
                        case .Multiply: inst(vm, .Multiply, user_reg(kind.dst.register), user_reg(kind.lhs.register), user_reg(kind.rhs.register));
                        case .Divide:   inst(vm, .Divide,   user_reg(kind.dst.register), user_reg(kind.lhs.register), user_reg(kind.rhs.register));
                        case: unimplemented(fmt.tprint(kind.op));
                    }
                }
                case IR_Unary: {
                    #partial
                    switch kind.op {
                        case: unimplemented(fmt.tprint(kind.op));
                    }
                }
                case: unimplemented(fmt.tprint(kind));
            }
        }
        inst(vm, .Pop, RFP);
    }

    for vm.registers[RIP] < len(vm.instructions) {
        using instruction := vm.instructions[vm.registers[RIP]];

        switch kind {
            case .Jump_If_Zero:   if vm.registers[p2] == 0 do vm.registers[RIP] = p1-1; // -1 because we increment RIP after every instruction
            case .Move:           vm.registers[p1] = vm.registers[p2];
            case .Push:           (cast(^int)&vm.memory[vm.registers[RSP]])^ = vm.registers[p1]; vm.registers[RSP] += size_of(int);
            case .Pop:            vm.registers[RSP] -= size_of(int); vm.registers[p1] = (cast(^int)&vm.memory[vm.registers[RSP]])^;
            case .Load:           vm.registers[p1] = (cast(^int)&vm.memory[vm.registers[p2] + p3])^;
            case .Load_Immediate: vm.registers[p1] = p2;
            case .Store:          (cast(^int)&vm.memory[vm.registers[p1] + p2])^ = vm.registers[p3];
            case .Add:            vm.registers[p1] = vm.registers[p2] + vm.registers[p3];
            case .Add_Immediate:  vm.registers[p1] += p2;
            case .Subtract:       vm.registers[p1] = vm.registers[p2] - vm.registers[p3];
            case .Multiply:       vm.registers[p1] = vm.registers[p2] * vm.registers[p3];
            case .Divide:         vm.registers[p1] = vm.registers[p2] / vm.registers[p3];
            case: unimplemented(fmt.tprint(kind));
        }

        vm.registers[RZ] = 0;
        vm.registers[RIP] += 1;
    }

    fmt.println(transmute([]int)vm.memory[:32]);
    fmt.println(transmute([]int)vm.memory[DATA:DATA+32]);
    fmt.println(vm.registers[:20]);

    return vm;
}

inst :: proc(vm: ^VM, k: Instruction_Kind, p1: int, p2: int = 0, p3: int = 0) {
    append(&vm.instructions, Instruction{k, p1, p2, p3});
}

user_reg :: proc(reg: int) -> int {
    return RUSER + reg;
}

*/