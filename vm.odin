package main

import "core:fmt"

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