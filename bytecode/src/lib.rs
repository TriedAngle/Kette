mod op;
mod instruction;
mod builder;
mod decoder;

pub use op::Op;
pub use instruction::Instruction;
pub use builder::{BytecodeBuilder, Label};
pub use decoder::BytecodeDecoder;

#[cfg(test)]
mod tests {
    use super::*;

    fn decode_all(bytes: &[u8]) -> Vec<Instruction> {
        BytecodeDecoder::new(bytes).collect()
    }

    #[test]
    fn round_trip_narrow() {
        let mut b = BytecodeBuilder::new();
        b.load_constant(42);
        b.load_local(5);
        b.store_local(10);
        b.send(100, 3, 2, 500);
        b.create_object(7, 1);
        b.create_block(99);
        b.load_stack(0xDEAD_BEEF);
        b.store_stack(0xCAFE_BABE);
        b.load_temp(10, 20);
        b.store_temp(30, 40);
        b.load_assoc(55);
        b.store_assoc(66);
        b.local_return();
        b.return_();

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadConstant { idx: 42 },
            Instruction::LoadLocal { reg: 5 },
            Instruction::StoreLocal { reg: 10 },
            Instruction::Send { message_idx: 100, reg: 3, argc: 2, feedback_idx: 500 },
            Instruction::CreateObject { map_idx: 7, values_reg: 1 },
            Instruction::CreateBlock { block_idx: 99 },
            Instruction::LoadStack { offset: 0xDEAD_BEEF },
            Instruction::StoreStack { offset: 0xCAFE_BABE },
            Instruction::LoadTemp { array_idx: 10, idx: 20 },
            Instruction::StoreTemp { array_idx: 30, idx: 40 },
            Instruction::LoadAssoc { idx: 55 },
            Instruction::StoreAssoc { idx: 66 },
            Instruction::LocalReturn,
            Instruction::Return,
        ]);
    }

    #[test]
    fn round_trip_wide() {
        let mut b = BytecodeBuilder::new();
        b.load_local(300);
        b.store_local(1000);
        b.send(1, 500, 4, 2);
        b.create_object(0, 400);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadLocal { reg: 300 },
            Instruction::StoreLocal { reg: 1000 },
            Instruction::Send { message_idx: 1, reg: 500, argc: 4, feedback_idx: 2 },
            Instruction::CreateObject { map_idx: 0, values_reg: 400 },
        ]);
    }

    #[test]
    fn forward_jump() {
        let mut b = BytecodeBuilder::new();
        b.load_constant(0);
        let label = b.jump_if_false();
        b.load_constant(1);
        b.bind(label);
        b.local_return();

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadConstant { idx: 0 },
            Instruction::JumpIfFalse { offset: 3 },
            Instruction::LoadConstant { idx: 1 },
            Instruction::LocalReturn,
        ]);
    }

    #[test]
    fn backward_jump() {
        let mut b = BytecodeBuilder::new();
        let loop_top = b.current_offset();
        b.load_local(0);
        b.jump_back(loop_top);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadLocal { reg: 0 },
            Instruction::Jump { offset: -5 },
        ]);
    }

    #[test]
    fn display_instructions() {
        assert_eq!(
            Instruction::Send { message_idx: 5, reg: 3, argc: 2, feedback_idx: 10 }.to_string(),
            "Send #5 r3 2 ~10"
        );
        assert_eq!(
            Instruction::Jump { offset: -7 }.to_string(),
            "Jump -7"
        );
        assert_eq!(
            Instruction::LoadTemp { array_idx: 1, idx: 2 }.to_string(),
            "LoadTemp #1[2]"
        );
    }

    #[test]
    fn mov_round_trip_narrow() {
        let mut b = BytecodeBuilder::new();
        b.mov(3, 7);
        b.mov_to_stack(0x1000, 5);
        b.mov_from_stack(10, 0x2000);
        b.mov_to_temp(1, 2, 8);
        b.mov_from_temp(9, 3, 4);
        b.mov_to_assoc(50, 12);
        b.mov_from_assoc(15, 60);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::Mov { dst: 3, src: 7 },
            Instruction::MovToStack { offset: 0x1000, src: 5 },
            Instruction::MovFromStack { dst: 10, offset: 0x2000 },
            Instruction::MovToTemp { array_idx: 1, idx: 2, src: 8 },
            Instruction::MovFromTemp { dst: 9, array_idx: 3, idx: 4 },
            Instruction::MovToAssoc { idx: 50, src: 12 },
            Instruction::MovFromAssoc { dst: 15, idx: 60 },
        ]);
    }

    #[test]
    fn mov_round_trip_wide() {
        let mut b = BytecodeBuilder::new();
        b.mov(300, 5);
        b.mov(2, 400);
        b.mov_to_stack(0x10, 500);
        b.mov_from_stack(600, 0x20);
        b.mov_to_temp(1, 2, 700);
        b.mov_from_temp(800, 3, 4);
        b.mov_to_assoc(10, 900);
        b.mov_from_assoc(1000, 20);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::Mov { dst: 300, src: 5 },
            Instruction::Mov { dst: 2, src: 400 },
            Instruction::MovToStack { offset: 0x10, src: 500 },
            Instruction::MovFromStack { dst: 600, offset: 0x20 },
            Instruction::MovToTemp { array_idx: 1, idx: 2, src: 700 },
            Instruction::MovFromTemp { dst: 800, array_idx: 3, idx: 4 },
            Instruction::MovToAssoc { idx: 10, src: 900 },
            Instruction::MovFromAssoc { dst: 1000, idx: 20 },
        ]);
    }

    #[test]
    fn mov_display() {
        assert_eq!(
            Instruction::Mov { dst: 1, src: 2 }.to_string(),
            "Mov r1, r2"
        );
        assert_eq!(
            Instruction::MovToTemp { array_idx: 5, idx: 3, src: 7 }.to_string(),
            "MovToTemp #5[3], r7"
        );
        assert_eq!(
            Instruction::MovFromAssoc { dst: 4, idx: 10 }.to_string(),
            "MovFromAssoc r4, #10"
        );
    }

    #[test]
    fn mov_narrow_size() {
        let mut b = BytecodeBuilder::new();
        b.mov(1, 2);
        assert_eq!(b.as_bytes().len(), 3);
    }

    #[test]
    fn mov_wide_size() {
        let mut b = BytecodeBuilder::new();
        b.mov(256, 2);
        assert_eq!(b.as_bytes().len(), 6);
    }

    #[test]
    fn load_smi_8bit() {
        let mut b = BytecodeBuilder::new();
        b.load_smi(0);
        b.load_smi(127);
        b.load_smi(-128);
        b.load_smi(-1);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadSmi { value: 0 },
            Instruction::LoadSmi { value: 127 },
            Instruction::LoadSmi { value: -128 },
            Instruction::LoadSmi { value: -1 },
        ]);
    }

    #[test]
    fn load_smi_8bit_size() {
        let mut b = BytecodeBuilder::new();
        b.load_smi(42);
        assert_eq!(b.as_bytes().len(), 2);
        assert_eq!(b.as_bytes()[0], Op::LoadSmi as u8);
    }

    #[test]
    fn load_smi_16bit() {
        let mut b = BytecodeBuilder::new();
        b.load_smi(128);
        b.load_smi(-129);
        b.load_smi(32767);
        b.load_smi(-32768);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadSmi { value: 128 },
            Instruction::LoadSmi { value: -129 },
            Instruction::LoadSmi { value: 32767 },
            Instruction::LoadSmi { value: -32768 },
        ]);
    }

    #[test]
    fn load_smi_16bit_size() {
        let mut b = BytecodeBuilder::new();
        b.load_smi(1000);
        assert_eq!(b.as_bytes().len(), 4);
        assert_eq!(b.as_bytes()[0], Op::Wide as u8);
        assert_eq!(b.as_bytes()[1], Op::LoadSmi as u8);
    }

    #[test]
    fn load_smi_32bit() {
        let mut b = BytecodeBuilder::new();
        b.load_smi(32768);
        b.load_smi(-32769);
        b.load_smi(i32::MAX);
        b.load_smi(i32::MIN);

        assert_eq!(decode_all(&b.into_bytes()), vec![
            Instruction::LoadSmi { value: 32768 },
            Instruction::LoadSmi { value: -32769 },
            Instruction::LoadSmi { value: i32::MAX },
            Instruction::LoadSmi { value: i32::MIN },
        ]);
    }

    #[test]
    fn load_smi_32bit_size() {
        let mut b = BytecodeBuilder::new();
        b.load_smi(100_000);
        assert_eq!(b.as_bytes().len(), 6);
        assert_eq!(b.as_bytes()[0], Op::ExtraWide as u8);
        assert_eq!(b.as_bytes()[1], Op::LoadSmi as u8);
    }

    #[test]
    fn load_smi_display() {
        assert_eq!(Instruction::LoadSmi { value: 42 }.to_string(), "LoadSmi 42");
        assert_eq!(Instruction::LoadSmi { value: -1 }.to_string(), "LoadSmi -1");
    }

    #[test]
    fn narrow_has_no_wide_prefix() {
        let mut b = BytecodeBuilder::new();
        b.load_local(255);
        let bytes = b.into_bytes();
        assert_eq!(bytes.len(), 2);
        assert_eq!(bytes[0], Op::LoadLocal as u8);
    }

    #[test]
    fn wide_has_prefix() {
        let mut b = BytecodeBuilder::new();
        b.load_local(256);
        let bytes = b.into_bytes();
        assert_eq!(bytes.len(), 4);
        assert_eq!(bytes[0], Op::Wide as u8);
        assert_eq!(bytes[1], Op::LoadLocal as u8);
    }
}
