/* --------------------------- Data Representation -------------------------- */

#[repr(C)]
#[derive(PartialEq, Eq, Copy, Clone)]
pub struct SnakeValue(pub u64);

#[repr(C)]
pub struct SnakeArray {
    pub size: u64,
    pub elts: *mut SnakeValue,
}

/* Casts a pointer to an array of more convenient interface
 *
**/
pub fn load_snake_array(p: *const u64) -> SnakeArray {
    unsafe {
        let size = *p;
        SnakeArray { size, elts: std::mem::transmute(p.add(1)) }
    }
}

pub const INT_MASK: u64 = 0b01;
pub const FULL_MASK: u64 = 0b11;
pub const INT_TAG: u64 = 0b00;
pub const BOOL_TAG: u64 = 0b01;
pub const ARRAY_TAG: u64 = 0b11;
pub const SNAKE_TRU: SnakeValue = SnakeValue(0b101);
pub const SNAKE_FLS: SnakeValue = SnakeValue(0b001);

// reinterprets the bytes of an unsigned number to a signed number
pub fn unsigned_to_signed(x: u64) -> i64 {
    i64::from_le_bytes(x.to_le_bytes())
}

pub fn signed_to_unsigned(x: i64) -> u64 {
    u64::from_le_bytes(x.to_le_bytes())
}
