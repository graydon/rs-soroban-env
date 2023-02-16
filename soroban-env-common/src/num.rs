use crate::raw_val::TAG_BITS;
pub use ethnum::{AsI256, AsU256, I256, U256};

use crate::declare_tag_based_wrapper;

declare_tag_based_wrapper!(U64Small);
declare_tag_based_wrapper!(I64Small);
declare_tag_based_wrapper!(TimepointSmall);
declare_tag_based_wrapper!(DurationSmall);

declare_tag_based_wrapper!(U128Small);
declare_tag_based_wrapper!(I128Small);
declare_tag_based_wrapper!(U256Small);
declare_tag_based_wrapper!(I256Small);

declare_tag_based_wrapper!(U64Object);
declare_tag_based_wrapper!(I64Object);
declare_tag_based_wrapper!(TimepointObject);
declare_tag_based_wrapper!(DurationObject);

declare_tag_based_wrapper!(U128Object);
declare_tag_based_wrapper!(I128Object);
declare_tag_based_wrapper!(U256Object);
declare_tag_based_wrapper!(I256Object);

pub const fn is_small_u64(u: u64) -> bool {
    u == ((u << TAG_BITS) >> TAG_BITS)
}

pub const fn is_small_i64(i: i64) -> bool {
    i == ((i << TAG_BITS) >> TAG_BITS)
}

pub fn is_small_u128(u: u128) -> bool {
    let word = u as u64;
    is_small_u64(word) && u == (word as u128)
}

pub fn is_small_i128(i: i128) -> bool {
    let word = i as i64;
    is_small_i64(word) && i == (word as i128)
}

pub fn is_small_u256(u: &U256) -> bool {
    let word = u.as_u64();
    is_small_u64(word) && *u == U256::from(word)
}

pub fn is_small_i256(i: &I256) -> bool {
    let word = i.as_i64();
    is_small_i64(word) && *i == I256::from(word)
}

#[test]
fn test_small_ints() {
    assert!(!is_small_i64(0xff7f_ffff_ffff_ffff_u64 as i64));
    assert!(is_small_i64(0xff80_0000_0000_0000_u64 as i64));
    assert!(is_small_i64(0x007f_ffff_ffff_ffff_u64 as i64));
    assert!(!is_small_i64(0x0080_0000_0000_0000_u64 as i64));

    assert!(is_small_u64(0x00ff_ffff_ffff_ffff_u64));
    assert!(!is_small_u64(0x0100_0000_0000_0000_u64));
}
