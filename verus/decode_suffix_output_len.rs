use vstd::prelude::*;

verus! {

pub open spec fn suffix_output_len(morsels: int) -> int {
    morsels * 6 / 8
}

/// Mirrors the arithmetic expression used for `leftover_bytes_to_append` in
/// `src/engine/general_purpose/decode_suffix.rs`.
pub fn suffix_output_len_exec(morsels: usize) -> (result: usize)
    requires
        morsels <= 4,
    ensures
        result as int == suffix_output_len(morsels as int),
{
    morsels * 6 / 8
}

pub proof fn accepted_suffix_output_len(morsels: int)
    requires
        morsels == 0 || (2 <= morsels && morsels <= 4),
    ensures
        suffix_output_len(morsels) == if morsels == 0 { 0 } else { morsels - 1 },
        0 <= suffix_output_len(morsels) && suffix_output_len(morsels) <= 3,
{
    if morsels == 0 {
        assert(suffix_output_len(morsels) == 0);
    } else if morsels == 2 {
        assert(suffix_output_len(morsels) == 1);
    } else if morsels == 3 {
        assert(suffix_output_len(morsels) == 2);
    } else {
        assert(morsels == 4);
        assert(suffix_output_len(morsels) == 3);
    }
}

pub proof fn canonical_nonempty_suffix_shape(morsels: int, padding: int)
    requires
        2 <= morsels && morsels <= 4,
        0 <= padding && padding <= 2,
        morsels + padding <= 4,
        (morsels + padding) % 4 == 0,
    ensures
        (morsels == 2 && padding == 2)
            || (morsels == 3 && padding == 1)
            || (morsels == 4 && padding == 0),
{
    assert(0 < morsels + padding);
    assert(morsels + padding == 4);
    if morsels == 2 {
        assert(padding == 2);
    } else if morsels == 3 {
        assert(padding == 1);
    } else {
        assert(morsels == 4);
        assert(padding == 0);
    }
}

}

fn main() {}
