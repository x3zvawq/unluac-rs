use super::storage::{CompactSet, RegValueMap};
use crate::transformer::Reg;

#[test]
fn sparse_and_dense_reg_value_maps_compare_by_logical_contents() {
    let reg = Reg(3);
    let values = CompactSet::singleton(7_u32);

    let mut sparse = RegValueMap::sparse();
    sparse.insert(reg, values.clone());

    let mut dense = RegValueMap::with_reg_count(8);
    dense.insert(reg, values);

    assert_eq!(sparse, dense);
    assert_eq!(sparse.get(reg), dense.get(reg));
    assert_eq!(sparse.keys().collect::<Vec<_>>(), vec![reg]);
}
