use crate::lattices::{ConstLattice, VariableState};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HeapValue {
    HeapBase,
    GlobalsBase,

    // Lucet-specific values
    Bounded4GB,
    LucetTables,
    GuestTable0,

    // Wamr-specific values
    WamrExecEnv,        // the value pointed to by %rdi at the beginning of Wamr AOT functions
    WamrModuleInstance, // Wamr allocates one of these per module, which contains a pointer to linear memory
}

// Wamr-specific constants
pub const WAMR_MODULEINSTANCE_OFFSET: i64 = 0x10;   // the offset of the current ModuleInstance w/n a Wamr ExecEnv
pub const WAMR_HEAPBASE_OFFSET: i64 = 0x150;        // the offset of the linear memory region base w/n a Wamr ModuleInstance

pub type HeapValueLattice = ConstLattice<HeapValue>;

pub type HeapLattice = VariableState<HeapValueLattice>;

#[test]
fn heap_lattice_test() {
    use crate::lattices::reachingdefslattice::LocIdx;
    use crate::lattices::Lattice;

    let x1 = HeapValueLattice { v: None };
    let x2 = HeapValueLattice {
        v: Some(HeapValue::HeapBase),
    };
    let x3 = HeapValueLattice {
        v: Some(HeapValue::HeapBase),
    };
    let x4 = HeapValueLattice {
        v: Some(HeapValue::Bounded4GB),
    };

    assert_eq!(x1 == x2, false);
    assert_eq!(x2 == x3, true);
    assert_eq!(x3 == x4, false);

    assert_eq!(x1 != x2, true);
    assert_eq!(x2 != x3, false);
    assert_eq!(x3 != x4, true);

    assert_eq!(x1 > x2, false);
    assert_eq!(x2 > x3, false);
    assert_eq!(x3 > x4, false);

    assert_eq!(x1 < x2, true);
    assert_eq!(x2 < x3, false);
    assert_eq!(x3 < x4, false);

    assert_eq!(
        x1.meet(&x2, &LocIdx { addr: 0, idx: 0 }) == HeapValueLattice { v: None },
        true
    );
    assert_eq!(
        x2.meet(&x3, &LocIdx { addr: 0, idx: 0 })
            == HeapValueLattice {
                v: Some(HeapValue::HeapBase)
            },
        true
    );
    assert_eq!(
        x3.meet(&x4, &LocIdx { addr: 0, idx: 0 }) == HeapValueLattice { v: None },
        true
    );
}
