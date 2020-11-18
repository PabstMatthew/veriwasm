use crate::lifter::ValSize;
use crate::lifter::Binopcode;
use crate::ir_utils::is_rsp;
use crate::ir_utils::get_imm_offset;
use std::cmp::Ordering;
pub mod regslattice;
pub mod heaplattice;
pub mod switchlattice;
pub mod davlattice;
pub mod calllattice;
pub mod stackgrowthlattice;
pub mod stacklattice;
pub mod reachingdefslattice;
use crate::lattices::regslattice::X86RegsLattice;
use crate::lattices::stacklattice::StackLattice;
use crate::lifter::{Value, MemArgs, MemArg, ImmType};
use std::fmt::Debug;

pub trait Lattice: PartialOrd + Eq + Default + Debug{
    fn meet(&self, other : &Self) -> Self;
}

pub trait VarState{
    type Var;
    fn get(&mut self, index : &Value) -> Option<Self::Var>;
    fn set(&mut self, index : &Value, v : Self::Var) -> ();
    fn set_to_bot(&mut self, index : &Value) -> ();
    fn on_call(&mut self) -> ();
    fn adjust_stack_offset(&mut self, opcode: &Binopcode, dst: &Value, src1: &Value, src2: &Value);
    // fn get_reg(&self, index : &Value) -> Self::Var; 
}

#[derive(Eq, Clone, Copy, Debug)]
pub struct BooleanLattice{
    v: bool
}

impl PartialOrd for BooleanLattice {
    fn partial_cmp(&self, other: &BooleanLattice) -> Option<Ordering> {
        Some(self.v.cmp(&other.v))
    }
}

impl PartialEq for BooleanLattice {
    fn eq(&self, other: &BooleanLattice) -> bool {
        self.v == other.v
    }
}

impl Lattice for BooleanLattice {
    fn meet(&self, other : &Self) -> Self {
        BooleanLattice {v : self.v && other.v}
    }
} 

impl Default for BooleanLattice {
    fn default() -> Self {
        BooleanLattice {v : false}
    }
}

pub type Constu32Lattice = ConstLattice::<u32>;

#[derive(Eq, Clone, Copy, Debug)]
pub struct ConstLattice<T:Eq + Copy + Debug>{
    pub v: Option<T>
}

impl<T:Eq + Copy + Debug> PartialOrd for ConstLattice<T> {
    fn partial_cmp(&self, other: &ConstLattice<T>) -> Option<Ordering> {
        match (self.v, other.v){
            (None,None) => Some(Ordering::Equal),
            (None,_) => Some(Ordering::Less),
            (_,None) => Some(Ordering::Greater),
            (Some(x), Some(y)) => 
                if x == y {Some(Ordering::Equal) }
                else {None}
        }
    }
}

impl<T:Eq + Copy + Debug> PartialEq for ConstLattice<T> {
    fn eq(&self, other: &ConstLattice<T>) -> bool {
        self.v == other.v
    }
}

impl<T:Eq + Copy + Debug> Lattice for ConstLattice<T> {
    fn meet(&self, other : &Self) -> Self {
        if self.v == other.v {ConstLattice {v : self.v}}
        else {ConstLattice { v : None}}
    }
} 

impl<T:Eq + Copy + Debug> Default for ConstLattice<T> {
    fn default() -> Self {
        ConstLattice {v : None}
    }
}

impl<T:Eq + Copy + Debug> ConstLattice<T>{
    pub fn new(v : T) -> Self{
        ConstLattice{ v : Some(v)}
    }
}



#[derive(PartialEq, Eq, PartialOrd, Default, Clone, Debug)]
pub struct VariableState<T:Lattice + Clone>{
    pub regs: X86RegsLattice<T>,
    pub stack: StackLattice<T>,
}

impl<T:Lattice + Clone> Lattice for VariableState<T> {
    fn meet(&self, other : &Self) -> Self {
        VariableState { 
            regs : self.regs.meet(&other.regs), 
            stack : self.stack.meet(&other.stack)
        }
    }
} 


impl<T:Lattice + Clone> VarState for VariableState<T> {
    type Var = T;
    fn set(&mut self, index : &Value, value : T) -> (){
        match index{
            Value::Mem(_, memargs) => match memargs{
                MemArgs::Mem1Arg(arg) => 
                    if let MemArg::Reg(regnum, size) = arg{
                        if *regnum == 4{
                            self.stack.update(0, value, size.to_u32() / 8)
                        }
                    },
                MemArgs::Mem2Args(arg1, arg2) => 
                    if let MemArg::Reg(regnum, size) = arg1{
                        if *regnum == 4{
                            if let MemArg::Imm(imm_sign,_,offset) = arg2{
                                self.stack.update(*offset, value, size.to_u32() / 8)
                            }
                        }
                    },
                _ => ()
            },
            Value::Reg(regnum,s2) => self.regs.set(regnum, s2, value),
            Value::Imm(_,_,_) => panic!("Trying to write to an immediate value"),
        }
    } 

    fn get(&mut self, index : &Value) -> Option<T>{
        match index{
            Value::Mem(_, memargs) => match memargs{
                MemArgs::Mem1Arg(arg) => {
                    if let MemArg::Reg(regnum, size) = arg{
                        if *regnum == 4{
                            return Some(self.stack.get(0, size.to_u32() / 8));
                        }
                    } 
                    None},
                MemArgs::Mem2Args(arg1, arg2) => {
                    if let MemArg::Reg(regnum, size) = arg1{
                        if *regnum == 4{
                            if let MemArg::Imm(imm_sign,_,offset) = arg2{
                                return Some(self.stack.get(*offset, size.to_u32() / 8));
                            }
                        }
                    }
                    None} ,
                _ => None
            },
            Value::Reg(regnum,s2) => Some(self.regs.get(regnum, s2)),
            Value::Imm(_,_,_) => None,
        }
    } 

    fn set_to_bot(&mut self, index : &Value){
        self.set(index, Default::default())
    }

    fn on_call(&mut self){
        self.regs.clear_regs()
    }

    fn adjust_stack_offset(&mut self, opcode: &Binopcode, dst: &Value, src1: &Value, src2: &Value){
        if is_rsp(dst) {
            if is_rsp(src1){
                let adjustment = get_imm_offset(src2);
                //println!("opcode = {:?} {:?} = {:?} {:?} {:?}", opcode, dst, src1, src2, adjustment); 
                match opcode{
                    Binopcode::Add => self.stack.update_stack_offset(adjustment),
                    Binopcode::Sub => self.stack.update_stack_offset(-adjustment),
                    _ => panic!("Illegal RSP write")
                }
                
            }
            else{ panic!("Illegal RSP write") }
        }        
    }
} 

// //TODO: complete transition to default aexec
// impl<T:Lattice + Clone> VariableState<T>{
//     pub fn default_exec_binop(&mut self, dst: &Value, src1: &Value, src2: &Value){
//         self.adjust_stack_offset(dst, src1, src2); 
//         self.set_to_bot(dst)
//     }
// }




#[test]
fn boolean_lattice_test() {
    let x  = BooleanLattice {v : false};
    let y  = BooleanLattice {v : true};
    assert_eq!(x < y, true);
    assert_eq!(x > y, false);
    assert_eq!(x.lt(&y), true);
}

#[test]
fn u32_lattice_test() {
    let x1  = ConstLattice::<u32> {v : Some(1)};
    let x2  = ConstLattice::<u32> {v : Some(1)};
    let y1  = ConstLattice::<u32> {v : Some(2)};
    let y2  = ConstLattice::<u32> {v : Some(2)};

    let z1  = Constu32Lattice {v : Some(3)};
    let z2  = Constu32Lattice {v : Some(3)};

    // let y1  = Constu32Lattice {v : Some(2)};
    // let y2  = Constu32Lattice {v : Some(2)};
    assert_eq!(x1 < y1, false);
    assert_eq!(y1 < x1, false);
    assert_eq!(x1 == x2, true);
    assert_eq!(x1 != x2, false);
    assert_eq!(y2 != x1, true);
    assert_eq!(x1 >= y1, false);
    assert_eq!(x1 > x2, false);
    assert_eq!(x1 >= x2, true);
    assert_eq!(z1 == z2, true);
    assert_eq!(z1 == x1, false);
    assert_eq!(x1.lt(&y1), false);
}
