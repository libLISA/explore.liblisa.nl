use std::fmt::Display;
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not, Sub};

use liblisa::smt::{SmtBV, SmtBool, SmtInt, SmtModel, SmtModelRef, SmtSolver};

#[derive(Clone, Debug)]
pub struct BvConst {
    name: String,
    size: u32,
}

impl BvConst {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn size(&self) -> u32 {
        self.size
    }
}

#[derive(Clone, Debug)]
pub struct BoolConst {
    name: String,
}

impl BoolConst {
    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Clone, Debug, Default)]
pub struct SmtStringSolver {
    bv_consts: Vec<BvConst>,
    bool_consts: Vec<BoolConst>,
}

impl SmtStringSolver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bv_consts(&self) -> &[BvConst] {
        &self.bv_consts
    }

    pub fn bool_consts(&self) -> &[BoolConst] {
        &self.bool_consts
    }
}

fn f1(s: &str, x: impl Display) -> String {
    format!("({s} {x})")
}

fn f2(s: &str, lhs: impl Display, rhs: impl Display) -> String {
    format!("({s} {lhs} {rhs})")
}

fn f3(s: &str, a: impl Display, b: impl Display, c: impl Display) -> String {
    format!("({s} {a} {b} {c})")
}

impl<'a> SmtSolver<'a> for SmtStringSolver {
    type BV = BV;
    type Int = Int;
    type Bool = Bool;

    type ModelRef<'r>
        = ModelRef
    where
        Self: 'r;

    type Model = Model;

    fn bv_from_i64(&mut self, val: i64, size: u32) -> Self::BV {
        if size % 4 == 0 {
            BV(format!("#x{val:0width$X}", width = size as usize / 4))
        } else {
            BV(format!("#b{val:0width$b}", width = size as usize))
        }
    }

    fn bv_from_u64(&mut self, val: u64, size: u32) -> Self::BV {
        if size % 4 == 0 {
            BV(format!("#x{val:0width$X}", width = size as usize / 4))
        } else {
            BV(format!("#b{val:0width$b}", width = size as usize))
        }
    }

    fn bv_from_int(&mut self, int: Self::Int, size: u32) -> Self::BV {
        BV(format!("((_ int2bv {size}) {int})"))
    }

    fn new_bv_const(&mut self, name: impl AsRef<str>, size: u32) -> Self::BV {
        self.bv_consts.push(BvConst {
            name: name.as_ref().to_string(),
            size,
        });
        BV(name.as_ref().to_string())
    }

    fn new_bool_const(&mut self, name: impl AsRef<str>) -> Self::Bool {
        self.bool_consts.push(BoolConst {
            name: name.as_ref().to_string(),
        });

        Bool(name.as_ref().to_string())
    }

    fn int_from_i64(&mut self, val: i64) -> Self::Int {
        Int(val.to_string())
    }

    fn int_from_u64(&mut self, val: u64) -> Self::Int {
        Int(val.to_string())
    }

    fn int_from_bv(&mut self, bv: Self::BV, signed: bool) -> Self::Int {
        if signed {
            todo!()
        }

        Int(f1("bv2int", bv))
    }

    fn bool_from_bool(&mut self, val: bool) -> Self::Bool {
        Bool(val.to_string())
    }

    fn forall_const(&mut self, _vals: &[liblisa::smt::Dynamic<'a, Self>], _condition: Self::Bool) -> Self::Bool {
        todo!("forall")
    }

    fn check_assertions<'me>(&'me mut self, _assertions: &[Self::Bool]) -> liblisa::smt::SatResult<Self::ModelRef<'me>> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct BV(String);

impl Display for BV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl SmtBV<'_, SmtStringSolver> for BV {
    fn is_identical(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn concat(self, other: Self) -> Self {
        BV(f2("concat", self, other))
    }

    fn extract(self, hi: u32, lo: u32) -> Self {
        BV(f1(&format!("(_ extract {hi} {lo})"), self))
    }

    fn zero_ext(self, num: u32) -> Self {
        BV(f1(&format!("(_ zero_extend {num})"), self))
    }

    fn sign_ext(self, num: u32) -> Self {
        BV(f1(&format!("(_ sign_extend {num})"), self))
    }

    fn bvshl(self, count: Self) -> Self {
        BV(f2("bvshl", self, count))
    }

    fn bvlshr(self, count: Self) -> Self {
        BV(f2("bvlshr", self, count))
    }

    fn bvashr(self, count: Self) -> Self {
        BV(f2("bvashr", self, count))
    }

    fn bvurem(self, n: Self) -> Self {
        BV(f2("bvurem", self, n))
    }

    fn bvsrem(self, n: Self) -> Self {
        BV(f2("bvsrem", self, n))
    }

    fn bvudiv(self, n: Self) -> Self {
        BV(f2("bvudiv", self, n))
    }

    fn bvsdiv(self, n: Self) -> Self {
        BV(f2("bvsdiv", self, n))
    }

    fn bvrotl(self, count: Self) -> Self {
        BV(f2("bvrotl", self, count))
    }

    fn bvrotr(self, count: Self) -> Self {
        BV(f2("bvrotr", self, count))
    }

    fn bvslt(self, other: Self) -> Bool {
        Bool(f2("bvslt", self, other))
    }

    fn bvsge(self, other: Self) -> Bool {
        Bool(f2("bvsge", self, other))
    }

    fn bvsgt(self, other: Self) -> Bool {
        Bool(f2("bvsgt", self, other))
    }

    fn bvugt(self, other: Self) -> Bool {
        Bool(f2("bvugt", self, other))
    }

    fn bvult(self, other: Self) -> Bool {
        Bool(f2("bvult", self, other))
    }

    fn bvule(self, other: Self) -> Bool {
        Bool(f2("bvule", self, other))
    }

    fn bvuge(self, other: Self) -> Bool {
        Bool(f2("bvuge", self, other))
    }

    fn _eq(self, other: Self) -> Bool {
        Bool(f2("=", self, other))
    }

    fn simplify(self) -> Self {
        self
    }

    fn get_size(&self) -> u32 {
        // TODO
        128
    }

    fn as_u64(&self) -> Option<u64> {
        None
    }
}

impl Not for BV {
    type Output = BV;

    fn not(self) -> Self::Output {
        BV(f1("not", self))
    }
}

impl BitXor for BV {
    type Output = BV;

    fn bitxor(self, rhs: Self) -> Self::Output {
        BV(f2("bvxor", self, rhs))
    }
}

impl BitAnd for BV {
    type Output = BV;

    fn bitand(self, rhs: Self) -> Self::Output {
        BV(f2("bvand", self, rhs))
    }
}

impl BitOr for BV {
    type Output = BV;

    fn bitor(self, rhs: Self) -> Self::Output {
        BV(f2("bvor", self, rhs))
    }
}

impl Mul for BV {
    type Output = BV;

    fn mul(self, rhs: Self) -> Self::Output {
        BV(f2("bvmul", self, rhs))
    }
}

impl Add for BV {
    type Output = BV;

    fn add(self, rhs: Self) -> Self::Output {
        BV(f2("bvadd", self, rhs))
    }
}

impl Sub for BV {
    type Output = BV;

    fn sub(self, rhs: Self) -> Self::Output {
        BV(f2("bvsub", self, rhs))
    }
}

#[derive(Clone, Debug)]
pub struct Int(String);

impl Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl SmtInt<'_, SmtStringSolver> for Int {
    fn is_identical(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn _eq(self, other: Self) -> Bool {
        Bool(f2("=", self, other))
    }

    fn simplify(self) -> Self {
        self
    }

    fn as_u64(&self) -> Option<u64> {
        None
    }
}

impl Mul for Int {
    type Output = Int;

    fn mul(self, rhs: Self) -> Self::Output {
        Int(f2("*", self, rhs))
    }
}

impl Add for Int {
    type Output = Int;

    fn add(self, rhs: Self) -> Self::Output {
        Int(f2("+", self, rhs))
    }
}

impl Sub for Int {
    type Output = Int;

    fn sub(self, rhs: Self) -> Self::Output {
        Int(f2("-", self, rhs))
    }
}

#[derive(Clone, Debug)]
pub struct Bool(String);

impl Display for Bool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl SmtBool<'_, SmtStringSolver> for Bool {
    fn is_identical(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    fn _eq(self, other: Self) -> Bool {
        Bool(f2("=", self, other))
    }

    fn simplify(self) -> Self {
        self
    }

    fn ite_bv(self, lhs: BV, rhs: BV) -> BV {
        BV(f3("ite", self, lhs, rhs))
    }

    fn ite_int(self, lhs: Int, rhs: Int) -> Int {
        Int(f3("ite", self, lhs, rhs))
    }

    fn ite_bool(self, lhs: Bool, rhs: Bool) -> Bool {
        Bool(f3("ite", self, lhs, rhs))
    }

    fn as_bool(&self) -> Option<bool> {
        None
    }
}

impl Not for Bool {
    type Output = Bool;

    fn not(self) -> Self::Output {
        Bool(f1("bvnot", self))
    }
}

impl BitXor for Bool {
    type Output = Bool;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Bool(f2("bvxor", self, rhs))
    }
}

impl BitAnd for Bool {
    type Output = Bool;

    fn bitand(self, rhs: Self) -> Self::Output {
        Bool(f2("bvand", self, rhs))
    }
}

impl BitOr for Bool {
    type Output = Bool;

    fn bitor(self, rhs: Self) -> Self::Output {
        Bool(f2("bvor", self, rhs))
    }
}

#[derive(Clone, Debug)]
pub struct ModelRef;

impl SmtModelRef<'_, SmtStringSolver> for ModelRef {
    fn to_model(&self) -> Option<Model> {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct Model;

impl SmtModel<'_, SmtStringSolver> for Model {
    fn get_const_interp(&self, _name: &BV) -> Option<BV> {
        todo!()
    }
}
