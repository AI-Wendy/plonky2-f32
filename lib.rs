use plonky2::field::goldilocks_field::GoldilocksField as Fld;
use plonky2::field::types::Field;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::plonk::circuit_builder::CircuitBuilder;

use plonky2::hash::merkle_tree::MerkleTree as Mt;
use plonky2::hash::poseidon::PoseidonHash as Ph;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_data::{CircuitConfig, VerifierCircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::plonk::proof::CompressedProofWithPublicInputs;

pub const D: usize = 2;
pub type C = PoseidonGoldilocksConfig;
pub type F = <C as GenericConfig<D>>::F;
pub type H = <C as GenericConfig<D>>::Hasher;

use std::borrow::{Borrow, BorrowMut};
use std::ops::{Add, Mul, Neg, Not, Sub};

use crate::fld_float2::GLHALF;
use crate::fld_float2::*;

pub const SPLIT: u64 = 1 << 12;

pub type Cb = CircuitBuilder<Fld, 2>;

pub struct Ops<'a, Cb, T> {
    cb: &'a mut Cb,
    shift: Vec<T>,
}

pub trait Trait<'a> {
    type Cb: 'a;
    type T: Clone + Copy + std::fmt::Debug;
    type Bt: Clone + Copy + std::fmt::Debug;

    fn debug<F: FnOnce(Fld)>(a: Self::Bt, b: Self::T, f: F) {}

    fn get_cb(self) -> &'a mut Self::Cb;
    fn get_shift(&self) -> &Vec<Self::T>;

    fn fake() -> Self::T;

    fn unsafe_into_bool(a: Self::T) -> Self::Bt;

    fn constant(&mut self, fld: Fld) -> Self::T;

    fn neg(&mut self, a: Self::T) -> Self::T;
    fn add(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T;
    fn sub(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T;
    fn mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T;

    fn and(&mut self, lhs: Self::Bt, rhs: Self::Bt) -> Self::Bt;
    fn or(&mut self, lhs: Self::Bt, rhs: Self::Bt) -> Self::Bt;
    fn not(&mut self, a: Self::Bt) -> Self::Bt;

    fn is_equal(&mut self, lhs: Self::T, rhs: Self::T) -> Self::Bt;

    fn select(&mut self, cnd: Self::Bt, lhs: Self::T, rhs: Self::T) -> Self::T;
    fn random_access(&mut self, i: Self::T, v: Vec<Self::T>) -> Self::T;
    fn split_le(&mut self, integer: Self::T, num_bits: usize) -> Vec<Self::Bt>;
    fn split_low_high(&mut self, x: Self::T, n_log: usize, num_bits: usize) -> (Self::T, Self::T);

    fn new(cb: &'a mut Self::Cb) -> Ops<'a, Self::Cb, Self::T>
    where
        Self::T: 'a,
        Ops<'a, Self::Cb, Self::T>: Trait<'a, Cb = Self::Cb, T = Self::T>,
    {
        let mut shift = vec![];
        let mut obj = Ops { cb, shift: vec![] };
        for i in 0..16 {
            shift.push(obj.constant(Fld(1u64 << i)));
        }
        Ops {
            cb: obj.get_cb(),
            shift,
        }
    }

    /// Multiply input by weight.
    fn mul_ibw(
        &mut self,
        input: FldFloat3<Self::T>,
        weight: FldFloat4<Self::T>,
    ) -> FldFloat25<Self::T> {
        //println!("MUL_IBE I O {input:#?} {weight:#?}");

        let fmf = self.mul(input.fld_f, weight.fld_mf);
        let fdf = self.mul(input.fld_f, weight.fld_df);

        let fme = self.add(input.fld_me, weight.fld_me);
        let fde = self.add(input.fld_de, weight.fld_de);

        // 16 - 12 = 4, 11 + 4 = 15, so number GE 16 will have extra bit.
        let plus_for_mod = self.constant(Fld(4));
        let fme_plus_4 = self.add(fme, plus_for_mod);
        let (modu, curry) = self.split_low_high(fme_plus_4, 4, 5);
        let modu_fixed = self.sub(modu, plus_for_mod);
        let modu = self.select(Self::unsafe_into_bool(curry), modu, modu_fixed);

        //println!("FME {fme:#?} {modu:#?}");

        let mul_to_shift = self.random_access(modu, self.get_shift().clone());
        let fmf = self.mul(fmf, mul_to_shift);
        let fdf = self.mul(fdf, mul_to_shift);
        let fde = self.add(fde, curry);

        let plus_for_idx = self.constant(Fld(12));
        let idx = self.add(fde, plus_for_idx);

        //println!("MODU CURRY M2S {modu:#?} {curry:#?} {mul_to_shift:#?}");
        //println!("FDE {fde:#?} IDX {idx:#?} FMF {fmf:#?} FDF {fdf:#?}");

        let zero = self.constant(Fld(0));
        let mut out = FldFloat25([zero; 25]);
        for i in 0..24 {
            let pos = self.constant(Fld(i as u64));
            let is_eq = self.is_equal(pos, idx);
            //println!("IS_EQ {pos:#?} {idx:#?} {is_eq:#?}");
            out.0[i] = self.select(is_eq, fmf, out.0[i]);
            out.0[i + 1] = self.select(is_eq, fdf, out.0[i + 1]);
        }
        out
    }

    fn ibw_add_many<A, B>(&mut self, terms: B) -> FldFloat25<Self::T>
    where
        A: Borrow<FldFloat25<Self::T>>,
        B: IntoIterator<Item = A>,
    {
        let mut it = terms.into_iter();
        let mut acc = it.next().unwrap().borrow().clone();
        for elm in it {
            for i in 0..25 {
                //println!("{} {:#?}", i, acc.0[i]);
                acc.0[i] = self.add(acc.0[i], elm.borrow().0[i]);
                //println!("{} {:#?}", i, acc.0[i]);
            }
        }
        acc
    }

    /*
    24 bits of mantissa + 1 bit of sign = 25 bits.
    12 bits of mantissa + 1 bit of sign = 13 bits.
    25 + 13 = 38, bits after multiplication.
    38 + 12 = 50, bits after shift.
    64 - 50 = 14, bits left as space for addition (not full 100% of this bits is used).
    (a + bx)c = ac + bcx, x is 2^12.
    we still need to add, to normalize, so it is reason to add less then 52 bits.
    */

    fn ibw_norm(&mut self, ibw: &FldFloat25<Self::T>) -> FldFloat4<Self::T> {
        let zero = self.constant(Fld(0));
        let fls = Self::unsafe_into_bool(zero);
        let one = self.constant(Fld(1));
        let two = self.constant(Fld(2));
        let p12 = self.constant(Fld(1 << 12));
        let p24 = self.constant(Fld(1 << 24));
        let p36 = self.constant(Fld(1 << 36));

        let mut wa = zero;
        let mut wb = zero;
        let mut wc = zero;
        let mut pos_u = zero;
        let mut done = fls;
        for i in (0..25).rev() {
            let new_pos_u = self.constant(Fld(i as u64));

            let a = ibw.0[i];
            let mut b = zero;
            let mut c = zero;
            if i >= 1 {
                b = ibw.0[i - 1];
            }
            if i >= 2 {
                c = ibw.0[i - 2];
            }

            let cnd = self.is_equal(a, zero);
            let cnd = self.not(cnd);
            let not_done = self.not(done);
            let update = self.and(cnd, not_done);
            done = self.or(cnd, done);
            wa = self.select(update, a, wa);
            wb = self.select(update, b, wb);
            wc = self.select(update, c, wc);
            pos_u = self.select(update, new_pos_u, pos_u);
        }

        macro_rules! high {
            ($a:expr, $bits:expr) => {{
                let (_, sa) = self.split_low_high($a, 63, 64);
                let sa = Self::unsafe_into_bool(sa);
                let na = self.neg($a);
                let aa = self.select(sa, na, $a);
                let (_, aha) = self.split_low_high(aa, $bits, 63);
                let naha = self.neg(aha);
                self.select(sa, naha, aha)
            }};
        }

        let wb = high!(wb, 12);
        let wc = high!(wc, 24);
        let sfrac = self.add(wa, wb);
        let sfrac = self.add(sfrac, wc);

        let (_, sign) = self.split_low_high(sfrac, 63, 64);
        let sign = Self::unsafe_into_bool(sign);
        let nfrac = self.neg(sfrac);
        let frac = self.select(sign, nfrac, sfrac);
        let bits = self.split_le(frac, 63);

        let mut pos_mv = zero;
        let mut pos_dv = zero;
        let mut mul_shift = self.constant(Fld(1 << 62));
        let mut done = fls;
        for i in 0..63 {
            let j = 62 - i;
            let cnd = bits[j];
            let not_done = self.not(done);
            let update = self.and(cnd, not_done);
            done = self.or(cnd, done);
            let new_mul_shift = self.constant(Fld(1 << i));
            let new_pos_mv = self.constant(Fld((j as u64) % 12));
            let new_pos_dv = self.constant(Fld((j as u64) / 12));
            pos_mv = self.select(update, new_pos_mv, pos_mv);
            pos_dv = self.select(update, new_pos_dv, pos_dv);
            mul_shift = self.select(update, new_mul_shift, mul_shift);
        }
        let frac = self.mul(frac, mul_shift);
        let (_, frac) = self.split_low_high(frac, 39, 63);
        let (lo, hi) = self.split_low_high(frac, 12, 24);
        let nlo = self.neg(lo);
        let nhi = self.neg(hi);
        let lo = self.select(sign, nlo, lo);
        let hi = self.select(sign, nhi, hi);

        let fld_me = pos_mv;
        let fld_de = self.add(pos_u, pos_dv);

        let plus_for_mod = self.constant(Fld(29));
        let fix_a = self.constant(Fld(0));
        let fix_b = self.constant(Fld(20));
        let val = self.add(fld_me, plus_for_mod);
        let (modu, curry) = self.split_low_high(val, 5, 6);
        let curry = self.is_equal(curry, zero);
        let curry = self.not(curry);
        let posfx = self.select(curry, one, zero);
        let modu_a = self.sub(modu, fix_a);
        let modu_b = self.sub(modu, fix_b);
        let modu = self.select(curry, modu_a, modu_b);
        let fld_de = self.add(fld_de, posfx);
        let fix = self.constant(Fld(17));
        let fld_de = self.sub(fld_de, fix);

        FldFloat4 {
            fld_mf: lo,
            fld_df: hi,
            fld_me: modu,
            fld_de,
        }
    }
}

#[rustfmt::skip]
impl<'a> Trait<'a> for Ops<'a, Cb, Target> {
    type Cb = Cb;
    type T = Target;
    type Bt = BoolTarget;
    fn get_cb(self) -> &'a mut Self::Cb { self.cb }
    fn get_shift(&self) -> &Vec<Target> { &self.shift }
    fn unsafe_into_bool(a: Self::T) -> Self::Bt { BoolTarget::new_unsafe(a) }
    fn fake() -> Self::T { Target::VirtualTarget { index: 0 } }
    fn constant(&mut self, fld: Fld) -> Self::T { self.cb.constant(fld) }
    fn neg(&mut self, a: Self::T) -> Self::T { self.cb.neg(a) }
    fn add(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T { self.cb.add(lhs, rhs) }
    fn sub(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T { self.cb.sub(lhs, rhs) }
    fn mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T { self.cb.mul(lhs, rhs) }
    fn and(&mut self, lhs: Self::Bt, rhs: Self::Bt) -> Self::Bt { self.cb.and(lhs, rhs) }
    fn or(&mut self, lhs: Self::Bt, rhs: Self::Bt) -> Self::Bt { self.cb.or(lhs, rhs) }
    fn not(&mut self, a: Self::Bt) -> Self::Bt { self.cb.not(a) }
    fn is_equal(&mut self, lhs: Self::T, rhs: Self::T) -> Self::Bt { self.cb.is_equal(lhs, rhs) }
    fn select(&mut self, cnd: Self::Bt, lhs: Self::T, rhs: Self::T) -> Self::T { self.cb.select(cnd, lhs, rhs) }
    fn random_access(&mut self, i: Self::T, v: Vec<Self::T>) -> Self::T { self.cb.random_access(i, v) }
    fn split_low_high(&mut self, x: Self::T, n_log: usize, num_bits: usize) -> (Self::T, Self::T) {
        self.cb.split_low_high(x, n_log, num_bits)
    }
    fn split_le(&mut self, integer: Self::T, num_bits: usize) -> Vec<Self::Bt> { self.cb.split_le(integer, num_bits) }
}

#[rustfmt::skip]
impl<'a> Trait<'a> for Ops<'a, (), Fld> {
    type Cb = ();
    type T = Fld;
    type Bt = bool;
    fn debug<F: FnOnce(Fld)>(a: Self::Bt, b: Self::T, f: F) { f(b); }
    fn get_cb(self) -> &'a mut Self::Cb { self.cb }
    fn get_shift(&self) -> &Vec<Fld> { &self.shift }
    fn unsafe_into_bool(a: Self::T) -> Self::Bt { a.0 > 0 }
    fn fake() -> Self::T { Fld(0) }
    fn constant(&mut self, fld: Fld) -> Self::T { fld }
    fn neg(&mut self, a: Self::T) -> Self::T { a.neg() }
    fn add(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T { lhs.add(rhs).neg().neg() }
    fn sub(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T { lhs.sub(rhs) }
    fn mul(&mut self, lhs: Self::T, rhs: Self::T) -> Self::T { lhs.mul(rhs) }
    fn and(&mut self, lhs: Self::Bt, rhs: Self::Bt) -> Self::Bt { lhs & rhs }
    fn or(&mut self, lhs: Self::Bt, rhs: Self::Bt) -> Self::Bt { lhs || rhs }
    fn not(&mut self, a: Self::Bt) -> Self::Bt { a.not() }
    fn is_equal(&mut self, lhs: Self::T, rhs: Self::T) -> Self::Bt { lhs == rhs }
    fn select(&mut self, cnd: Self::Bt, lhs: Self::T, rhs: Self::T) -> Self::T { if cnd { lhs } else { rhs } }
    fn random_access(&mut self, i: Self::T, v: Vec<Self::T>) -> Self::T {
      //println!("RANDOM ACCESS {}", i.0);
      v[i.0 as usize]
    }
    fn split_low_high(&mut self, x: Self::T, n_log: usize, num_bits: usize) -> (Self::T, Self::T) {
        let l = x.0 & ((1 << n_log)-1);
        let h = x.0 >> n_log;
        assert_eq!(x.0, l | (h << n_log));
        (Fld(l), Fld(h))
    }
    fn split_le(&mut self, integer: Self::T, num_bits: usize) -> Vec<Self::Bt> {
      let mut bits = vec![];
      let mut a = integer.0;
      let mut b = 0;
      for i in 0..num_bits {
        bits.push((a & 1) == 1);
        b |= (a & 1) << i;
        a >>= 1;
      }
      assert_eq!(integer.0, b);
      bits
    }
}

#[cfg(test)]
enum MulTestRes {
    Exact,
    Pass1(f64),
    Diff(f64),
    Problem(f32, f32),
}

#[cfg(test)]
fn check_mul_test(a: f32, b: f32) -> MulTestRes {
    let mut cb = ();
    let mut ops = Ops::<(), Fld>::new(&mut cb);
    let c = FldFloat3::from_f32(a);
    let d = FldFloat4::from_f32(b);
    let g = FldFloat4::from_f32((a as f64 * b as f64) as f32);
    let e = ops.mul_ibw(c, d);
    let mut f = ops.ibw_norm(&e);
    let dif = f.fld_mf.0 as isize - g.fld_mf.0 as isize;
    let eq1 = f.fld_df.0 == g.fld_df.0;
    let eq2 = f.fld_me.0 == g.fld_me.0;
    let eq3 = f.fld_de.0 == g.fld_de.0;
    if !(eq1 && eq2 && eq3) {
        let mut _f = FldFloat4::into_f64_for_test(&f);
        let mut _g = FldFloat4::into_f64_for_test(&g);
        let mx = _f.abs().min(_g.abs());
        let fix = 2.0_f64.powf(mx.log2().round());
        _f /= fix;
        _g /= fix;
        let dif = (_f - _g).abs();
        //println!("DIF {dif} {_f} {_g}");
        //println!("{a} {b} {eq1} {eq2} {eq3}\n{g:#?}\n{f:#?}");
        if dif.is_finite() {
            MulTestRes::Diff(dif)
        } else {
            MulTestRes::Problem(a, b)
        }
    } else {
        if dif == 0 {
            MulTestRes::Exact
        } else {
            MulTestRes::Pass1((dif as f64).powf(2.0))
        }
    }
}

#[test]
fn test_rndsmp_01() {
    use rand::prelude::*;
    let min_base: Vec<f32> = vec![0.0, 1.0, f32::MIN_POSITIVE, 1.40129846432e-45_f32];
    let max_base: Vec<f32> = vec![0.0, 999999.0, 999999999999.0, 1E+23, 1E+32, f32::MAX];
    let mut rng = rand::thread_rng();
    let mut rnd = || loop {
        let i: usize = rng.gen_range(0..min_base.len());
        let j: usize = rng.gen_range(0..max_base.len());
        let mib = min_base[i] as f64;
        let mab = max_base[j] as f64;
        let a: f64 = rng.gen();
        let b: f64 = rng.gen();
        let c = ((a * 2.0 - 1.0) * 4.0).tanh() * mab;
        let d = ((b * 2.0 - 1.0) * 0.999999999).atanh() * 999.0 * mib;
        let e = (c + d) as f32;
        if e.is_finite() && (e.is_normal() || e.is_subnormal()) {
            return e.abs();
        }
    };
    let mut rnd_pair = || loop {
        let a = rnd();
        let b = rnd();
        let c = a * b;
        if c.is_finite() && (c.is_normal() | c.is_subnormal()) {
            return (a, b);
        }
    };
    let samples = 9999;
    let mut exact_cnt = 0.0_f64;
    let mut pass_cnt = 0.0_f64;
    let mut pass_acc = 0.0_f64;
    let mut dif_cnt = 0.0_f64;
    let mut dif_acc = 0.0_f64;
    let mut problems = vec![];
    for _ in 0..samples {
        let (a, b) = rnd_pair();
        match check_mul_test(a, b) {
            MulTestRes::Exact => {
                exact_cnt += 1.0;
            }
            MulTestRes::Pass1(a) => {
                pass_cnt += 1.0;
                pass_acc += a;
            }
            MulTestRes::Diff(a) => {
                dif_cnt += 1.0;
                dif_acc += a;
            }
            MulTestRes::Problem(a, b) => {
                problems.push((a, b));
            }
        }
    }
    pass_acc /= pass_cnt;
    dif_acc /= dif_cnt;
    pass_acc = pass_acc.sqrt();
    let prlen = problems.len();
    let per = 100.0 / ((pass_cnt + dif_cnt) / pass_cnt);
    println!("PASS DIF {prlen} {exact_cnt} {dif_cnt} {per} {pass_acc} {dif_acc}");
}

use plonky2::iop::generator::SimpleGenerator;
use plonky2::iop::witness::PartitionWitness;
use plonky2::iop::generator::GeneratedValues;
use std::sync::Arc;

#[derive(Debug)]
pub struct InputGenerator<F> {
    pub tab: Arc<Vec<(FldFloat3<Target>,FldFloat3<F>,f32)>>,
}

impl<F: Field> SimpleGenerator<F> for InputGenerator<F> {
    fn dependencies(&self) -> Vec<Target> {
        Vec::new()
    }
    fn run_once(&self, _witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        for (t,f,_) in self.tab.iter() {
          out_buffer.set_target(t.fld_f, f.fld_f);
          out_buffer.set_target(t.fld_me, f.fld_me);
          out_buffer.set_target(t.fld_de, f.fld_de);
        }
    }
}

#[derive(Debug)]
pub struct WeightsGenerator<F> {
    pub tab: Arc<Vec<(FldFloat4<Target>,FldFloat4<F>,f32)>>,
}

impl<F: Field> SimpleGenerator<F> for WeightsGenerator<F> {
    fn dependencies(&self) -> Vec<Target> {
        Vec::new()
    }
    fn run_once(&self, _witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        for (t,f,_) in self.tab.iter() {
          out_buffer.set_target(t.fld_mf, f.fld_mf);
          out_buffer.set_target(t.fld_df, f.fld_df);
          out_buffer.set_target(t.fld_me, f.fld_me);
          out_buffer.set_target(t.fld_de, f.fld_de);
        }
    }
}

#[test]
fn test_rndsmp_muladd_with_proof() {
    use rand::prelude::*;
    let mut rng = rand::thread_rng();
    let config = CircuitConfig::standard_recursion_config();
    let mut cb = CircuitBuilder::<F, D>::new(config);
    let mut ops = Ops::<_, Target>::new(&mut cb);
    let input_size = 768;
    let mut input_tab = vec![];
    let mut weights_tab = vec![];
    let mut input_targs = vec![];
    let mut weights_targs = vec![];
    let mut check_sum = 0_f32;
    let mut products = vec![];
    for _ in 0..input_size {
        let a: f32 = rng.gen();
        let b = ((a * 2.0 - 1.0) * 0.999999999).atanh() * 1.0;
        let c = FldFloat3::from_f32(b);
        let d: f32 = rng.gen();
        let e = ((a * 2.0 - 1.0) * 0.999999999).atanh() * 1.0;
        let f = FldFloat4::from_f32(b);
        let fld_f = ops.cb.add_virtual_target();
        let fld_me = ops.cb.add_virtual_target();
        let fld_de = ops.cb.add_virtual_target();
        let lhs = FldFloat3 { fld_f, fld_me, fld_de };
        input_tab.push((FldFloat3 { fld_f, fld_me, fld_de }, c, b));
        input_targs.push(fld_f);
        input_targs.push(fld_me);
        input_targs.push(fld_de);
        let fld_mf = ops.cb.add_virtual_target();
        let fld_df = ops.cb.add_virtual_target();
        let fld_me = ops.cb.add_virtual_target();
        let fld_de = ops.cb.add_virtual_target();
        weights_tab.push((FldFloat4 { fld_mf, fld_df, fld_me, fld_de }, f, e));
        weights_targs.push(fld_mf);
        weights_targs.push(fld_df);
        weights_targs.push(fld_me);
        weights_targs.push(fld_de);
        let rhs = FldFloat4 { fld_mf, fld_df, fld_me, fld_de };
        products.push(ops.mul_ibw(lhs, rhs));
        check_sum += b * e;
    }
    let input_tab_arc = Arc::new(input_tab);
    let weights_tab_arc = Arc::new(weights_tab);
    ops.cb.add_simple_generator(InputGenerator { tab: input_tab_arc.clone() });
    ops.cb.add_simple_generator(WeightsGenerator { tab: weights_tab_arc.clone() });
    let input_hash = ops.cb.hash_or_noop::<H>(input_targs);
    let weights_hash = ops.cb.hash_or_noop::<H>(weights_targs);
    let sum = ops.ibw_add_many(&products);
    let norm = ops.ibw_norm(&sum);

    ops.cb.register_public_inputs(&input_hash.elements);
    ops.cb.register_public_inputs(&weights_hash.elements);
    ops.cb.register_public_input(norm.fld_mf);
    ops.cb.register_public_input(norm.fld_df);
    ops.cb.register_public_input(norm.fld_me);
    ops.cb.register_public_input(norm.fld_de);

    let data = cb.build::<C>();

    use std::time::Instant;
    let now = Instant::now();

    let mut pw = PartialWitness::new();

    let proof = data.prove(pw).unwrap();

    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);

    let pil = proof.public_inputs.len();
    let out = FldFloat4 {
       fld_mf: proof.public_inputs[pil - 4],
       fld_df: proof.public_inputs[pil - 3],
       fld_me: proof.public_inputs[pil - 2],
       fld_de: proof.public_inputs[pil - 1],
     };
    let out_f64 = FldFloat4::into_f64_for_test(&out);
    println!("PI {:#?}", &proof.public_inputs);
    println!("OUT {:#?}", out);
    println!("OUT FROM PROOF {}", out_f64);
    println!("OUT FROM CHECKSUM {}", check_sum as f64);


}

/*
#[test]
fn test_rndsmp_02() {
    use rand::prelude::*;
    let mut rng = rand::thread_rng();
    let config = CircuitConfig::standard_recursion_config();
    let mut cb2 = CircuitBuilder::<F, D>::new(config);

    let elems = 128;
    let mut cb = ();
    let mut ops = Ops::<(), Fld>::new(&mut cb);
    let mut ops2 = Ops::<_, Target>::new(&mut cb2);
    let mut acc1 = FldFloat25([Fld(0); 25]);
    let mut acc2 = 0_f32;
    let mut acc3 = 0_f64;
    let mut acc4 = FldFloat25([ops2.constant(Fld(0)); 25]);
    let mut pubi_a: Vec<(Target, Fld)> = vec![];
    for i in 0..elems {
        let a: f32 = rng.gen();
        let b = ((a * 2.0 - 1.0) * 0.999999999).atanh() * 1.0;
        let c: f32 = rng.gen();
        let d = ((c * 2.0 - 1.0) * 0.999999999).atanh() * 1.0;
        let e = FldFloat3::from_f32(b);
        let f = FldFloat4::from_f32(d);
        let v_fld_f = ops2.cb.add_virtual_target();
        let v_fld_me = ops2.cb.add_virtual_target();
        let v_fld_de = ops2.cb.add_virtual_target();
        pubi_a.push((v_fld_f, e.fld_f));
        pubi_a.push((v_fld_me, e.fld_me));
        pubi_a.push((v_fld_de, e.fld_de));
        let e2 = FldFloat3 {
            fld_f: v_fld_f,
            fld_me: v_fld_me,
            fld_de: v_fld_de,
        };
        let f2 = FldFloat4 {
            fld_mf: ops2.constant(f.fld_mf),
            fld_df: ops2.constant(f.fld_df),
            fld_me: ops2.constant(f.fld_me),
            fld_de: ops2.constant(f.fld_de),
        };
        let g = ops.mul_ibw(e, f);
        let g2 = ops2.mul_ibw(e2, f2);
        let h = b * d;
        acc2 += h;
        acc3 += b as f64 * d as f64;
        acc1 = ops.ibw_add_many([acc1, g]);
        acc4 = ops2.ibw_add_many([acc4, g2]);
    }
    let norm = ops.ibw_norm(&acc1);
    let norm2 = ops2.ibw_norm(&acc4);
    let a = FldFloat4::into_f64_for_test(&norm);
    let b = acc2 as f64;
    //let b = FldFloat4::into_f64_for_test(&FldFloat4::from_f32(acc2));
    println!("RNDSMP2 DIF {a}");
    println!("RNDSMP2 DIF {acc3}");
    println!("RNDSMP2 DIF {b}");

    for i in &pubi_a {
        ops2.cb.register_public_input(i.0);
    }
/*
    for i in 0..25 {
       ops2.cb.register_public_input(acc4.0[i]);
    }
*/

    ops2.cb.register_public_input(norm2.fld_mf);
    ops2.cb.register_public_input(norm2.fld_df);
    ops2.cb.register_public_input(norm2.fld_me);
    ops2.cb.register_public_input(norm2.fld_de);

    //let cb2 = ops2.cb;

    let data = cb2.build::<C>();
    use std::time::Instant;
    let now = Instant::now();

    // Provide initial values.
    let mut pw = PartialWitness::new();
    for i in &pubi_a {
        pw.set_target(i.0, i.1);
    }
    /*
        pw.set_target(norm2.fld_mf, norm.fld_mf);
        pw.set_target(norm2.fld_df, norm.fld_df);
        pw.set_target(norm2.fld_me, norm.fld_me);
        pw.set_target(norm2.fld_de, norm.fld_de + Fld(1));
    */

    let proof = data.prove(pw).unwrap();
    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);

    let pil = proof.public_inputs.len();
    assert_eq!(norm.fld_mf, proof.public_inputs[pil - 4]);
    assert_eq!(norm.fld_df, proof.public_inputs[pil - 3]);
    assert_eq!(norm.fld_me, proof.public_inputs[pil - 2]);
    assert_eq!(norm.fld_de, proof.public_inputs[pil - 1]);

    let comp = proof
        .compress(&data.prover_only.circuit_digest, &data.common)
        .unwrap();

    let proof_bytes = comp.to_bytes();
    println!("PROOF SIZE BYTES {}", proof_bytes.len());

    let proof = CompressedProofWithPublicInputs::from_bytes(proof_bytes, &data.common).unwrap();

    let vres = data.verify_compressed(proof);
    match vres {
        Err(e) => panic!("{}", e),
        Ok(()) => (),
    }
}
*/

#[derive(Debug, Clone)]
pub struct FldFloat3<T> {
    fld_f: T,
    fld_me: T,
    fld_de: T,
}

#[derive(Debug, Clone)]
pub struct FldFloat4<T> {
    fld_mf: T,
    fld_df: T,
    fld_me: T,
    fld_de: T,
}

#[derive(Debug, Clone)]
pub struct FldFloat25<T>([T; 25]);

impl FldFloat3<Fld> {
    pub fn from_f32(fl: f32) -> Self {
        let FldFloat2 { fld_f, fld_e } = FldFloat2::from_f32(fl);
        let mut fe = fld_to_i64(fld_e);

        fe += 149;
        let modu = fe as u64 % 12;
        let fld_me = Fld(modu);
        fe -= modu as i64;
        fe /= 12;
        fe -= 12;
        //println!("MODUCHK {}", fe);
        let fld_de = if fe >= 0 {
            Fld(fe as u64)
        } else {
            Fld(fe.neg() as u64).neg()
        };

        Self {
            fld_f,
            fld_me,
            fld_de,
        }
    }
}

impl FldFloat4<Fld> {
    pub fn from_f32(fl: f32) -> Self {
        let FldFloat3 {
            fld_f,
            fld_me,
            fld_de,
        } = FldFloat3::from_f32(fl);
        let f = fld_to_i64(fld_f);

        let fld_mf = if f >= 0 {
            Fld(f as u64 % SPLIT)
        } else {
            Fld(f.neg() as u64 % SPLIT).neg()
        };
        let fld_df = if f >= 0 {
            Fld(f as u64 / SPLIT)
        } else {
            Fld(f.neg() as u64 / SPLIT).neg()
        };

        Self {
            fld_mf,
            fld_df,
            fld_me,
            fld_de,
        }
    }

    #[cfg(test)]
    pub fn into_f64_for_test(&self) -> f64 {
        let FldFloat4 {
            fld_mf,
            fld_df,
            fld_me,
            fld_de,
        } = self;
        let fld_f = *fld_mf + *fld_df * Fld(1 << 12);
        let fld_e = *fld_me + *fld_de * Fld(12);
        let (sign, m) = if fld_mf.0 < GLHALF {
            (1.0, fld_f.0)
        } else {
            (-1.0, fld_f.neg().0)
        };
        let rexp = if fld_e.0 < GLHALF {
            fld_e.0 as isize
        } else {
            (fld_e.neg().0 as isize).neg()
        };
        sign * (m as f64) * (2.0_f64.powf((rexp - 23 - 5) as f64))
    }
}
