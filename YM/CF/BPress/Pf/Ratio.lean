import YM.CF.BPress.Pf.Recursive
import YM.CF.BPress.Pf.Rotate
/-! Straight-line for the logarithm after isolation of its actual initial phase. Keep orientation of ket derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter Finset NormedSpace Fock Spin MeasureTheory Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{A B:ℝ→Wave I} {x y v: Wave I} {a b c r:ℝ}{T:Op I}
namespace Bridge
lemma rift {f g:ℝ→ℂ}(p:ContinuousOn g (Icc a b))(h:∀ x∈ Icc a b,HasDerivAt f (f x*g x) x)(u:a≤b) : f b= f a* Complex.exp (∫ x in a..b, g x):=by
 let D(x):=∫ t in a..x, g t; let F(x):= Complex.exp (-D x)*f x; have hg:IntegrableOn g (Icc a b):= p.integrableOn_Icc
 have he: ContinuousOn D (Icc a b):= (intervalIntegral.continuousOn_primitive hg).congr (fun i hi=> intervalIntegral.integral_of_le hi.1)
 have ht: ContinuousOn (fun x=>f x) (Icc a b):=fun x hx=>(h x hx).continuousAt.continuousWithinAt
 have hp:ContinuousOn F (Icc a b):=he.neg.cexp.mul ht
 have hm:∀ x∈ Ioo a b,HasDerivWithinAt F 0 (Ioi x) x:=by
    intro x hX; have hP:x∈Icc a b:= Ioo_subset_Icc_self hX; have hC:=p.mono Ioo_subset_Icc_self; have hh : IntervalIntegrable g MeasureTheory.volume a x:= by rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hP.1]; exact hg.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hP.2))
    have hz := ((intervalIntegral.integral_hasDerivAt_right hh (hC.stronglyMeasurableAtFilter isOpen_Ioo x hX) (p.continuousAt (Icc_mem_nhds hX.1 hX.2))).neg.cexp.mul (h x hP)).hasDerivWithinAt (s:=Ioi x)
    apply hz.congr_deriv; ring
 have hz := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le u hp hm (f':=fun _=> (0:ℂ)) (by simp)
 have hl:F b=F a:= sub_eq_zero.mp (hz.symm.trans (by simp)); unfold F at hl; rw [show D a=0 from intervalIntegral.integral_same, neg_zero, Complex.exp_zero,one_mul] at hl; rw [← hl]; unfold D; rw [Complex.exp_neg]; field_simp

-- Core trace matrices on the unconditioned Wick endpoint at each parameter. S=W=∅, L=1. Include powers. For bra paths der pair-waves:
def seedM (A T C:Op I) := T * (contextM (cutM ∅) (cutM ∅) 1 A C 1 0 0 1)ᵀ
def dinoM (A T C:Op I):= (2:ℂ)⁻¹ • (star T*(contextM (cutM ∅) (cutM ∅) 1 A C 0 1 0 1)ᵀ)

lemma pays_right {C P: Op I}(b:Bore P C r)(u:Top P v): wick (pairWave C) v (dg T)=(seedM P T C).trace:= by simpa only [pureE,seedM] using bare (Arrange.regular b) u T
lemma pays_left {C P: Op I}(b:Bore P C r)(u:Top P v): wick (pairWave C) v (star (coupl T))=(dinoM P T C).trace:= by simpa only [dinoM,pureE,Matrix.trace_smul,smul_eq_mul] using couple (Arrange.regular b) u T
lemma dgC: Continuous (dg (n:=I)):= by unfold dg dyad; fun_prop
lemma crossing (p:a≤b)(Y:ℝ→Op I)(C:Op I)(g:ContinuousOn Y (Icc a b))(D:ℝ→Op I)(s:∀ x∈Icc a b,Bore (D x) C c)(h:∀ x∈Icc a b,Top (D x) (A x))(v:∀ x∈Icc a b, HasDerivAt A (acts (dg (Y x)) (A x)) x):
 inner ℂ (pairWave C) (A b)= inner ℂ (pairWave C) (A a)*Complex.exp (∫ x in a..b,(seedM (D x) (Y x) C).trace):=by
 let f:=fun x=>inner ℂ (pairWave C) (A x); let t:=fun x=>wick (pairWave C) (A x) (dg (Y x)); have hA(x)(p:x∈ Icc a b):t x=(seedM (D x) (Y x) C).trace:=pays_right (T:=Y x) (s x p) (h x p); have hx : ContinuousOn A (Icc a b):= fun x p=>(v x p).continuousAt.continuousWithinAt; have hz:ContinuousOn t (Icc a b):= ContinuousOn.div (continuousOn_const.inner (((acts_cont.comp dgC).comp_continuousOn g).clm_apply hx)) (continuousOn_const.inner hx) (fun x p=>(s x p).cleanA (h x p))
 rw [← intervalIntegral.integral_congr (show EqOn t (fun x=>_) (uIcc a b) from (by rw [uIcc_of_le p]; exact fun x hx=> hA x hx))]; apply rift (f:=f) hz _ p; intro x hX; refine ((hasDerivAt_const x (pairWave C)).inner ℂ (v x hX)).congr_deriv ?_; unfold f t wick; rw [inner_zero_left,add_zero]; field_simp [(s x hX).cleanA (h x hX)]
lemma passing (p:a≤b)(T:Op I)(h:Top T v)(C D:ℝ→Op I)(u:ContinuousOn D (Icc a b))(s:∀ x∈ Icc a b, HasDerivAt C (D x) x)(g:∀ x∈Icc a b,Bore T (C x) c) : inner ℂ (pairWave (C b)) v=inner ℂ (pairWave (C a)) v*Complex.exp (∫ x in a..b,(dinoM T (D x) (C x)).trace):=by
 let f:=fun x=>inner ℂ (pairWave (C x)) v; let t:=fun x=>wick (pairWave (C x)) v (star (coupl (D x))); have he(x)(p:x∈ Icc a b): t x=(dinoM T (D x) (C x)).trace:=pays_left (T:=D x) (g x p) h; have hC:ContinuousOn (fun x=>pairWave (C x)) (Icc a b):= fun x p=> (Rotate.d_pair (s x p)).continuousAt.continuousWithinAt; have ht:ContinuousOn t (Icc a b):= hC.inner (((acts_cont.comp_continuousOn ((coupl_cont.comp_continuousOn u).star)).clm_apply continuousOn_const)) |>.div (hC.inner continuousOn_const) (fun x p=>(g x p).cleanA h)
 rw [←intervalIntegral.integral_congr (show EqOn t (fun x=>_) (uIcc a b) from (by rw [uIcc_of_le p]; exact fun x hx=> he x hx))]; apply rift (f:=f) ht _ p; intro x hx; have hh := (Rotate.d_pair (s x hx)).inner ℂ (hasDerivAt_const x v); simp only [inner_zero_right,zero_add] at hh; refine hh.congr_deriv ?_; unfold f t wick; rw [←act_inner,star_star]; field_simp [(g x hx).cleanA h]
end Bridge
end YM.CF.BPress.Pf
