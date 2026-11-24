import YM.SU5.Reconstruction.Anvil.Bay
import YM.SU5.Reconstruction.Trap.Ray
/-! # Momentum chamber affine arithmetic. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric MeasureTheory InnerProductSpace Spectral OS Semigroup ConePrice
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators
-- distinguish ℝ costs. E4 and Pi coordinates
abbrev Meter := Axis→ℝ
abbrev Wage := Axis→ℂ
abbrev RealAge (p:Wage):Meter:= fun i=>(p i).re
abbrev Deeper (p:Wage):Meter:= fun i=>(p i).im
def facet (p:Meter): Wage := fun i=>p i
@[simp] lemma facet_apply (p:Meter)(i:Axis): facet p i=p i:=rfl
abbrev onlyTime {X:Type*}[Zero X](i:Axis)(x:X) : Axis→X:= Pi.single i x
@[simp] lemma facet_t (a:Axis)(x:ℝ): facet (onlyTime a x)= onlyTime a (x:ℂ):=by ext i; by_cases p:i=a<;>simp [onlyTime,p]
lemma single_compensate {X:Type*}[AddCommGroup X](a:Axis)(x y:X): onlyTime a (x+y)= onlyTime a x+ onlyTime a y:=by ext i; by_cases p:i=a<;>simp [onlyTime,p]
lemma single_negate {X:Type*}[AddCommGroup X](a:Axis)(x:X): onlyTime a (-x)= -onlyTime a x:=by ext i; by_cases p:i=a<;>simp [onlyTime,p]
lemma single_steal {X:Type*}[AddCommGroup X](a:Axis)(x y:X): onlyTime a (x-y)= onlyTime a x- onlyTime a y:=by simp only [sub_eq_add_neg, single_compensate, single_negate]
@[simp] lemma facet_zero : facet 0=0:= rfl -- not?
@[simp] lemma facet_add (x y:Meter): facet (x+y)= facet x+facet y:=by ext; simp
@[simp] lemma facet_neg (x:Meter): facet (-x)= -facet x:=by ext; simp
@[simp] lemma facet_sub (x y:Meter): facet (x-y)= facet x-facet y:= by simp only [sub_eq_add_neg,facet_add,facet_neg]
@[simp] lemma discounts (x:Meter): RealAge (facet x)=x:= rfl
@[simp] lemma grace (x:Meter): Deeper (facet x)=0:= rfl
@[simp] lemma deeper_add (x y:Wage): Deeper (x+y)= Deeper x+ Deeper y:=rfl
@[simp] lemma deeper_neg (x:Wage): Deeper (-x)= -Deeper x:=rfl
@[simp] lemma deeper_sub (x y:Wage): Deeper (x-y)=Deeper x-Deeper y:=rfl
local notation "ĥ" => WithLp.toLp 2
abbrev rimPay (a:Axis)(x:Meter):= SEP a (WithLp.toLp 2 x)
lemma rimPay_at (a:Axis)(x:Meter)(i:Axis)(u:i≠a): (rimPay a x).val i=x i:=by change ((ĥ x-(x a) • basis a : E4) i)=_; simp [u]
lemma rimPay_norm (a:Axis)(x:Meter): ‖rimPay a x‖^2=∑ i∈ Finset.univ.erase a,x i^2:= by
 rw [rimPay,sep_size, ←real_inner_self_eq_norm_sq,PiLp.inner_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)] -- names
 simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]; exact add_sub_cancel_right ..
@[simp] lemma rimPay_zero (a:Axis): rimPay a 0=0:=by unfold rimPay; rw [WithLp.toLp_zero, map_zero]
@[simp] lemma rimPay_add (a:Axis)(x y : Meter): rimPay a (x+y)=rimPay a x+rimPay a y:= by unfold rimPay; rw [WithLp.toLp_add,map_add]
@[simp] lemma rimPay_smul (a:Axis)(p:ℝ)(x:Meter): rimPay a (p • x)= p • rimPay a x:= by unfold rimPay; rw [WithLp.toLp_smul,map_smul]
@[simp] lemma rimPay_neg (a:Axis)(x:Meter): rimPay a (-x) = -rimPay a x := by unfold rimPay; rw [WithLp.toLp_neg,map_neg]
@[simp] lemma rimPay_sub (a:Axis)(x y:Meter) : rimPay a (x-y)= rimPay a x-rimPay a y:= by rw [sub_eq_add_neg x,rimPay_add,rimPay_neg, sub_eq_add_neg]
@[simp] lemma only_pay (a:Axis)(x:ℝ) : rimPay a (onlyTime a x)=0:= by
 ext i; by_cases p:i=a; · subst i; change _=0; exact ((rimPay a (onlyTime a x)).property : (rimPay a (onlyTime a x)).val a=0)
 change (rimPay a (onlyTime a x)).val i = (0:E4) i; rw [rimPay_at a _ i p]; simp [onlyTime,p]
@[simp] lemma parcel (p:E4)(a:Axis)(x:Meter): inner ℝ p (rimPay a x).val= ∑ i∈ Finset.univ.erase a,x i*p i:= by
 rw [PiLp.inner_apply,← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
 simp only [RCLike.inner_apply,conj_trivial] -- try
 rw [show (rimPay a x).val.ofLp a=0 from (rimPay a x).property, zero_mul, add_zero]; exact Finset.sum_congr rfl (fun t h=> congrArg (· * p t) (rimPay_at a x t (Finset.ne_of_mem_erase h)))
@[fun_prop] lemma c_r (a:Axis): Continuous (rimPay a):= by unfold rimPay; fun_prop
@[fun_prop] lemma c_f:Continuous facet:= continuous_pi fun _=>by unfold facet; fun_prop
lemma c_x:Continuous RealAge:=continuous_pi fun _=>by unfold RealAge; fun_prop
lemma c_y:Continuous Deeper:=continuous_pi fun _=>by unfold Deeper; fun_prop
lemma only_agree (a:Axis)(x:ℂ): Deeper (onlyTime a x)= onlyTime a x.im:= by ext i; by_cases p:i=a<;>simp [Deeper,onlyTime,p]
abbrev Tunnel (a:Axis): Set Wage := {Z | ‖rimPay a (Deeper Z)‖ < (Z a).re}
abbrev Loan (a:Axis)(Z:Wage): Prop := ‖rimPay a (Deeper Z)‖ ≤ (Z a).re
lemma tunnel_open (a:Axis): IsOpen (Tunnel a):= isOpen_lt ((c_r a|>.comp c_y).norm) (Complex.continuous_re.comp (continuous_apply a))
@[simp] lemma tunnel_initial (a:Axis)(x:Meter): facet x∈ Tunnel a ↔ 0<x a := by simp [Tunnel]
lemma loan_initial (a:Axis)(x:Meter): Loan a (facet x) ↔ 0 ≤ x a:= by simp [Loan]
@[simp] lemma tunnel_invoice (a:Axis)(x:ℂ): onlyTime a x∈ Tunnel a ↔0<x.re:= by simp [Tunnel,only_agree,only_pay,onlyTime]
lemma tunnel_re (a:Axis)(q:Wage)(p:q∈ Tunnel a): 0 < (q a).re:= lt_of_le_of_lt (norm_nonneg _) p
end YM.Anvil
