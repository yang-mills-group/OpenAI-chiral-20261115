import YM.SU5.Relativistic.Ghats
import Mathlib.MeasureTheory.Integral.Pi
/-! # spatial sampling over actual angular lattice. Triangle to land inside<br> support. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=> 2 * Real.pi
local notation "Φ"=> Set.Icc (-π) π
attribute [local instance] screen_fin

variable (d:ℕ)(r:ℝ)(p:0<d)
abbrev dropH (d:ℕ):ℝ:=2*π/d
def hornA (r:ℝ)(d:ℕ)(x:ℝ):ℝ:= max 0 (1 - |x-(r+dropH d)|/dropH d)
@[fun_prop] lemma hornA_c : Continuous (hornA r d):=by unfold hornA; fun_prop
local notation "u"=>dropH d
private lemma eToe (n:ℤ)(a b:ℝ)(q:n≠0) :
    (∫ t in a..b,surge n t) = (surge n b-surge n a)/(Complex.I*n):=by
 let z:=(Complex.I*n); have he:z≠0:=mul_ne_zero Complex.I_ne_zero (by exact_mod_cast q)
 rw [show surge (↑n:ℝ)=(fun t:ℝ=> Complex.exp (z*(t:ℂ))) from funext fun t=> by unfold z surge; push_cast; ring_nf, integral_exp_mul_complex he]
include p
lemma rung_pos:0<dropH d:=by unfold dropH; positivity
lemma hornA_off {x:ℝ}(h:x ∉ Set.Ioo r (r+u+u)): hornA r d x=0:=by
 unfold hornA; refine max_eq_left (sub_nonpos.mpr ((one_le_div (rung_pos d p)).2 ?_)); by_cases ht:x≤r; · linarith [neg_le_abs (x-(r+u))]
 have hx:r+u+u ≤ x:= le_of_not_gt (fun e=>h ⟨lt_of_not_ge ht,e⟩)
 linarith only [hx, le_abs_self (x-(r+u))]
lemma hornA_mid {x:ℝ}(h:x∈ Set.Ioc r (r+u)) : hornA r d x+ hornA r d (x+u)=1:=by
 unfold hornA; rw [abs_of_nonpos (sub_nonpos.mpr h.2), abs_of_nonneg (by linarith only [h.1]:0 ≤ x+u- (r+u)),max_eq_right ?_,max_eq_right ?_]; rotate_left
 · exact sub_nonneg.mpr ((div_le_one (rung_pos d p)).2 (by linarith only [h.2])) -- order
 · exact sub_nonneg.mpr ((div_le_one (rung_pos d p)).2 (by linarith only [h.1]))
 field_simp [(rung_pos d p).ne']; ring
private lemma eToe_p (n:ℤ)(x:ℝ): surge ((d*n:ℤ):ℝ) (x+u)=surge ((d*n:ℤ):ℝ) x:=by
 rw [surge_right, show surge (↑(d*n:ℤ):ℝ) u=Complex.exp ((n:ℂ)*(2*Real.pi*Complex.I)) from ?_,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow,mul_one]
 have he: (d:ℂ)≠0:=by exact_mod_cast p.ne'
 unfold surge dropH; push_cast; field_simp
variable {r d}
lemma hornA_rim (ht:-π<r)(hv:r+u+u<π)(n:ℤ) : pluse (d*n) (fun x=> (d:ℂ)*(hornA r d x:ℂ))= if n=0 then (↑(φ:ℝ):ℂ) else 0:=by
 let f(x:ℝ):ℂ:= surge ((d*n:ℤ):ℝ) x *(↑(hornA r d x):ℂ)
 have he:Continuous f:= (surge_cont.comp (continuous_const.prodMk continuous_id)).mul (Complex.continuous_ofReal.comp (hornA_c d r))
 have hi (x y:ℝ):IntervalIntegrable f volume x y:= he.intervalIntegrable _ _
 have hu:=rung_pos _ p; let a:=r+u
 have hx(a b:ℝ)(hp:a≤b)(e:∀ x∈ Set.Ioc a b,x∉ Set.Ioo r (r+u+u)): (∫x in a..b,f x)=0:=by rw [intervalIntegral.integral_of_le hp]; exact setIntegral_eq_zero_of_forall_eq_zero fun x v=> by unfold f; rw [hornA_off d r p (e x v),Complex.ofReal_zero,mul_zero]
 have hw : (∫ t in screen, f t)=∫ t in r..r+u,surge (↑(d*n:ℤ):ℝ) t:=by
    rw [screen,←intervalIntegral.integral_of_le (by linarith [pi_pos]:-π≤π), ← intervalIntegral.integral_add_adjacent_intervals (hi (-π) r) (hi r π), hx _ _ ht.le (fun x v e=> e.1.not_ge v.2), zero_add, ← intervalIntegral.integral_add_adjacent_intervals (hi r (a+u)) (hi _ π), hx _ _ hv.le (fun x v e=> e.2.not_ge v.1.le), add_zero,← intervalIntegral.integral_add_adjacent_intervals (hi r a) (hi a _),←intervalIntegral.integral_comp_add_right f u]
    rw [←intervalIntegral.integral_add (hi r a) (show IntervalIntegrable (fun x=> f (x+u)) volume r a from (he.comp (continuous_id.add continuous_const)).intervalIntegrable r a), intervalIntegral.integral_of_le (show r≤a by unfold a; linarith), intervalIntegral.integral_of_le (show r≤r+u by linarith)]; apply setIntegral_congr_fun measurableSet_Ioc; intro x v; change f x+f (x+u)=_
    unfold f; rw [eToe_p d p,←mul_add,←Complex.ofReal_add,hornA_mid d r p v,Complex.ofReal_one,mul_one] -- order
 rw [pluse_const]; unfold pluse; rw [hw]; -- pattern f
 by_cases t:n=0
 · subst n; simp [dropH,intervalIntegral.integral_const,Complex.real_smul]; have hg:(d:ℂ)≠0:=by exact_mod_cast p.ne'
   field_simp
 rw [if_neg t, eToe _ _ _ (mul_ne_zero (by exact_mod_cast p.ne') t),eToe_p d p,sub_self,zero_div,mul_zero]
end YM.CF.Crest.Sleet
