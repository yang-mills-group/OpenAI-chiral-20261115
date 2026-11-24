import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 320000
open Set Filter
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace GarnetAct
variable {A B:ℂ}{C d ε σ V:ℝ}
-- convex cost. unify sign selection notation. preserve normalized fields.IC.
def mood (V:ℝ):ℝ:= if V≥0 then 1 else -1
lemma mood_abs : |mood V|=1:=by unfold mood; split_ifs<;> norm_num
lemma mood_pay : mood V * V=|V|:=by
 unfold mood; split_ifs with h
 · rw [one_mul,abs_of_nonneg h]
 · rw [abs_of_nonpos (le_of_not_ge h), neg_one_mul]
lemma reflect_bounds(p:A.re ≥ C)(f:0 < σ)(u:‖B-(↑σ:ℂ)*2*V*A‖≤ σ* |V| * C): mood V * B.re ≥ σ*|V| *C:=by
 let t:= mood V; have ht: |B.re- σ*2*V*A.re| ≤ σ*|V| *C:=by
    refine le_trans (?_ : _ ≤ ‖B-(↑σ:ℂ)*2*V*A‖) u
    convert Complex.abs_re_le_norm (B-(↑σ:ℂ)*2*V*A) using 1; simp [Complex.mul_re]
 have hu:= abs_le.mp ht; unfold mood; split_ifs with h; · rw [abs_of_nonneg h] at *; linarith only [h,hu,mul_le_mul_of_nonneg_left p (show 0 ≤ σ * V from mul_nonneg f.le h)] -- replaced ht or hu etc
 · have h':=lt_of_not_ge h; rw [abs_of_nonpos h'.le] at *; linarith only [h',hu,mul_le_mul_of_nonpos_left p (show σ * V ≤ 0 from mul_nonpos_of_nonneg_of_nonpos f.le h'.le)]
lemma proofDesk {α:Type*}[MeasurableSpace α](μ:Measure α)[IsProbabilityMeasure μ] (g: Fin 4→ Bool→ α→ ℝ)(h:∀ i b,Integrable (g i b) μ)(c:ℝ)(H:0<c){V:ℝ} (p:∀ᵐ x∂μ, c ≤ mood V*∑ i:Fin 4,(g i true x-g i false x)):
 ∃ (i:Fin 4)(b:Bool), c/8≤ |∫ x, g i b x ∂μ|:=by
 let u i:= fun b=> ∫ x,g i b x∂μ; let W:= mood V; let z(i:Fin 4)(x:α):= g i true x-g i false x; let Z(x:α):=∑ i,z i x; have hz(i: Fin 4):Integrable (z i) μ:=(h i true).sub (h i false); let f:= W • Z; have h0 : Integrable Z μ := integrable_finsetSum _ fun _ _=>hz _; have hF: c≤ ∫ x,f x ∂μ:=by simpa [f] using (integral_mono_ae (integrable_const c) (h0.smul W) (show ∀ᵐ x∂μ,c≤f x from p))
 have hw: ∫ x,f x∂μ=∑ i,W*(u i true-u i false):=by
    change ∫ x,W • Z x∂μ= _; unfold Z; rw [integral_smul, integral_finsetSum _ (fun i _=>hz i), Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [show ∫ x,z i x∂μ=u i true-u i false from integral_sub (h i true) (h i false)]; rfl -- tune
 rw [hw] at hF; by_contra! hc; have hf(i: Fin 4): W* (u i true-u i false) < c/4:=by
    refine (le_abs_self _).trans_lt ?_; rw [abs_mul,mood_abs,one_mul]; have e:= abs_sub (u i true) (u i false); exact e.trans_lt (by linarith only [hc i true,hc i false]) -- name abs_sub? check
 exact (not_lt_of_ge hF) ((Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _=>hf i)).trans_eq (by simp; ring))
lemma presence {α:Type*} [MeasurableSpace α](μ:Measure α)[IsProbabilityMeasure μ](f:α→ℝ)(h:Integrable f μ)(c:ℝ)(e:0<c)(p:c ≤ |∫ x,f x ∂μ|) : ∃ᶠ x in ae μ,c/2 ≤ mood (∫ x,f x∂μ)* f x :=by
 let i:= ∫ x,f x∂μ; let z:=mood i; by_contra! w -- syntax by_contra! turns ∀? triggers push.
 have hG: (∫ x,z*f x∂μ)≤ c/2:=by simpa [z,i] using integral_mono_ae (h.const_mul _) (integrable_const (μ:=μ) (c/2)) (w.mono fun _ h=>h.le)
 rw [integral_const_mul] at hG; change mood i * i ≤ _ at hG; rw [mood_pay] at hG; linarith only [p,e,hG]
end GarnetAct
