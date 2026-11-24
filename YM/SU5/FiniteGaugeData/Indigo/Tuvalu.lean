import YM.SU5.FiniteGaugeData.Indigo.Brew
import YM.SU5.FiniteGaugeData.LapisQ.Probia
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Indigo
open Function Filter Finset NormedSpace MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Classical
namespace Taper
open LapisQ Apoth Nectar
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (x y:E)(t:ℝ) {z:ℝ}
noncomputable def velum (t x:ℝ):ℝ:= t⁻¹*(1-Real.exp (-t*x))
noncomputable abbrev roseM {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E] (t:ℝ)(x:E):= velum t (‖x‖^2)
variable (h:0<t)
@[fun_prop] lemma velum_C(k:ℕ): ContDiff ℝ (k:WithTop ℕ∞) (velum t):=by unfold velum; fun_prop
@[fun_prop] lemma rose_C : ContDiff ℝ 1 (roseM t (E:=E)):= (velum_C t 1).comp (contDiff_norm_sq ℝ)
lemma velum_c : Continuous (velum t):= (velum_C t 1).continuous
lemma rose_a: Continuous (roseM t (E:=E)):= (rose_C t).continuous
include h
lemma vitaM(u:0≤z) : 0≤ velum t z:= mul_nonneg (inv_pos.mpr h).le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h.le) u)))
lemma vivid(u:0≤z) : velum t z≤ t⁻¹:=mul_le_of_le_one_right (inv_pos.mpr h).le (sub_le_self _ (Real.exp_pos _).le)
lemma slit(u:0≤z): velum t z ≤ z:= by
 let f:= Real.exp (-t*z); have he : -t*z+1≤ f:=Real.add_one_le_exp _; unfold velum; apply le_of_mul_le_mul_left _ h; rw [←mul_assoc,mul_inv_cancel₀ h.ne',one_mul]; linarith only [he]
lemma fee₁(u:0≤z) : z-velum t z≤t*z^2 :=by
 let Q:= t*z; let A:=Real.exp (-Q); have hp:0≤ Q:= mul_nonneg h.le u; have ht:0<Q+1:= add_pos_of_nonneg_of_pos hp zero_lt_one; have hz:A ≤ (Q+1)⁻¹:=by rw [show A= (Real.exp Q)⁻¹ from Real.exp_neg _]; exact inv_anti₀ ht (Real.add_one_le_exp _)
 have hv: (Q+1)⁻¹≤ 1-Q+Q^2:=by apply le_of_mul_le_mul_left _ ht; rw [mul_inv_cancel₀ ht.ne']; nlinarith only [pow_nonneg hp 3]
 unfold velum; apply le_of_mul_le_mul_left _ h; rw [mul_sub,←mul_assoc _ _ (1-Real.exp _),mul_inv_cancel₀ h.ne',one_mul]; rw [show -t*z= -Q from neg_mul ..]; unfold Q at *; nlinarith only [hz.trans hv] -- tune A unfolds
lemma fee₂(u:0≤z): |velum t z-z|≤ t*z^2:=by rw [abs_of_nonpos (sub_nonpos.mpr (slit t h u)),neg_sub]; exact fee₁ t h u
noncomputable abbrev tease :ℝ:=Real.sqrt (2*t)
lemma mentorB : roseM t x= t⁻¹*(1-Apoth.mentor (tease t • x)):=by
 let a:= tease t; have he:(tease t)^2=2*t:=Real.sq_sqrt (by positivity); unfold roseM velum Apoth.mentor; rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,he]; ring_nf
lemma lips₁ : |roseM t x-roseM t y|≤ (t⁻¹*tease t)*‖x-y‖:=by
 let a:= tease t; rw [mentorB x t h, mentorB y t h,←mul_sub]; rw [show (1-mentor (a •x))-(1- mentor (a • y))=mentor (a • y)-mentor (a • x) from (by ring)]; rw [abs_mul,abs_of_pos (inv_pos.mpr h)]; exact (mul_le_mul_of_nonneg_left (mentor_z ..) (inv_pos.mpr h).le).trans_eq (by unfold tease; rw [← smul_sub,norm_smul,Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),norm_sub_rev y x,mul_assoc]) -- name $x t h` type unification? tease.
#print axioms lips₁
open Brew
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable {ι:Type} [Fintype ι] [Nonempty ι] (A B:ι→E) (C:ℝ)
local notation "μ"=> stdGaussian E
abbrev seasonE (t:ℝ)(A:ι→E)(x:E):= velum t (bowl A x)
abbrev dawn (t:ℝ)(A:ι→E):ℝ:= ∫ x:E, seasonE t A x∂ stdGaussian E
abbrev dualC (t:ℝ)(A B:ι→E):ℝ:= ∫ x:E, seasonE t A x * seasonE t B x∂ stdGaussian E
omit h in
@[fun_prop] lemma season_C : Continuous (seasonE t A):=(velum_c t).comp (bowl_C ..)
private lemma peachE : Integrable (bowl A) μ:=by simpa only [pow_one] using! bowlP 1 A
lemma cubit : Integrable (seasonE t A) μ := (peachE t h A).mono' (Continuous.aestronglyMeasurable (season_C t A)) (Eventually.of_forall fun x=> (Real.norm_of_nonneg (vitaM t h (joy A x))).le.trans (slit t h (joy A x)))
lemma pUnit : 0≤ dawn t A := integral_nonneg fun x=> vitaM t h (joy A x)
lemma dawnB : dawn t A ≤ t⁻¹:= (integral_mono (cubit t h A) (integrable_const _) (fun x=>vivid t h (joy A x))).trans_eq (by simp)
lemma tenor : Integrable (fun x:E=> seasonE t A x*seasonE t B x) μ:=by
 let H:=(show Integrable (fun x:E=>bowl A x*bowl B x) μ from (by simpa only [pow_one] using! canvas A B 1 1)); exact H.mono' (by fun_prop) (Eventually.of_forall fun x=> (Real.norm_of_nonneg (mul_nonneg (vitaM t h (joy A x)) (vitaM t h (joy B x)))).le.trans (mul_le_mul (slit t h (joy A x)) (slit t h (joy B x)) (vitaM t h (joy B x)) (joy A x)))
-- product discrepancy. uniform.G. buy covariance up to δ by telescoping.
private lemma priorC(u v:ℝ)(p:0≤u)(w:0≤v): u*v - velum t u*velum t v ≤ t*(u*v^2+u^2*v):=by
 let A:= velum t; change _ - (A u*A v)≤_; have h0:u*(v-A v) ≤ u*(t*v^2):= mul_le_mul_of_nonneg_left (fee₁ t h w) p
 have h1: (u-A u)*A v ≤ (t*u^2)*v:= mul_le_mul (fee₁ t h p) (slit t h w) (vitaM t h w) (by positivity)
 linarith only [h0,h1] -- ring normalized nonlinear powers? linarith normalizations? tune
abbrev ridgeK (ι:Type)[Fintype ι](C:ℝ):=postage ι 2 C+postage ι 4 C
abbrev genial (ι:Type)[Fintype ι](C:ℝ):= 2*ridgeK ι C
variable (C₀:0≤C)(p₁:∀ i,‖A i‖ ≤ C) (p₂:∀ i,‖B i‖ ≤ C)
omit h in
lemma gen_p : 0 ≤ C → 0≤ genial ι C:= fun u=> by
      apply mul_nonneg zero_le_two (add_nonneg (post_p _ _ u) (post_p _ _ u)) -- shape
include p₁ p₂
lemma thrift : Nir A B - (dualC t A B - dawn t A*dawn t B) ≤ t*genial ι C:= by
 rw [← sigma₂]; let f:= bowl A; let g:=bowl B; let f':= seasonE t A; let g':=seasonE t B; let Q(r:ℝ):= velum t r; let F(x):= f x*g x^2; let G(x):=f x^2*g x; have hT: (∫ x:E,F x∂μ) ≤ ridgeK ι C ∧ Integrable F μ:=by
    have he:Integrable (fun x=> bowl A x^1*bowl B x^2) μ:= canvas ..; simp only [pow_one] at he; refine ⟨?_,he⟩; simpa only [pow_one,Nat.reduceMul,ridgeK] using! canv_B 1 2 A B C p₁ p₂
 have hg: (∫ x:E,G x∂μ) ≤ ridgeK ι C ∧ Integrable G μ:=by
    have he:Integrable (fun x=> bowl A x^2*bowl B x^1) μ:= canvas ..; simp only [pow_one] at he; refine ⟨?_,he⟩; have ht':= canv_B 2 1 A B C p₁ p₂; unfold ridgeK; rw [add_comm (postage ι 2 C)]; simpa only [pow_one,Nat.reduceMul] using! ht'
 have hh: (∫ x:E, f x*g x∂μ)-dualC t A B ≤ t* genial ι C:=by
    unfold dualC; rw [← integral_sub (show Integrable (fun x:E => f x*g x) μ from (by simpa only [pow_one] using! canvas A B 1 1)) (tenor t h A B)]; let Y' := fun x=> t*(F x+G x); have hl:Integrable Y' μ:= (hT.2.add hg.2).const_mul _; apply (integral_mono (_ : Integrable _ _) hl (fun x=> priorC t h _ _ (joy A x) (joy B x))).trans; unfold Y'; rw [integral_const_mul,integral_add hT.2 hg.2]; exact mul_le_mul_of_nonneg_left ((add_le_add hT.1 hg.1).trans_eq (two_mul ..).symm) h.le
    exact (show Integrable (fun x:E=> f x*g x) μ from (by simpa only [pow_one] using! canvas A B 1 1)).sub (tenor t h A B)
 have he(A:ι→E):dawn t A ≤ ∫ x:E,bowl A x∂μ:= integral_mono (cubit t h A) (peachE t h A) fun x=> slit t h (joy ..)
 have hv:=mul_le_mul (he A) (he B) (pUnit t h B) ((pUnit t h A).trans (he A)); linarith only [hv,hh]
#print axioms thrift
end Taper
end YM.SU5.FiniteGaugeData.Indigo
