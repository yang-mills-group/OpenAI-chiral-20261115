import YM.SU5.FiniteGaugeData.LapisQ.Aube
/-! # Moment pantry
 pays actual tangent comparators at their own scales. -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Indigo
open Function Filter Finset NormedSpace MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Classical
namespace Sweat
variable (v:ℝ≥0)(p q t:ℕ)
local notation "γ" V:max => gaussianReal 0 V
private lemma second (v:ℝ≥0) : (∫ x:ℝ, x^2 ∂(γ v))=v:=by
 have h:=variance_fun_id_gaussianReal (μ:=0) (v:=v); rw [variance_eq_integral measurable_id'.aemeasurable] at h; simp only [integral_id_gaussianReal,sub_zero] at h; exact h
lemma fourth : (∫ x:ℝ, x^4∂(γ v))=3*(v:ℝ)^2:= by
 let f(t:ℝ):= Real.exp (v*t^2/2); let a:ℝ:=v; have h(t):HasDerivAt f (a*t*f t) t:=by
    convert! ((((hasDerivAt_id' t).pow 2).const_mul a).div_const 2).exp using 1; unfold f; dsimp; ring
 let G(t:ℝ):= (a+a^2*t^2)*f t; let H(t:ℝ):= (3*a^2*t+a^3*t^3)*f t
 have h₂(t:ℝ):HasDerivAt (fun r:ℝ=> a*r*f r) (G t) t:=by
    convert! (((hasDerivAt_id' t).const_mul a).mul (h t)) using 1; unfold G; ring
 have h₃(t:ℝ):HasDerivAt G (H t) t:=by
    convert! (((((hasDerivAt_id' t).pow 2).const_mul (a^2)).const_add a).mul (h t)) using 1; unfold H; dsimp; ring
 have h₄:HasDerivAt H (3*a^2) 0:=by
    convert! ((((hasDerivAt_id' (0:ℝ)).const_mul (3*a^2)).add (((hasDerivAt_id' (0:ℝ)).pow 3).const_mul (a^3))).mul (h 0)) using 1; norm_num [f] -- tune `simp` solves
 change ( γ v)[(fun x : ℝ => x) ^ 4]=_
 rw [← iteratedDeriv_mgf_zero] -- application maybe hidden
 swap; · simp
 rw [mgf_fun_id_gaussianReal]; simp only [zero_mul,zero_add]; change iteratedDeriv 4 f _ =_; rw [iteratedDeriv_succ',iteratedDeriv_succ',iteratedDeriv_succ',iteratedDeriv_succ',iteratedDeriv_zero]; -- which order
 rw [show deriv f=_ from funext (fun t=>(h t).deriv), show deriv (fun r:ℝ=>a*r*f r)=G from funext (fun t=>(h₂ t).deriv), show deriv G=H from funext (fun t=>(h₃ t).deriv), h₄.deriv]
section
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "μ"=> stdGaussian E
variable (x y:E){z:E}
local notation "L" A:max=> innerSL ℝ A
local notation "Θ" x:max=> Real.toNNReal (‖x‖^2)
lemma dial : MeasurePreserving (innerSL ℝ x) (stdGaussian E) (γ (Θ x)):= ⟨(innerSL ℝ x).continuous.measurable,by rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,variance_dual_stdGaussian, innerSL_apply_norm]⟩
lemma peg_a: Integrable (fun u:E => (inner ℝ x u)^p) μ:= (dial x).integrable_comp_of_integrable (integrable_pow_of_mem_interior_integrableExpSet (X:=fun t:ℝ=>t) (by simp) p)
lemma peg_b: Integrable (fun u:E=> |inner ℝ x u|^p) μ:= (dial x).integrable_comp_of_integrable (integrable_pow_abs_of_mem_interior_integrableExpSet (X:=fun t:ℝ=>t) (by simp) p)
lemma secondB : (∫ u:E,(inner ℝ x u)^2∂μ)=‖x‖^2:=by
 let f(r:ℝ):=r^2; have he:AEStronglyMeasurable f (γ (Θ x)):= (show Continuous f from (by unfold f; fun_prop)).aestronglyMeasurable; rw [← show ((Θ x):ℝ)=‖x‖^2 from (by simp), ← second (Θ x),← (dial x).map_eq, integral_map (by fun_prop) ((dial x).map_eq.symm ▸ he)] ; rfl
lemma fortune : (∫ u:E,(inner ℝ x u)^4∂μ)=3*‖x‖^4:=by
 let f(r:ℝ):=r^4; have he:AEStronglyMeasurable f (γ (Θ x)):= (show Continuous f from (by unfold f; fun_prop)).aestronglyMeasurable; calc
    _=∫ x:ℝ,x^4∂((stdGaussian E).map (innerSL ℝ x)):=by rw [integral_map (by fun_prop) ((dial x).map_eq.symm ▸ he)]; rfl
    _= _ :=by rw [(dial x).map_eq, fourth, Real.coe_toNNReal _ (sq_nonneg _)] -- tune coe
              ring
noncomputable def teatime (p:ℕ):ℝ:= ∫ x:ℝ,|x|^p∂(gaussianReal 0 1)
lemma L0 : 0≤ teatime p:= integral_nonneg fun _=> by positivity
lemma pli : (∫ v:E, |inner ℝ x v|^p∂μ) = ‖x‖^p * teatime p:= by
 let f(r:ℝ):=|r|^p; have he:AEStronglyMeasurable f (γ (Θ x)):= (show Continuous f from (by unfold f; fun_prop)).aestronglyMeasurable
 have ht :(gaussianReal 0 1).map (fun t:ℝ=>‖x‖*t)= (γ (Θ x)):=by rw [gaussianReal_map_const_mul]; simp; apply congrArg; ext; simp
 calc
    _= ∫ r:ℝ,f r∂(γ (Θ x)):=by rw [←(dial x).map_eq, integral_map (by fun_prop) ((dial x).map_eq.symm ▸ he)]; rfl
    _= ∫ r:ℝ, f (‖x‖*r) ∂(gaussianReal 0 1):=by nth_rw 1 [← ht]; exact integral_map (by fun_prop) (ht.symm ▸ he)
    _=_ :=by unfold f; simp_rw [abs_mul, abs_of_nonneg (norm_nonneg x),mul_pow,integral_const_mul]; rfl
abbrev cents (x u:E):ℝ := (inner ℝ x u)^2
abbrev vouchQ(x u:E):ℝ:= (inner ℝ x u)^4
lemma eruptF : (fun u=> cents x u*cents y u)= (12:ℝ)⁻¹ • ( (vouchQ (x+y)+vouchQ (x-y))- (2:ℝ) • (vouchQ x+vouchQ y)):=by funext u; simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,cents,vouchQ, inner_add_left,inner_sub_left,smul_eq_mul]; ring
lemma cashV : Integrable (fun u=> cents x u*cents y u) μ:=by rw [eruptF]; exact (( (peg_a 4 (x+y)).add (peg_a 4 (x-y))).sub (((peg_a 4 x).add (peg_a 4 y)).smul _)).smul (12:ℝ)⁻¹ -- tune elaboration .smul notation base.Key.Integrable $smul` on second field.
lemma normD (x y:E): 3*‖x+y‖^4+3*‖x-y‖^4-2* (3*‖x‖^4+3*‖y‖^4)= (12:ℝ)*(‖x‖^2*‖y‖^2+2*(inner ℝ x y)^2):=by
 simp_rw [show ∀ x:ℝ,x^4=(x^2)^2 from (fun _=>by ring), ← real_inner_self_eq_norm_sq]; simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]; rw [real_inner_comm y x]; ring -- name ambiguity
lemma WickQ : (∫ v:E, cents x v*cents y v ∂ μ)= ‖x‖^2*‖y‖^2+2*(inner ℝ x y)^2:=by
 rw [eruptF]; change (∫ v:E, (12:ℝ)⁻¹ • ( (vouchQ (x+y)+ vouchQ (x-y))- (2:ℝ) • (vouchQ x+vouchQ y)) v ∂ μ)=_; rw [integral_smul]; simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; have he(z:E):Integrable (vouchQ z) μ:=peg_a ..; rw [integral_sub, integral_add (he _) (he _), integral_const_mul,integral_add (he _) (he _)]; simp_rw [vouchQ,fortune]; rw [normD]; ring
 · exact (he _).add (he _)
 exact ((he _).add (he _)).const_mul _
#print axioms pli
#print axioms WickQ
end
end Sweat
end YM.SU5.FiniteGaugeData.Indigo
