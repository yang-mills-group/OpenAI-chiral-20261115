import YM.SU5.FiniteGaugeData.Indigo.Sweat
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Indigo
open Function Filter Finset NormedSpace MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Classical
namespace Brew
variable (v:ℝ≥0)(p q t:ℕ)
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "μ"=> stdGaussian E
open Sweat YM.SU5.FiniteGaugeData.LapisQ Apoth
variable {ι:Type} [Fintype ι] [Nonempty ι] (A B:ι→E) (C:ℝ)
local notation "τ"=> (Fintype.card ι:ℝ)
abbrev bowl (A:ι→E)(x:E):= ‖opus A x‖^2
lemma joy(x:E): 0≤ bowl A x:=sq_nonneg _
@[fun_prop] lemma bowl_C: Continuous (bowl A):= ((opus A).continuous.norm).pow _
lemma pie(x:E): bowl A x=∑ i:ι,cents (A i) x:= EuclideanSpace.real_norm_sq_eq _ -- tune
abbrev shade_p (A:ι→E)(p:ℕ)(x:E):ℝ:= (Fintype.card ι:ℝ)^p *∑ i:ι,|inner ℝ (A i) x|^(2*p)
lemma shapeP (x:E): (bowl A x)^p ≤ shade_p A p x:=by
 let f(i:ι):= (inner ℝ (A i) x)^2; obtain ⟨i,e,h⟩:=exists_max_image univ f univ_nonempty; have he:bowl A x≤ (Fintype.card ι:ℝ)*f i:=by rw [pie]; exact (sum_le_sum (fun _ t=> h _ t)).trans_eq (by simp)
 refine (pow_le_pow_left₀ (joy A x) he p).trans ?_; unfold shade_p; rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold f; refine (single_le_sum (fun i _=>pow_nonneg (abs_nonneg _) (2*p)) (mem_univ i)).trans' ?_
 rw [pow_mul,sq_abs] -- tune
lemma dime : Integrable (shade_p A p) μ:= ( (integrable_finsetSum univ (fun i _=> peg_b (2*p) (A i)))).const_mul ((τ)^p)
lemma bowlP : Integrable (fun x=> (bowl A x)^p) μ := (dime p A).mono' (by fun_prop) (Eventually.of_forall fun i=> (Real.norm_of_nonneg (pow_nonneg (joy A i) p)).le.trans (shapeP p A i))
abbrev postage (ι:Type)[Fintype ι](p:ℕ)(C:ℝ):ℝ := (Fintype.card ι:ℝ)^p*((Fintype.card ι:ℝ)*(C^(2*p)*teatime (2*p)))
lemma post_p(c:0≤C): 0 ≤ postage ι p C:=by have h:= L0 (2*p); unfold postage; positivity
lemma deputized (F:E→ℝ)(p₁:∀ i,‖A i‖≤ C)(d:ℕ)(u₁:Continuous F)(v:∀ x, ‖F x‖ ≤ (bowl A x)^d) : (∫ x:E, ‖F x‖∂μ) ≤ postage ι d C ∧ Integrable F μ:=by
 let E₁:= (bowlP d A).mono' u₁.aestronglyMeasurable (Eventually.of_forall v); refine ⟨(integral_mono E₁.norm (dime d A) (fun x=> (v x).trans (shapeP d A x))).trans ?_, E₁⟩; unfold shade_p; rw [integral_const_mul, integral_finsetSum _ (fun i _=> peg_b ..)]; simp_rw [pli]; refine mul_le_mul_of_nonneg_left ?_ (by positivity); exact (sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (p₁ i) _) (L0 _))).trans_eq (by simp)
lemma bowl2 (p₁:∀ i,‖A i‖≤ C)(d:ℕ) : (∫ x:E, bowl A x^d ∂μ) ≤ postage ι d C:=by
 have he:= (deputized A C (fun x=>bowl A x^d) p₁ d (by fun_prop) (fun x=>(Real.norm_of_nonneg (pow_nonneg (joy ..) _)).le)).1; simpa only [Real.norm_of_nonneg (pow_nonneg (joy A _) d)] using he
lemma canvasP(x:E): bowl A x^p*bowl B x^q≤ (bowl A x)^(2*p)+(bowl B x)^(2*q):=by let a:=bowl A x^p; let b:=bowl B x^q; rw [show bowl A x^(2*p)=a^2 by unfold a; rw [mul_comm 2 p, pow_mul (bowl A x) p 2], show bowl B x^(2*q)= b^2 by unfold b; rw [mul_comm 2 q, pow_mul (bowl B x) q 2]]; nlinarith only [sq_nonneg (a-b), sq_nonneg a,sq_nonneg b]
lemma canvas (p q:ℕ): Integrable (fun x:E=> bowl A x^p * bowl B x^q) μ:= ((bowlP (2*p) A).add (bowlP (2*q) B)).mono' (by fun_prop) (Eventually.of_forall fun x=> (Real.norm_of_nonneg (mul_nonneg (pow_nonneg (joy A x) p) (pow_nonneg (joy B x) q))).le.trans (canvasP p q A B x))
lemma canv_B (p₁:∀ i,‖A i‖≤ C)(p₂:∀ i,‖B i‖ ≤ C) : (∫ x:E,bowl A x^p*bowl B x^q∂μ) ≤ postage ι (2*p) C+postage ι (2*q) C:=by
 let g:= fun x:E=> bowl A x^(2*p)+bowl B x^(2*q); have hg:Integrable g μ:=(bowlP _ A).add (bowlP _ B)
 refine (integral_mono (canvas A B _ _) hg (canvasP p q A B)).trans ?_; unfold g; rw [integral_add (bowlP _ A) (bowlP _ B)]; exact add_le_add (bowl2 A C p₁ _) (bowl2 B C p₂ _)
-- two point law
lemma sigma₁ : (∫ x:E, bowl A x∂μ)= ∑ i:ι, ‖A i‖^2:=by simp_rw [pie,cents, integral_finsetSum _ (fun i _=>peg_a 2 (A i)),secondB] -- integral_finsetSum indexing should work
abbrev Nir(A B:ι→E):ℝ:= 2*∑ i:ι,∑ j:ι,(inner ℝ (A i) (B j))^2
lemma sigma₂: (∫ x:E,bowl A x*bowl B x∂μ)-(∫ x:E, bowl A x∂μ)*(∫ x:E, bowl B x∂μ)=Nir A B:=by
 unfold Nir; rw [sigma₁,sigma₁,sub_eq_iff_eq_add]; simp_rw [pie,sum_mul,mul_sum]; rw [integral_finsetSum _ (fun i _=>integrable_finsetSum univ (fun j _=>cashV (A i) (B j)))]; simp_rw [integral_finsetSum _ (fun i _=>cashV ..), WickQ]; rw [add_comm]; simp only [sum_add_distrib] -- danger lean infers i argument.
lemma exhaust(i j:ι) : 2*(inner ℝ (A i) (B j))^2 ≤ Nir A B:=mul_le_mul_of_nonneg_left ((single_le_sum (f:=fun j=>(inner ℝ (A i) (B j))^2) (fun _ _=>sq_nonneg _) (mem_univ j)).trans (single_le_sum (f:=fun i:ι=> ∑ j:ι, (inner ℝ (A i) (B j))^2) (fun _ _=>sum_nonneg (fun _ _=>sq_nonneg _)) (mem_univ i))) zero_le_two
#print axioms sigma₂
#print axioms canv_B
end Brew
end YM.SU5.FiniteGaugeData.Indigo
