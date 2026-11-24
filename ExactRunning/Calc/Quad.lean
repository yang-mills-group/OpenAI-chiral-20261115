import ExactRunning.Calc.Touch

/-!
# Linear calculus for the quadratic test
-/
noncomputable section
open scoped ContDiff Topology
namespace ExactRunning
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {f g : ℝ → E}

lemma quad_clm (L : E →L[ℝ] H) (h : ContDiffAt ℝ 2 f 0) :
    quad (L ∘ f) = L (quad f) := by
  rw [quad, L.iteratedFDeriv_comp_left h (by simp), quad, map_smul]
  rfl

lemma quad_re {f : ℝ → ℂ} (h : ContDiffAt ℝ 2 f 0) :
    quad (fun s => (f s).re) = (quad f).re := quad_clm Complex.reCLM h

lemma quad_add (h : ContDiffAt ℝ 2 f 0) (h' : ContDiffAt ℝ 2 g 0) :
    quad (f+g) = quad f + quad g := by
  rw [quad,iteratedFDeriv_add_apply (i:=2) h h']
  simp only [_root_.add_apply,smul_add];rfl

lemma quad_sub (h : ContDiffAt ℝ 2 f 0) (h' : ContDiffAt ℝ 2 g 0) :
    quad (f-g) = quad f - quad g := by
  rw [sub_eq_add_neg, quad_add h (g:=-g) h'.neg]
  simp only [quad,iteratedFDeriv_neg_apply,_root_.neg_apply,
             smul_neg,sub_eq_add_neg]

lemma quad_weight {R : Type*} [DistribSMul R E] [SMulCommClass ℝ R E] [ContinuousConstSMul R E]
    (h : ContDiffAt ℝ 2 f 0) (c : R) : quad (c • f) = c • quad f := by
  rw [quad,iteratedFDeriv_const_smul_apply (i:=2) h]
  simp only [_root_.smul_apply, smul_comm (2⁻¹:ℝ) c]
  rfl

lemma quad_rescale (h : ContDiff ℝ 2 f) (d : ℝ) :
    quad (fun x => f (d*x)) = d^2 • quad f := by
  let L := d • ContinuousLinearMap.id ℝ ℝ
  change quad (f ∘ L) = _
  rw [quad,L.iteratedFDeriv_comp_right h _ (by simp),map_zero,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change ((2⁻¹:ℝ) • (iteratedFDeriv ℝ 2 f 0) (fun i=> d • ((1:Fin 2 → ℝ) i))) = _
  rw [ContinuousMultilinearMap.map_smul_univ (iteratedFDeriv ℝ 2 f 0) (fun _=>d) 1]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact smul_comm ..

end ExactRunning
