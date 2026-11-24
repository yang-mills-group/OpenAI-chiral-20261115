import ExactRunning.Finite.Repeat

/-!
# Beat from touching along rays
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

variable {v u : Phase α}
lemma beat_axes (f : Corn α → ℝ) (u v) :
    beat f 0 2 ![axes u,axes v] = (iteratedFDeriv ℝ 2 f 0 ![u,v] : ℂ) := by
  rw [show (![axes u,axes v] : Fin 2 → Phase α) = axes ∘ ![u,v] from funext fun i => by fin_cases i <;>rfl,beat_real]

section ray
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma quad_line {f : X → ℝ} (h : ContDiffAt ℝ ω f 0) (v : X) :
    quad (fun t => f (t • v)) = (2⁻¹:ℝ) * fderiv ℝ (fderiv ℝ f) 0 v v := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  change quad (f ∘ L) = _
  rw [quad, wired L (by simpa using h.analyticAt),map_zero,iteratedFDeriv_two_apply]
  simp [L]

lemma touch_line_hessian {P : X → Prop} {f g : X → ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    (h : ∀ v, P v → Touch (fun t => f (t • v)) (fun t => g (t • v)))
    {u v : X} (hu : P u) (hv : P v) (hw : P (u+v)) :
    iteratedFDeriv ℝ 2 f 0 ![u,v] = iteratedFDeriv ℝ 2 g 0 ![u,v] := by
  have hq (v) (hv : P v) :
      2⁻¹ * fderiv ℝ (fderiv ℝ f) 0 v v = 2⁻¹ * fderiv ℝ (fderiv ℝ g) 0 v v := by
    rw [← quad_line hf,← quad_line hg]
    apply Touch.quad_eq (h v hv)
    · exact ContDiffAt.comp (f:=fun t : ℝ => t • v) (g:=f) 0 (by simpa using hf.of_le (show 2 ≤ ω from le_top)) (by fun_prop)
    exact ContDiffAt.comp (f:=fun t : ℝ => t • v) (g:=g) 0 (by simpa using hg.of_le (show 2 ≤ ω from le_top)) (by fun_prop)
  have H := hq _ hw
  rw [map_add,map_add,map_add,map_add] at H
  simp only [_root_.add_apply] at H
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  change fderiv _ (fderiv _ _) _ u v = fderiv _ (fderiv _ _) _ u v
  linarith [hf.isSymmSndFDerivAt le_top u v, hg.isSymmSndFDerivAt le_top u v,hq u hu,hq v hv]
end ray

def realPart (v : Phase α) : Corn α := fun i => (v i).re
def imagPart (v : Phase α) : Corn α := fun i => (v i).im

lemma parts (v : Phase α) : axes (realPart v) + Complex.I • axes (imagPart v) = v :=
  funext fun _ => by simp [axes,realPart,imagPart]; rw [mul_comm Complex.I, Complex.re_add_im]

namespace Latitude
variable (D : Latitude)
variable {Y : Type} [Add Y] [SMul ℂ Y]

lemma extend {p q : Phase (Co m α) → Y} (hp : Leads p) (hq : Leads q)
    (h : ∀ v, D.repeats v → p (axes v) = q (axes v))
    {v : Phase (Co m α)} (hv : D.repeats v) : p v = q v := by
  rw [← parts v,hp,hq, h (realPart v) (hv.comp Complex.re), h (imagPart v) (hv.comp Complex.im)]

lemma beat_on {f g : Corn (Co m α) → ℝ}
    (h : ∀ u v, D.repeats u → D.repeats v →
        iteratedFDeriv ℝ 2 f 0 ![u,v] = iteratedFDeriv ℝ 2 g 0 ![u,v])
    {u v : Phase (Co m α)} (hu : D.repeats u) (hv : D.repeats v) :
    beat f 0 2 ![u,v] = beat g 0 2 ![u,v] := by
  refine D.extend (left_beat _ _) (left_beat _ _) (fun x hx =>
    D.extend (right_beat _ _) (right_beat _ _) (fun y hy => ?_) hv) hu
  rw [beat_axes,beat_axes,h x y hx hy]

lemma beat_of_touch {f g : Corn (Co m α) → ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    (h : ∀ v, D.repeats v → Touch (fun t => f (t • v)) (fun t => g (t • v)))
    {u v : Phase (Co m α)} (hu : D.repeats u) (hv : D.repeats v) :
    beat f 0 2 ![u,v] = beat g 0 2 ![u,v] :=
  D.beat_on (fun _ _ hx hy => touch_line_hessian hf hg h hx hy (hx.add hy)) hu hv
end Latitude
end ExactRunning
