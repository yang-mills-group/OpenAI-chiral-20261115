import YM.SU5.MacroSix.ProjectedUV
import YM.SU5.MacroSix.UniformBall
/-!
# l:zoommat

Spectral estimates hold simultaneously for the full six-by-six array, on the
one elected character. Everything applies on the supplied physical course / Spine,
`Launch` and `readyUV` on that same choice, and `lodestarHere` (e.g.
`party.2.1.accepted 3`). Higher-level existence call in the task entry file.
No postulated measure limits here; uses the project's Wick/kernel prices for *varying*
tests, plus our new off-diagonal transport extension. Note:

* argument `x` is outside all estimates, no re-election as `i` varies;
  `β` below just stands for `P.otherSpectrum 3 3 x` (as in Bands).
* `crossIntegral` = integrate against the **actual** PVM cross-measure, implemented
  via polarization of its finite *diagonal* measures, see `PolarizedMeasure`.
* `gram_press` identifies the projected matrix in `sixGrant` with the corresponding
  spectral-measure matrix (at the scaled open window). We allow any open region intersecting
  `Mink.inside`; in the application's reflected smeared Gram test we'll use in particular
  a bounded open ball inside with spatial projection in an open octant.
* the indices are `Lead.Clan` = `Window.Family` (i.e. `Fin 3 × Bool`, true for Ten);
  the raw `SU.Slot`s are a different type, with that same family map.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Filter MeasureTheory Ballad Lead Cordial Prototype
open scoped Topology MatrixOrder ComplexOrder InnerProductSpace NNReal ENNReal BigOperators
attribute [local instance] opCStarAlgebra
open Cheer MatrixZoom

namespace Spine
variable {P : Spine} {x : P.Spectrum0 3} {c r : ℕ → ℕ}
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 β
local notation "v" j:max i:max => P.birthCloud x j (c i) (r i)
local notation "ρ" i:max => P.dew (c i) (r i)
variable (A : Launch P c r) {d : ℕ → ℝ} (Y : readyUV P c r x d) (p : Tendsto d atTop (𝓝 0))
    (u : P.lodestarHere 3 (P.otherSpectrum 3 3 x))
include A Y p u

omit A Y p u in
private lemma tendsto_switch {Z W : Clan} {g : ℕ → ℂ} {q r : ℂ} (h : q=r)
    (u : Tendsto g atTop (𝓝 (if Z=W then q else 0))) :
    Tendsto g atTop (𝓝 (if Z=W then r else 0)) := by rwa [← h]

lemma sixLyrical (ι : ℕ → ℕ) (hi : Tendsto ι atTop atTop) (a : Window.Family → ℂ)
    (b : ℕ → Window.Family → ℂ) (hb : ∀ j, Tendsto (fun i ↦ b i j) atTop (𝓝 (a j))) :
    Lyrical (combinationLaw promenade a)
      (fun i ↦ outlay S (∑ j, b i j • v j (ι i)) (ρ (ι i))) := by
  let X (i : ℕ) : ℝ≥0 := ⟨ρ i, (P.dew_pos _ (A.unitSize i)).le⟩
  let f (i : ℕ) (j : Clan) := v j i
  let H := P.ManyF 3 β
  have he (j k : Clan) (z : Space3) (t : ℝ≥0) : Tendsto (fun i ↦ inner ℂ (f i j)
      ((S).U ((X i:ℝ) • Cheer.shore z) ((S).E (X i*t) (f i k)))) atTop
        (𝓝 (if j=k then FLap (promenade j) z ↑(t:ℝ) else 0)) := by
    let T i := X i*t
    let U := cutPulse z
    let F (i : ℕ) := ρ i • U
    have hx : P.dimensionS c r T (t:ℝ) := tendsto_const_nhds.congr fun i ↦ by
      rw [show (T i:ℝ) = ρ i * (t:ℝ) from rfl]; field_simp [(P.dew_pos _ (A.unitSize i)).ne']
    have hv : Tendsto (fun i ↦ (ρ i)⁻¹ • F i) atTop (𝓝 U) := tendsto_const_nhds.congr fun i ↦
      (inv_smul_smul₀ (P.dew_pos _ (A.unitSize i)).ne' U).symm
    exact tendsto_switch (blinded j z t) (centeredMatrixZoom j k A Y p u U t t.property T hx F hv)
  exact combinationLaw_lyrical H S X f promenade home_bright he hi hb

/-- The scaled measures converge weakly as a matrix: test *all* coefficient vectors,
not just diagonal entries. This also tolerates varying coefficients (costs at the same
rescaled height i) with fixed limits. -/
theorem sixLawLimit (a : Window.Family → ℂ) (b : ℕ → Window.Family → ℂ)
    (hb : ∀ j, Tendsto (fun i ↦ b i j) atTop (𝓝 (a j))) :
    Tendsto (fun i ↦ outlay S (∑ j, b i j • v j i) (ρ i))
      atTop (𝓝 (combinationLaw promenade a)) :=
  MatrixZoom.weak (sixLyrical A Y p u id tendsto_id a b hb)

/-- Full l:zoommat test statement: all cross pairings and tolerates
compact-uniform test motion. Use `ZoomTest.const` for a single arbitrary bounded
continuous cost on nonnegative energy. -/
theorem sixZoom (j k : Window.Family) {F : ℕ → E4 → ℂ} {f : E4 → ℂ} (X : ZoomTest F f) :
    Tendsto (fun i ↦ crossIntegral (S).ℚmeasure (v j i) (v k i)
      (fun p ↦ F i ((ρ i) • p))) atTop
        (𝓝 (if j=k then ∫ x, f x ∂(promenade j:Measure E4) else 0)) :=
  let R (i : ℕ) : ℝ≥0 := ⟨ρ i, (P.dew_pos _ (A.unitSize i)).le⟩
  entryLimit S R (fun i j ↦ v j i) promenade home_bright (fun a ↦
    sixLawLimit A Y p u a (fun _ ↦ a) (fun _ ↦ tendsto_const_nhds)) j k X

/-- A single lower rank price d (PSD order) for the *measure* grant on every such ball.
d is outside height threshold but may depend on the ball. Stronger than ball-only:
applies to every open spectral window meeting the timelike interior. -/
theorem sixGrant (D : Set E4) (hd : IsOpen D) (hn : (Mink.inside ∩ D).Nonempty) :
    ∃ t : ℝ, 0 < t ∧ ∀ᶠ i in atTop, (t:ℂ) • (1 : Matrix Window.Family _ ℂ) ≤
      Matrix.gram ℂ (fun j ↦ (S).ℚmeasure.region (Cheer.press (ρ i) D) (v j i)) :=
  combinationBall S (fun i ↦ ρ i) (fun i j ↦ v j i) promenade
    (sixLyrical A Y p u) D hd (fun j ↦ importance j hd hn)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms sixLawLimit
#print axioms sixZoom
#print axioms sixGrant
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
