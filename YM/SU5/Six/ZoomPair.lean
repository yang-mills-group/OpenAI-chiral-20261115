import YM.SU5.Six.ZoomMix
import YM.SU5.Six.JointPM
/-!
# Six-clan zoom matrix: integration (`eq:Zmat`)
-/

set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section

namespace YM.Spectral.PVM
open Filter Complex
open scoped Topology

/-- Polarize the limit on mixed positive measures. -/
lemma polarize_tendsto {H : Hilbert} {q : ℕ → H → ℂ} {x y : ℕ → H} {L : ℂ}
    (h : ∀ a : ℂ, ‖a‖=1 → Tendsto (fun i => q i (x i + a • y i)) atTop (𝓝 L)) :
    Tendsto (fun i => polarize (q i) (x i) (y i)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun i => q i (x i+y i)) atTop (𝓝 L) :=
    (h 1 norm_one).congr (by simp)
  have h2 : Tendsto (fun i => q i (x i-y i)) atTop (𝓝 L) :=
    (h (-1) (by simp)).congr (by simp [sub_eq_add_neg])
  have h3 := h I norm_I
  have h4 : Tendsto (fun i => q i (x i-I • y i)) atTop (𝓝 L) :=
    (h (-I) (by simp)).congr (by simp [sub_eq_add_neg])
  have ht := ((h1.sub h2).sub ((h3.sub h4).const_mul I)).div_const 4
  rw [sub_self,mul_zero,sub_self,zero_div] at ht
  exact ht

end YM.Spectral.PVM

set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine
open Cheer YM.Six

variable {P : Spine} {x : P.Spectrum0 3} {c r : ℕ → ℕ} (Z Z' : Lead.Clan)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "S" => P.seasons 3 ξ
local notation "Q" => YM.OS.Semigroup.ℚmeasure S
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "η" X:max i:max => P.birthCloud x X (c i) (r i)

variable (A : Launch P c r) {q : ℕ → ℝ} (Y : readyUV P c r x q)
         (e : Tendsto q atTop (𝓝 0)) (u : P.lodestarHere 3 (P.otherSpectrum 3 3 x))
variable {F : ℕ → E4 → ℂ} {f : E4 → ℂ} (h : HalfLimit F f)

include A Y e u h

lemma mix_variable (hZZ : Z ≠ Z') (a : ℂ) (ha : ‖a‖=1) :
    Tendsto (fun i => ∫ p, F i (Cheer.zoom (ρ i) p) ∂(Q).diagonal (η Z i + a • η Z' i)) atTop
      (𝓝 (∫ p, f p ∂((promenade Z + promenade Z' : Narrow):Measure E4))) := by
  let W := lyrical_mix Z Z' A Y e u hZZ a ha
  refine (h.weak (weak_mix Z Z' A Y e u hZZ a ha) W.1 W.2).congr fun i => ?_
  exact (h.term i).outlay_integral S (P.dew_pos _ (A.unitSize i)).le _

/-- The `eq:Zmat` limit, allowing variable uniformly bounded costs,
Borel on the positive half-space and converging uniformly on its compacta.
Use `HalfLimit.fixed` when `F i = f` is simply bounded continuous there. -/
theorem zoom_pair :
    Tendsto (fun i => (Q).pairIntegral (fun p => F i (Cheer.zoom (ρ i) p)) (η Z i) (η Z' i)) atTop
      (𝓝 (if Z=Z' then ∫ p, f p ∂(promenade Z:Measure E4) else (0:ℂ))) := by
  by_cases hZZ : Z = Z'
  · subst Z'
    rw [if_pos rfl]
    let W := lyricalCloud Z A Y e u
    refine (h.weak (fertile Z A Y e u).weak W.1 W.2).congr fun i => ?_
    let hρ := (P.dew_pos (c i) (A.unitSize i)).le
    exact ((h.term i).outlay_integral S hρ _).trans
      (YM.Spectral.PVM.pairIntegral_diag (((h.term i).zoom hρ).adm S) _).symm
  rw [if_neg hZZ]
  exact YM.Spectral.PVM.polarize_tendsto (mix_variable Z Z' A Y e u h hZZ)
#print axioms zoom_pair

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
