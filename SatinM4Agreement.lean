import YM.SU5.Registration.M8
import Velour.Wadding.Tiara

/-!
Agreement on the fixed Satin election, field maps and padded physical instruments.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld

universe u

namespace RegistrationAgreement

theorem sameM4Tuple (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4) :
    M4Tuple P K c r x R i₀ F U A n w V g h X Y Z ↔
      M4Furnish P K c r x R i₀ F U A n w V g h X Y Z := by
  constructor <;> intro q <;> cases q <;> constructor <;> assumption

private theorem clippedHeat (s width : ℝ≥0) :
    ((s : ℝ) - (width : ℝ)).toNNReal = s - width := by
  rcases le_total width s with h | h
  · rw [← NNReal.coe_sub h, Real.toNNReal_coe]
  · have hs : (s : ℝ) ≤ (width : ℝ) := h
    rw [tsub_eq_zero_of_le h, Real.toNNReal_of_nonpos (sub_nonpos.mpr hs)]

theorem samePaddedOperator (P : Spine) (j : Axis) (x : P.Spectrum0 j)
    (A : P.Apron) (s t : ℝ≥0) :
    A.dye P j x (s : ℝ) (t : ℝ) = P.stageH j x A s t := by
  unfold Apron.dye stageH
  rw [OS.Semigroup.pad_val, A.width_real P j, clippedHeat, clippedHeat]

theorem sameProjectedOperator (P : Spine) (j : Axis) (x : P.Spectrum0 j)
    (A : P.Apron) (s t : ℝ≥0) :
    P.toStageG j x (A.dye P j x (s : ℝ) (t : ℝ)) = P.stageG j x A s t := by
  exact congrArg (fun op => P.toStageG j x op) (samePaddedOperator P j x A s t)

/-- M8's funding pays a polynomial bound for the very same Velour pivot instruments. -/
theorem pivotPricesForVelour (P : Spine) (x : P.Spectrum0 3) (A : ℕ → P.Apron)
    (funding : P.Funding x A) (j : Axis) (l : List Axis) :
    ∃ k : ℕ, ∃ C ≥ (0 : ℝ), ∀ s : ℝ≥0, 0 < s → s ≤ 1 → ∀ᶠ i : ℕ in atTop,
      (s : ℝ)^k * ‖((A i).pivot P l).velour P j (P.advocate 3 x j) (s : ℝ)‖ ≤ C := by
  simpa only [Apron.velour, samePaddedOperator] using funding.price j l

/-- At each positive time budget the projected Velour operators and adjoints are
strongly Cauchy on the purchased physical Hilbert space. -/
theorem projectedVelourCauchy (P : Spine) (x : P.Spectrum0 3) (A : ℕ → P.Apron)
    (funding : P.Funding x A) (j : Axis) (l : List Axis) (s : ℝ≥0) (hs : 0 < s) :
    Travels (H := P.ManyF j (P.advocate 3 x j)) (fun i : ℕ =>
      P.toStageG j (P.advocate 3 x j)
        (((A i).pivot P l).velour P j (P.advocate 3 x j) (s : ℝ))) := by
  simpa only [Apron.velour, sameProjectedOperator] using funding.travels j l s hs

/-- The complete M8 construction purchases the base Velour field tuple on its own elected vacuum. -/
theorem planetaryWithVelourTuple : ∃ (P : Spine) (K : P.Register) (c r : ℕ→ℕ) (x : P.Spectrum0 3) (R : P.Ellis 3 x)
    (i₀ : ℕ) (F U : SampleDose) (A : ℕ → P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4 →L[ℂ] P.ManyF 3 (P.advocate 3 x 3)) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4),
    id ≤ r ∧ uniform P K (fun _ _ _ _ _ _ _ _ _ _ _ _ => 0) 1 1 ∧
    M4Furnish P K c r x R i₀ F U A n w V g h X Y Z ∧ P.Garrison x c r A n ∧ PlanetaryG.{u} P A ∧ (∀ x:P.Spectrum0 3,P.Guest x c r A n) ∧ ∃ p:CapBacked P x A c r n w, P.OverM4 x c r F U A n w V Y Z p := by
  obtain ⟨P,K,c,r,x,R,i₀,F,U,A,n,w,V,g,h,X,Y,Z,hr,hu,q,rest⟩ := planetary_sunlit.{u}
  exact ⟨P,K,c,r,x,R,i₀,F,U,A,n,w,V,g,h,X,Y,Z,hr,hu,
    (sameM4Tuple P K c r x R i₀ F U A n w V g h X Y Z).mp q,rest⟩

end RegistrationAgreement
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
