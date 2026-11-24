import YM.SU5.Six.IncBody
import YM.SU5.Six.ViewHom
import YM.SU5.Six.Night
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
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

/-!
Time increment probe on the same `ManyF` as the spectral zoom.
No change of realization.
-/
open Cheer YM.Six YM.OS

private lemma dark_aux {H : Hilbert} (T : H.Op) (u e : H) (a : ℂ) (h : T e = e) :
    u - T u = (1 - T : H.Op) (u - a • e) := by
  rw [sub_apply,T.map_sub,T.map_smul,h]
  change u - T u = u - a • e - _
  abel

variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "Q" => YM.OS.Semigroup.ℚmeasure S

/-- `v` in `eq:dark`, by projection on the continuous part. -/
def incV (Z : Window.Family) (s n : ℕ) : H :=
  P.wealth 3 ξ (P.viewF 3 ξ s (P.incF_bright Z s n))
lemma dark (Z : Window.Family) (s n : ℕ) :
    P.incV x Z s n = (1 - (S).E (P.incT s n) : (H).Op) (P.birthCloud x Z s n) := by
  let η := P.shard x Z s n
  let d := P.incT s n
  let u := P.wealth 3 ξ η
  have h := P.brightC Z s n
  have q := P.passesLater 3 s (P.incStep n) h
  have he : P.viewF 3 ξ s (P.incF_bright Z s n) = η - (P.physicalEnergy 3 ξ).E d η :=
    (P.view_sub 3 ξ s h q).trans <|
      congrArg (η - ·) (P.releasedLater 3 ξ s (P.incStep n) h)
  exact Eq.trans (congrArg (P.wealth 3 ξ) he)
    <| Eq.trans ((P.wealth 3 ξ).map_sub η ((P.physicalEnergy 3 ξ).E d η))
    <| Eq.trans (congrArg (u - ·) (P.bankHeat 3 ξ d η))
      (dark_aux ((S).E d) u _ (P.allowance x Z s n) (P.heaven_hot 3 ξ d))
lemma incV_night (Z : Window.Family) (s n : ℕ) :
    (Q).region night (P.incV x Z s n) = 0 := by
  exact Eq.trans (congrArg ((Q).region night) (P.dark x Z s n)) (morning ..)

/-- Pair matrix in `(space,time)` coordinates. -/
def risingK (s n : ℕ) (y : Space3) (T : ℝ≥0) : Matrix Window.Family Window.Family ℂ :=
  .of fun Z Z' => inner ℂ (P.incV x Z s n) ((S).U (shore y) ((S).E T (P.incV x Z' s n)))

lemma risingK_app (s n : ℕ) (y : Space3) (T : ℝ≥0) (Z Z' : Window.Family) :
    P.risingK x s n y T Z Z' = (Q).pairIntegral (tapered y T (P.incT s n))
      (P.birthCloud x Z s n) (P.birthCloud x Z' s n) := by
  exact Eq.trans (congrArg₂ (fun (a b : H) => inner ℂ a ((S).U (shore y) ((S).E T b)))
       (P.dark x Z s n) (P.dark x Z' s n))
    (tapered_pair _ y _ _ (P.birthCloud x Z s n) (P.birthCloud x Z' s n))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
