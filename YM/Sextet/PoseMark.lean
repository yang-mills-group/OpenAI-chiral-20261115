import YM.Sextet.Body
import YM.SU5.Aria.SatinRails

/-!
# Grid tickets for moving bodies

Movement/opposition on the resolution labels; exact held budgets even through repeated advances
before moving. One elected character sees **zero one-point price** for these six bodies, before
smearing and after any advance, including their oppositions in any coordinate. In particular
joint prices measured from these probes at any such regulation need no product-of-one-point
subtraction relative to those same probes on this state.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria
variable (P: Spine)

/-- All resolutions use the *same* length unit. Integer arguments are in full ticks
and the mesh is `Spine.macroTick`. -/
def grid (t : ℕ) (q : Cover) := P.laysM (P.vtile t q)

lemma grid_eq (t : ℕ) (q : Cover) (j:Axis) :
    P.grid t q j = P.macroTick t * (q j:ℝ) := mul_comm _ _

lemma oppose_grid (j:Axis) (t:ℕ) (q:Cover) :
    P.grid t (mirrorΩ j q) = mirrorΩ j (P.grid t q) := by
  funext i; by_cases p:i=j
  · subst i; simp [grid_eq,mirrorΩ]
  simp [grid_eq,mirrorΩ,p]

/-- Meaningful for `A.s ≤ t`. Use at every purchase (`fullScroll` for products
is by definition the product of these). Singlet price is paid with an **exact** shield. -/
def aimMark (A:P.Apron) (t:ℕ) (q: Cover) := P.chartAll q (A.full P t)

/-- Actual pose prices. `Apron.scenery` uses RSpace = doubled physical units. -/
def footBill (A:P.Apron) (y:Vantage) : Set Vantage :=
  {z|∀j, |z j-y j| ≤ A.realWidth P j}

lemma scenery_bill (A:P.Apron) (y:Vantage) :
    A.scenery P y = {z | (fun i=>z i/2) ∈ P.footBill A y} := by
  ext x
  apply forall_congr'
  intro i
  exact
    show |x i-2*y i|≤2*A.realWidth P i ↔ |x i/2 - y i| ≤ A.realWidth P i from by
      rw [abs_le, abs_le]; constructor <;> rintro ⟨h,k⟩ <;> constructor <;> linarith

lemma aim_singlet (A:P.Apron) (t:ℕ) (q:Cover) :
    P.aimMark A t q ∈ enclave P.calibration :=
  P.cruise_color _ q (A.fullColor P t)

lemma aim_support (R:P.Register) (A:P.Apron) (t:ℕ) (h:A.s ≤ t) (q:Cover) :
    P.aimMark A t q ∈ keep P.par P.width t P.calibration true (A.scenery P (P.grid t q)) :=
  P.calibrated_location t A q R h

lemma oppose_cruise (j:Axis) (q:Cover) (f:P.Test) (L:List Axis) :
    P.reflectTest j (P.cruise L q f) = P.cruise L (mirrorΩ j q) (P.reflectTest j f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [cruise_step,cruise_step,AlgHom.comp_apply,AlgHom.comp_apply,←ih]
    unfold mirrorΩ
    by_cases p:i=j
    · subst i; rw [P.meetOwn,if_pos rfl]
    rw [←P.meetrefl i j _ _ p,if_neg p]

lemma oppose_aim (j:Axis) (A:P.Apron) (t:ℕ) (q:Cover) :
    P.reflectTest j (P.aimMark A t q) = P.aimMark (A.kiss P j) t (mirrorΩ j q) := by
  have he:P.reflectTest j (A.full P t)=(A.kiss P j).full P t := (P.reflUp ..).symm
  unfold aimMark chartAll; rw [P.oppose_cruise,he]

variable (a:Axis) (x:P.Spectrum0 a)
local notation "m" t:max => P.singleState a t x

lemma selected_reality (j:Axis) (t:ℕ) (f:P.Test) :
    (m t) (P.reflectTest j f) = star ((m t) f) := by
  rw [←P.single_agrees a j x,←P.single_agrees a j x,P.single_state j t,
     P.single_state j t,←P.reading_star,map_star]

lemma selected_cruise (t:ℕ) (q:Cover) (f:P.Test) (L:List Axis) :
    (m t) (P.cruise L q f) = (m t) f := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [cruise_step,AlgHom.comp_apply,←ih]
    rw [←P.single_agrees a i x,←P.single_agrees a i x,P.slide_single]

lemma selected_advance (s k:ℕ) (f:P.Test) :
    (m (s+k)) (P.conveying s k f) = (m s) f := by
  simp only [P.single_state,P.carryReads]

lemma selected_aim (A:P.Apron) (t:ℕ) (h:A.s ≤ t) (q:Cover) :
    (m t) (P.aimMark A t q) = (m (A.s)) A.F := by
  unfold aimMark chartAll Apron.full
  rw [P.selected_cruise]
  generalize hu:t-A.s=k
  rw [show t=A.s+k by omega,P.selected_advance]

theorem one_point (Z:Lead.Clan) {s t:ℕ} (h:s ≤ t) (n:ℕ) (q:Cover) :
    (m t) (P.aimMark (P.macroBody Z s n) t q)=0 := by
  rw [P.selected_aim a x _ t h,←P.single_agrees a 3 x]
  change P.singleState 3 s (P.otherSpectrum a 3 x) (P.timeDifference Z n)=0
  rw [timeDifference,map_sub,P.slide_single,sub_self]

theorem one_point_mirror (j:Axis) (Z:Lead.Clan) {s t:ℕ} (h:s ≤ t) (n:ℕ) (q:Cover) :
    (m t) (P.aimMark ((P.macroBody Z s n).kiss P j) t q)=0 := by
  have he : mirrorΩ j (mirrorΩ j q)=q := by
    funext i; by_cases p:i=j <;> simp [mirrorΩ,p]
  rw [←he, ←oppose_aim, P.selected_reality,P.one_point a x Z h n,star_zero]

/-- Reading instruction if using `Θ_x`. This pays ***whole*** single-height
mixed costs, by linearity also the smoothed products there. Every positive point evaluation
uses this instruction: opposed or unopposed, advancing and moving before asking at `t`.
Never implement a joint purchase instead by multiplying prior compressed costs. -/
theorem center_fuse (R:P.Register) (j:Axis) (t:ℕ) (f:P.Test) :
    P.spirits R a x (Altitude.pinhole P.Test t f) =
      P.singleState j t (P.advocate a x j) f := by
  rw [P.oneCup,P.single_agrees]

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
