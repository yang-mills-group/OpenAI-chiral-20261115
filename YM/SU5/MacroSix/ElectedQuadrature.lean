import YM.SU5.MacroSix.StrongQuadrature
import YM.SU5.MacroSix.Payments
/-! # Putting the quadrature on this Spine and this character

The strong limit is on ColorHil, the still-*selected* realization.
It is exactly in the real continuous-translation sector and we give
it using `P.cartage`. No assertion of unprojected grid price tending
pointwise to the `commonWell` answer on a general two-body time order.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria

namespace Spine
variable (P : Spine) (x : P.Spectrum0 3)
local notation "β" => P.otherSpectrum 3 3 x
local notation "H" => P.ColorHil 3 β
local notation "F" => P.ManyF 3 β
local notation "M" => timeMesh P.par
local notation "T" => P.enter 3 β
local notation "U" => P.truck 3 β
local notation "V" => P.cartage 3 β

abbrev meshSize (i : ℕ) : ℝ := (mill (timeMesh P.par) i:ℝ)
lemma pose_place (i : ℕ) (r : Cover) : P.pose i r = MacroSix.Grid.place (P.meshSize i) r := rfl
lemma meshSize_pos (i : ℕ) : 0 < P.meshSize i := mill_pos M i
lemma pose_supplied (g : P.VMark) : ∀ᶠ n in atTop, ∃ z, P.vtile n z=g := by
  filter_upwards [Filter.eventually_all.mpr (fun i : Axis ↦ P.vwhere (g:=g) 0 i)] with n v
  choose k w using v
  exact ⟨k,funext w⟩

lemma truck_setup : MacroSix.Grid.Setup (I:=Axis) P.meshSize (P.truck 3 β) P.vtile P.laysM where
  pos := P.meshSize_pos
  vanishes := NNReal.tendsto_coe.mpr (vanishes M)
  act_add g h y := DFunLike.congr_fun (P.truck_paves 3 β g h).symm y
  norm_eq := P.truck_norm 3 β
  additiveGrid n x y := funext fun i ↦ notch_add M n _ _
  placement := fun _ _ ↦ rfl
  finer := P.pose_supplied

lemma gridCosts_finite (t : ℕ) (E : Type*) [Zero E]
    (f : Vantage → E) (u : HasCompactSupport f) :
    (Function.support fun x ↦ f (P.pose t x)).Finite :=
  MacroSix.Grid.finite_tags_of (P.meshSize t) (P.meshSize_pos t) u

/-- Actual single mesh sum with compactly supported vector cost; no jitter. -/
def vectorSum (f : Vantage → H) (i : ℕ) : H := ((P.meshSize i:ℂ)^4) •
  ∑ᶠ k, U (P.vtile i k) (f (P.pose i k))

lemma vectorSum_eq (f : Vantage → H) (i : ℕ) : MacroSix.Grid.transportSum
    (I:=Axis) P.meshSize (P.truck 3 β) P.vtile f i = P.vectorSum x f i := by
  let u := P.meshSize i
  have hc : ((↑(u^Fintype.card Axis)):ℂ) = (u:ℂ)^4 := by
    rw [Fintype.card_fin]; push_cast; rfl
  exact congrArg (fun y : ℂ ↦ y • ∑ᶠ k, U (P.vtile i k) (f (P.pose i k))) hc

/-- Special case of `t:macro-order` technology, applied to the actual grid and Ellis
of *this x*; needs neither off-calendar UV transport nor continuity of raw translations. -/
lemma vectorLimit (J : P.Ellis 3 x) (f : Vantage → H) (p : Continuous f)
    (c : HasCompactSupport f) :
    Tendsto (fun i ↦ P.vectorSum x f i) atTop
      (𝓝 (P.enter 3 β (MacroSix.total F volume (fun y : Vantage ↦
        V y (P.wealth 3 β (f y)))))) :=
  (MacroSix.transportSum_limit (I:=Axis) P.VMark H F (T).toContinuousLinearMap
    (P.wealth 3 β) P.meshSize (U) P.vtile P.laysM (P.truck_setup x) (V)
    (fun g hg ↦ P.caravan 3 β _ g continuous_id hg) (fun i k g ↦ P.cart_and 3 β (P.vtile i k) g)
    J.mistT (fun _ h ↦ P.gentle_room J.owned h) (J.shaky 3) f p c).congr
    fun i ↦ P.vectorSum_eq x f i

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.vectorLimit
