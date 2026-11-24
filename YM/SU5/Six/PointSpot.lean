import YM.SU5.Six.PricePair
import YM.SU5.Aria.Affliction
import YM.SU5.Selected.Upstage
set_option autoImplicit false
set_option maxHeartbeats 80000
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
open Aria
open PhaseChoice (handstamp)
variable (P : Spine)
/-- Physical aperture box around body center `p`. -/
def Apron.crate (D : P.Apron) (p : Vantage) :=
  {x : Vantage | ∀ i : Axis, |x i - p i| ≤ D.realWidth P i}
lemma Apron.crate_shield (D : P.Apron) (p : Vantage) :
    handstamp (D.crate P p) = D.scenery P p := by
  ext x; unfold handstamp crate scenery
  change (∀ i : Axis, |x i / 2 - p i| ≤ D.realWidth P i) ↔ _
  refine forall_congr' (fun i => ?_)
  rw [abs_le, abs_le]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

/-- The singlet tests located in a proposed physical price.
The use of `handstamp` pays shields in physical length convention
(fermion unit rather than gauge). -/
def locatedIn (t : ℕ) (O : Set Vantage) : Subalgebra ℂ P.Test :=
  enclave P.calibration ⊓ keep P.par P.width t P.calibration true (handstamp O)
lemma locatedIn_enclave (t : ℕ) (O : Set Vantage) : P.locatedIn t O ≤ enclave P.calibration := inf_le_left
lemma locatedIn_mono (t : ℕ) {U V : Set Vantage} (h : U ⊆ V) : P.locatedIn t U ≤ P.locatedIn t V :=
  inf_le_inf_left _ <| rooms _ _ _ _ _ _ (Set.preimage_mono h)

/-- `Δ_t`, physical mesh unit. -/
def spotMesh (t : ℕ) : ℝ := mill (timeMesh P.par) t
lemma spotMesh_pos (t : ℕ) : 0 < P.spotMesh t := mill_pos ..
/-- Grid pose. -/
def gridSpot (t : ℕ) (d : Cover) : Vantage := P.laysM (P.vtile t d)
lemma gridSpot_mul (t : ℕ) (d : Cover) (j : Axis) :
    P.gridSpot t d j = (d j : ℝ) * P.spotMesh t := rfl
lemma gridSpot_comp (t : ℕ) {I : Type*} (d : I → Cover) :
    P.gridSpot t ∘ d = P.laysM ∘ (P.vtile t ∘ d) := rfl
lemma gridSpot_usher (t : ℕ) (d f : Cover) :
    usher (P.gridSpot t d) (P.gridSpot t f) = P.laysM ∘ (P.vtile t ∘ usher d f) := by
  funext b; cases b <;> rfl

/-- `T_d^(t) (D_s:t F)`. Used only with `D.s ≤ t`. -/
def castAt (D : P.Apron) (t : ℕ) (d : Cover) : P.Test :=
  P.chartAll d (D.full P t)
lemma castAt_located (D : P.Apron) (R : P.Register) {t : ℕ} (h : D.s ≤ t) (d : Cover) :
    P.castAt D t d ∈ P.locatedIn t (D.crate P (P.gridSpot t d)) := by
  constructor
  · exact P.cruise_color _ _ (Apron.fullColor P D t)
  rw [Apron.crate_shield]; exact P.calibrated_location t D d R h

variable (x : P.Spectrum0 3)

/-- Selected fine-grid reading and continuum point recognition,
when footprints actually in `Plenum` and implemented at `t`.
(Here we only need ordered-on-3 lists in their given order.) -/
lemma spot_full {I : Type*} (A : I → P.Apron) (L : List I) (d : I → Cover) (J : P.Ellis 3 x)
    (t : ℕ) (ht : ∀ i∈L, (A i).s ≤ t)
    (h3 : P.Turnstile 3 A L (P.gridSpot t ∘ d)) (ha : P.Plenum A L (P.gridSpot t ∘ d)) :
    P.singleState 3 t x (P.fullScroll t A d L) = P.commonWell 3 x A (P.gridSpot t ∘ d) L := by
  rw [← P.single_agrees 3 3 x, P.common_cult 3 x A _ _ J (List.Perm.refl _) h3]
  exact (P.turn_purchase 3 (P.advocate 3 x 3) A d t L h3 ht).symm.trans
    (P.entirely_now 3 x A L J 3 _ h3 ha)

/-- `M` of any opposed mark. -/
lemma opposed_single (s : ℕ) (f : P.Test) :
    P.singleState 3 s x (P.reflectTest 3 f) = star (P.singleState 3 s x f) :=
  (congrArg (P.chi 3 x) (P.reading_star 3 s f).symm).trans (map_star ..)

/-- Native continuum one-point kernel (`D` at `p`). -/
def bodyOne (D : P.Apron) (p : Vantage) := P.commonWell 3 x
    (fun _ : Unit => D) (fun _ : Unit => p) [()]
lemma bodyOne_price (J : P.Ellis 3 x) (D : P.Apron) (p : Vantage) :
    P.bodyOne x D p = P.singleState 3 D.s x D.F := by
  let A := fun _ : Unit => D
  let f := fun _ : Unit => p
  have hf : P.Turnstile 3 A [()] f := List.pairwise_singleton ..
  let A' := fun i : P.Model0 => i.1
  let f' := fun i : P.Model0 => i.2
  have hg : P.Turnstile 3 A' [(D,p)] f' := List.pairwise_singleton ..
  exact Eq.trans (P.common_cult 3 x A f [()] J (.refl _) hf)
    (Eq.trans (P.common_cult 3 x A' f' [(D,p)] J (.refl _) hg).symm
      ((P.commons_single x J D p).trans (P.single_agrees 3 3 x _ _)))

lemma castAt_price (J : P.Ellis 3 x) (D : P.Apron) {t : ℕ} (h : D.s ≤ t) (d : Cover) :
    P.singleState 3 t x (P.castAt D t d) = P.bodyOne x D (P.gridSpot t d) := by
  let U := fun _ : Unit => D; let f := fun _ : Unit => d
  have he : P.fullScroll t U f [()] = P.castAt D t d := mul_one _
  rw [← he]
  exact P.spot_full x U [()] f J t (fun _ _ => h) (List.pairwise_singleton ..)
    ⟨fun _ => ⟨[()],List.Perm.refl _,List.pairwise_singleton ..⟩⟩

variable (s n : ℕ)
lemma bodyOne_incA (J : P.Ellis 3 x) (Z : Window.Family) (p : Vantage) :
    P.bodyOne x (P.incA Z s n) p = 0 := (P.bodyOne_price x J _ _).trans (P.incF_zero Z s n x)
lemma bodyOne_incB (J : P.Ellis 3 x) (Z : Window.Family) (p : Vantage) :
    P.bodyOne x (P.incB s n Z) p = 0 := by
  rw [P.bodyOne_price x J]
  change P.singleState 3 s x (P.reflectTest 3 (P.incF Z n)) = _
  rw [P.opposed_single, P.incF_zero, star_zero]

/-- Domain for all-axis strict margins on a *relative* pose (time increasing).
Measures on pairs of rectangles use only such points in Part (ii).
-/
def starPair := {r : Vantage | 2*(P.costW s n 3)< r 3 ∧
    ∀ i : Axis, 2*(P.costW s n i) < |r i|}
lemma star_clear (Z Z' : Window.Family) (p q : Vantage) (h : q-p ∈ P.starPair s n) :
    let A := usher (P.incB s n Z) (P.incA Z' s n)
    let L := [false,true]
    P.Turnstile 3 A L (usher p q) ∧ P.Plenum A L (usher p q) := by
  obtain ⟨h,y⟩ := h
  simp only [two_mul] at h y
  exact ⟨P.orderPair (P.incB s n Z) _ 3 _ _ h,⟨fun i => by
    rcases lt_abs.mp (y i) with v|u
    · exact ⟨[false,true],List.Perm.refl _,P.orderPair _ _ i _ _ v⟩
    rw [Pi.sub_apply,neg_sub] at u
    exact ⟨[true,false],List.Perm.swap ..,P.orderPair' _ _ i _ _ u⟩⟩⟩

/-- Matrix of point tests **at** `t`, full ticks. No independence assumptions
on the readings. Ordered separated comparison will always take `t ≥ s`. -/
def spotMat (t : ℕ) (d f : Cover) : Matrix Window.Family Window.Family ℂ := .of fun i j =>
  P.singleState 3 t x (P.castAt (P.incB s n i) t d * P.castAt (P.incA j s n) t f)

/-- Under the indicated stronger support clearance on ALL axes,
recognition is exact already on point prices at `t`. -/
lemma spotMat_rise (J : P.Ellis 3 x) (t : ℕ) (ht : s ≤ t) (d f : Cover)
    (h : P.gridSpot t f - P.gridSpot t d ∈ P.starPair s n) :
    P.spotMat x s n t d f = P.rise x s n (P.gridSpot t f - P.gridSpot t d) := by
  ext1 Z Z'
  have he := P.bodyPair_rise x (P.gridSpot t d) (P.gridSpot t f) s n Z Z' J h.1
  let B := P.incB s n Z
  let D := P.incA Z' s n
  have hv : P.fullScroll t (usher B D) (usher d f) [false,true] = P.castAt B t d * P.castAt D t f := by
    change _ * (_ * 1) = _; rw [mul_one]; rfl
  obtain ⟨h₁,h₂⟩ := P.star_clear s n Z Z' _ _ h
  unfold bodyPair at he
  rw [P.gridSpot_usher] at h₁ h₂ he
  have ht' : ∀ i ∈ [false,true], ((usher B D) i).s ≤ t := by
    rintro (_|_) _ <;> exact ht
  exact Eq.trans (congrArg (P.singleState 3 t x) hv.symm)
    ((P.spot_full x _ _ (usher d f) J t ht' h₁ h₂).trans he)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
