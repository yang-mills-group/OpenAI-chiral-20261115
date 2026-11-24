import YM.SU5.Six.Aprons
import YM.SU5.Relativistic.Box
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open Aria Set
open Cheer (Narrow)
/-!
# Charge the *support price* before any finer reading

Use spacetime with gauge-site spacing as in Selected.gaugeMesh, i.e. exactly
half the Tapestry support unit conversions. P.laysM ticks are already clock
in this physical conversion. -/
variable (P:Spine)(s t:ℕ)(S D:Finset Cover)
local notation "K"=>P.calibration
local notation "Λ"=> P.par
local notation "l"=>P.width
-- In Vantage COORDINATES (all other test data in these units too).
def Aperture (A:P.Apron)(p:Vantage): Set Vantage:= {q|∀ i:Axis, |q i-p i|≤ A.realWidth P i}
def pinFoot : Set Vantage:= {x|∃ i∈ S,(2:ℝ) • x∈ Tapestry.shield Λ l s i}
open Tower.Reconstruction
lemma usual_footprint : P.pinFoot s S=Tower.Reconstruction.footprint Λ l s S:= by
  ext x
  simp only [pinFoot,Tower.Reconstruction.footprint,Set.mem_setOf_eq,Set.mem_iUnion, Finset.mem_coe]
  refine exists_congr fun i => ?_
  rw [exists_prop, shield_collar]
  refine and_congr_right fun _ => ?_
  change (fun j:Axis => (2*x j)/2)∈ Tower.Reconstruction.collar Λ l s i ↔ _
  rw [show (fun j:Axis => (2*x j)/2)=x from funext fun j=>by ring]
lemma pin_mono (p:S⊆D): P.pinFoot s S ⊆ P.pinFoot s D:=by rintro x ⟨i,u,h⟩; exact ⟨i,p u,h⟩
lemma pin_onward (p:s≤t): P.pinFoot t (volumeAround Λ l (t-s) S) ⊆ P.pinFoot s S:= by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le p
  rw [P.usual_footprint,P.usual_footprint, Nat.add_sub_cancel_left]; exact Reconstruction.covers_footprint Λ l s S k
lemma pin_disjoint (p:Disjoint (P.pinFoot s S) (P.pinFoot s D)):Disjoint S D:=by
  apply Finset.disjoint_left.mpr
  intro i h u
  let y:Vantage:=fun j=> markZ Λ s (i j)/2
  have he:(2:ℝ) • y∈ Tapestry.shield Λ l s i:=by
    have he:(2:ℝ) • y=(fun j=>markZ Λ s (i j)):=by ext; simp [y]; ring
    rw [he]; exact Tapestry.treads Λ l s i
  exact Set.disjoint_left.mp p (show y∈P.pinFoot s S from ⟨i,h,he⟩) ⟨i,u,he⟩
lemma aperture_licensed (A:P.Apron) : P.pinFoot A.s A.S ⊆ P.Aperture A 0:=by
  rintro g ⟨i,h,u⟩ j
  have ht:=A.efficiency P i h u j
  change |g j-0|≤ _; change |2*g j-2*0|≤_ at ht; rw [sub_zero]; rw [mul_zero,sub_zero,abs_mul,abs_of_pos zero_lt_two] at ht; linarith

-- Move *each* charged stencil
variable (j:Axis)(n:ℤ)(L:List Axis)(r:Cover)
def placeSet : Finset Cover:= L.foldr (fun i W=> plow K i (r i) W) S
-- argument order adjust to S BEFORE L (section binders)
lemma step_back_pin {x:Vantage}(p:x∈P.pinFoot s (plow K j n S)): x-P.plenumShift s j n∈P.pinFoot s S:= by
  obtain ⟨i,t,u⟩:=p
  obtain ⟨i,h,rfl⟩:= plow_stays K j n S t
  refine ⟨i,h,?_⟩
  rw [smul_sub]
  have he : (2:ℝ) • P.plenumShift s j n=(2:ℕ) • P.plenumShift s j n:=by apply funext; intro y; simp only [two_smul]
  rw [he]; exact P.step_shield j s n i _ u
lemma place_back_pin {x:Vantage}(p:x∈P.pinFoot s (P.placeSet S L r)): x-P.jettyT s r L ∈ P.pinFoot s S:=by
  induction L generalizing x with
  | nil=> simpa only [jettyT,placeSet,List.foldr_nil,List.map_nil,List.sum_nil,sub_zero] using p
  | cons i L h=>
    have he:= h (P.step_back_pin s (P.placeSet S L r) i _ p)
    rw [show P.jettyT s r (i::L)=P.plenumShift s i (r i)+ P.jettyT s r L from rfl, ← sub_sub]; exact he
lemma pin_relocate (p:Disjoint (P.pinFoot s S) (P.pinFoot s D)): Disjoint (P.pinFoot s (plow K j n S)) (P.pinFoot s (plow K j n D)):= Set.disjoint_left.mpr fun _i h u=> Set.disjoint_left.mp p (P.step_back_pin s S j n h) (P.step_back_pin s D j n u)
lemma mirror_back_pin {x:Vantage}(p:x∈P.pinFoot s (Tower.reflectedBox j 0 S)): mirrorΩ j x∈P.pinFoot s S:=by
  obtain ⟨q,t,u⟩:=p
  obtain ⟨a,h,c⟩:= SlabMark.reflect_stays j 0 S t
  refine ⟨a,h,?_⟩
  intro k; specialize u k; rw [c] at u
  by_cases p:k=j; swap; · rw [if_neg p] at u; simpa only [Pi.smul_apply,mirrorΩ,if_neg p] using u
  rw [if_pos p,mul_zero,add_zero,Int.cast_neg] at u
  change |(precisionAt Λ s)*(2*((mirrorΩ j x) k))-(a k:ℝ)|≤_
  change |(precisionAt Λ s)*(2*x k)- - (a k:ℝ)| ≤ _ at u
  rw [mirrorΩ,if_pos p,mul_neg,mul_neg, show -(precisionAt Λ s * (2*x j)) - ↑(a k)= -(precisionAt Λ s*(2*x j)+↑(a k)) from by ring,abs_neg]
  subst k
  simpa only [sub_neg_eq_add] using u
lemma pin_reflect (p:Disjoint (P.pinFoot s S) (P.pinFoot s D)) : Disjoint (P.pinFoot s (Tower.reflectedBox j 0 S)) (P.pinFoot s (Tower.reflectedBox j 0 D)):= Set.disjoint_left.mpr fun _i h u=> Set.disjoint_left.mp p (P.mirror_back_pin s S j h) (P.mirror_back_pin s D j u)
lemma place_mono (p:S⊆D) : P.placeSet S L r ⊆ P.placeSet D L r:=by
  induction L with
  | nil=> exact p
  | cons i L h=> exact Finset.image_subset_image h
lemma place_distinct (p:Disjoint (P.pinFoot s S) (P.pinFoot s D)): Disjoint (P.pinFoot s (P.placeSet S L r)) (P.pinFoot s (P.placeSet D L r)):=
  Set.disjoint_left.mpr fun _i u v=> Set.disjoint_left.mp p (P.place_back_pin _ _ L r u) (P.place_back_pin _ _ L r v)
lemma place_test {x:P.Test}(p:x∈ bay K S true) : P.cruise L r x∈ bay K (P.placeSet S L r) true:= by
  induction L with
  | nil=> exact p
  | cons i L h=> rw [P.cruise_step,AlgHom.comp_apply]; exact P.shifts_support i (r i) _ h

def meshPose (t:ℕ)(r:Cover):Vantage := P.laysM (P.vtile t r)
def issuing (t:ℕ)(A:P.Apron)(r:Cover): P.Test:= P.chartAll r (A.full P t)
def plotSet (t:ℕ) (A:P.Apron)(r:Cover): Finset Cover:= P.placeSet (volumeAround Λ l (t-A.s) A.S) Vacancy.ordinate r
variable (A:P.Apron)
lemma inside_now (p:A.s≤t): P.pinFoot t (P.plotSet t A r) ⊆ P.Aperture A (P.meshPose t r) := by
  intro x a
  have ht:= P.place_back_pin t _ Vacancy.ordinate r a
  rw [P.jettyT_full] at ht
  intro i; simpa only [Pi.zero_apply, sub_zero,Pi.sub_apply,meshPose] using P.aperture_licensed A (P.pin_onward A.s t A.S p ht) i
lemma issuing_support : P.issuing t A r∈bay K (P.plotSet t A r) true:=
  P.place_test _ Vacancy.ordinate r (x:=A.full P t) (by
    exact (Tower.proceeds P.run P.large P.history.circuit A.s (t-A.s) ((Tapestry.locates ..).1 A.bay)).1)
lemma issuing_color : P.issuing t A r∈enclave K:= P.cruise_color Vacancy.ordinate r (A.fullColor P t)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
