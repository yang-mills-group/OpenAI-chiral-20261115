import YM.SU5.Obstruction.LateSlots
import YM.SU5.Obstruction.Conditional
import YM.SU5.Relativistic.Box
import YM.SU5.Reconstruct.Regions

/-!
# Mixed-level local retest in the resolution-polynomial system

Real first-link-only W in slot `n`, scalar normalized trace. J subtracts its
conditional expression in slot `n+1` and multiplies by the reciprocal of the
variance (proved pointwise in the conditional charts). All admitted in the
*actual* Pol of that footprint (even a narrow W); the overlapping product is
paid in the same Cloud. We never compute it by multiplying separately projected
operators. It detects W with a unit gap on this Exhibition; in particular it
reads exactly so on **every** character in the panel used here. Not a Gram
computation.
-/
set_option autoImplicit false
set_option maxHeartbeats 375000
set_option maxRecDepth 7500
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter MeasureTheory
open Lattice SU Buffered Buffered.Afterglow Tapestry Satin
open Py Py.Rate LocalLimit Preparation Journey Vale
open Tapestry.Altitude
open Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice Tower.Reconstruction
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
  {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Buffered.Family (tent Y H) → ℂ}
  {L : Rack Λ l} {B : Clay Λ l}

-- ambient, includes wide non-singlet inputs as well. Original physical location.
abbrev loosePol (U : Set RSpace) (s : Set ℕ) := jetty Λ l (tent Y H) true (handstamp U) s
/-- high-only, all heights > n. -/
abbrev higherOnly (n : ℕ) := loosePol Y H Set.univ (Set.Ici (n+1))

/-- This is the full high-only ambient unital algebra, i.e. no stencil neutrality hypotheses. -/
lemma higherOnly_eq (n : ℕ) :
    higherOnly Y H n = Algebra.adjoin ℂ (⋃ i ∈ Set.Ici (n+1),
      (pinhole (Dome (tent Y H)) i) '' Set.univ) := by
  rw [higherOnly, loosePol, generating, show handstamp Set.univ = Set.univ from rfl]
  simp_rw [fullKeep, vestibuleFull]; rfl

variable (n : ℕ) (p : Lattice.Face ℤ)
local notation "K" => tent Y H
local notation "A" => Dome K
local notation "S" => faceSites p
local notation "U" => footprint Λ l n S

def plaquetteWord : Cloud (Dome (tent Y H)) := pinhole A n (faceDome Y H p)
local notation "W" => plaquetteWord Y H n p

section Take
variable (D : Exhibition Y H a b I E L B)
local notation "F" s:max => Exhibition.vistaFinish Y H s D
local notation "X" => faceDome Y H p
local notation "T" => followBox (Λ:=Λ) (l:=l) (faceSites p)
local notation "Y₁" => D.liftD Y H n X
local notation "A₁" x:max => pinhole A (n+1) x
local notation "Z" => faceInverse Y H D n p

def countertest : Cloud (Dome (tent Y H)) := (plaquetteWord Y H n p - A₁ Y₁) * (A₁ Z)
local notation "J" => countertest Y H n p D

lemma footprint_advance : SupportedPhysically Λ l (n+1) T U :=
  shielding Λ l n (handstamp U) S (has_footprint Λ l n S)
lemma W_slot (w : Bool) : plaquetteWord Y H n p ∈ circum Λ l (tent Y H) w U {n} :=
  oneSlotWell Λ K l w (handstamp U) {n} n (Set.mem_singleton n)
    (x:=faceDome Y H p) ((keeps ..).mpr ⟨_, faceDome_bay Y H p w, has_footprint Λ l n S⟩)
    (faceDome_enclave Y H p)
lemma W_local : plaquetteWord Y H n p ∈ PolAt Y H n U :=
  PhaseChoice.circum_widens Y H Set.Subset.rfl
    (show ({n} : Set ℕ) ⊆ Set.univ ∩ Set.Iic n from Set.singleton_subset_iff.mpr ⟨Set.mem_univ n,Set.mem_Iic.mpr le_rfl⟩)
    (W_slot Y H n p true)
lemma inv_local : pinhole A (n+1) Z ∈ PolAt Y H (n+1) U :=
  oneSlotWell Λ K l true (handstamp U) _ _
    (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr le_rfl)) (x:=Z)
    ((keeps ..).mpr ⟨T, inverse_bay .., footprint_advance (Λ:=Λ) (l:=l) n p⟩) (inverse_enclave Y H D n p)
lemma J_local : countertest Y H n p D ∈ PolAt Y H (n+1) U := by
  have h1 : pinhole A (n+1) Y₁ ∈ PolAt Y H (n+1) U :=
    oneSlotWell Λ K l true (handstamp U) _ _
      (Set.mem_inter (Set.mem_univ _) (Set.mem_Iic.mpr le_rfl)) (x:=Y₁)
      ((keeps ..).mpr ⟨T, D.risePay Y H n _ (faceDome_bay Y H p true), footprint_advance (Λ:=Λ) (l:=l) n p⟩)
      (D.riseGauge Y H n (faceDome_enclave Y H p))
  have hw : W ∈ PolAt Y H (n+1) U := polAt_up Y H (Nat.le_succ n) (W_local ..)
  exact (PolAt Y H (n+1) U).mul_mem ((PolAt Y H (n+1) U).sub_mem hw h1) (inv_local ..)

lemma finish_step (x : A) :
    (F (n+1)) (pinhole (Dome (tent Y H)) n x) = D.liftD Y H n x := by
  unfold Exhibition.vistaFinish; rw [Decking.joins _ _ _ _ (short_pinhole n x), Decking.outcrop]; rfl

lemma finish_multiply (x : Cloud (Dome K)) (s : ℕ) (h : x ∈ shorter A s) (y : A) :
    (F s) (x * pinhole A s y) = (F s) x * y := crown_last _ _ _ _ h y

lemma W_permits : W ∈ shorter A (n+1) := climbs A (Nat.le_succ n) (short_pinhole n X)
private lemma difference_permits : W - (A₁ Y₁) ∈ shorter A (n+1) :=
  (shorter ..).sub_mem (W_permits Y H n p) (short_pinhole (n+1) Y₁)

lemma J_at_one : (F (n+1)) J = 0 := by
  unfold countertest
  rw [finish_multiply _ _ _ _ _ (difference_permits Y H n p D), map_sub, plaquetteWord, finish_step,
    Exhibition.vistaFinish, Decking.outcrop]
  change (Y₁ - Y₁) * Z = _; rw [sub_self, zero_mul]

lemma JW_at_one : (F (n+1)) (J * W) = 1 := by
  have hw := W_permits Y H n p
  have ht := (shorter ..).mul_mem (difference_permits Y H n p D) hw
  have hm : W*W = pinhole A n (X*X) := (map_mul ..).symm
  unfold countertest
  rw [mul_right_comm (W-A₁ Y₁), finish_multiply _ _ _ _ _ ht, sub_mul, mul_comm (A₁ Y₁) W,
    map_sub, finish_multiply _ _ _ _ _ hw, hm, finish_step]
  -- before any ascent from n+1 we see the variance product
  unfold plaquetteWord
  rw [finish_step]; exact inverse_identity ..

lemma JW_all (s : ℕ) (h : n+1 ≤ s) : (F s) (J * W) = 1 := by
  induction s,h using Nat.le_induction with
  | base => exact JW_at_one ..
  | succ s hs ih =>
    have hv := climbs A hs ((shorter ..).mul_mem (inside_budget Y H (J_local Y H n p D)) (W_permits Y H n p))
    have hp := Decking.joins (D.vistaDressing Y H) s (J * W) (auxiliaryPad K) hv
    rw [show (F (s+1)) (J*W) = D.liftD Y H s ((F s) (J*W)) from hp, ih]
    exact D.onePlaster Y H s

lemma J_high (s : ℕ) (h : n+1 ≤ s) (V : Set RSpace) (y : Cloud A)
    (v : y ∈ loosePol Y H V (Set.Ici (n+1) ∩ Set.Iic s)) : (F s) (J*y) = 0 :=
  crown_later_poly (D.vistaDressing Y H) (auxiliaryPad K) J (inside_budget Y H (J_local Y H n p D))
    (J_at_one ..) s h _ Set.inter_subset_left Set.inter_subset_right
    (fun i => keep Λ l i K true (handstamp V)) v

private lemma heightCertificate (y : Cloud A) (v : y ∈ higherOnly Y H n) :
    ∃ s : ℕ, n+1 ≤ s ∧
      y ∈ loosePol Y H Set.univ (Set.Ici (n+1) ∩ Set.Iic s) ∧ J*y ∈ shorter A s := by
  obtain ⟨s,w⟩ := entrusted Λ l K true (handstamp Set.univ) _ v
  let j := max (n+1) s
  have a : n+1 ≤ j := le_max_left ..
  have b : s ≤ j := le_max_right ..
  have ht : y ∈ loosePol Y H Set.univ (Set.Ici (n+1) ∩ Set.Iic j) := by
    apply admits Λ l K true _ _ _ _ _ Set.Subset.rfl w
    exact Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr b)
  exact ⟨j,a,ht,(shorter ..).mul_mem (climbs A a (inside_budget Y H (J_local Y H n p D)))
    (jettyBan Λ l K true _ _ _ ht)⟩

theorem vista_JW : D.vistaTake Y H (J*W) = 1 := by
  rw [Exhibition.vistaCall Y H (n+1) _ D
    ((shorter ..).mul_mem (inside_budget Y H (J_local Y H n p D)) (W_permits Y H n p)), JW_at_one, Exhibition.planet1]

theorem vista_high (y : Cloud A) (v : y ∈ higherOnly Y H n) :
    D.vistaTake Y H (J*y) = 0 := by
  obtain ⟨s,h,hv,w⟩ := heightCertificate Y H n p D y v
  rw [Exhibition.vistaCall Y H s _ D w, J_high Y H n p D s h _ y hv,map_zero]
end Take

section Character
variable {T : ℕ → ℕ → Tariff} {t : ℕ → Tariff} (D : Fashion Y H a b I E L B T t)
  (G : SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
  (C : ∀ j : Axis, Tower.Arena Y H G.history.circuit j 0 false)
  (c : (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
local notation "J" => countertest Y H n p D.toExhibition

lemma sch_via_same {s : ℕ} (x y : Cloud A) (hx : x ∈ shorter A s) (hy : y ∈ shorter A s)
    (h : D.toExhibition.vistaFinish Y H s x = D.toExhibition.vistaFinish Y H s y) :
    sch Y H D G C c x = sch Y H D G C c y := by rw [sch_mark _ _ _ _ _ _ _ hx, sch_mark _ _ _ _ _ _ _ hy,h]

lemma sch_identity : sch Y H D G C c 1 = 1 := by
  rw [sch_mark Y H D G C c 0 (shorter ..|>.one_mem), Exhibition.vistaFinish, Decking.crown1,
    show fieldArg Y H 1 = (1 : Marks K false) from rfl, Selected.response, located_one,map_one]

theorem sch_JW : sch Y H D G C c (J*W) = 1 := by
  rw [← sch_identity Y H D G C c]
  apply sch_via_same _ _ _ _ _ _ (s:=n+1) _ _
    ((shorter ..).mul_mem (inside_budget Y H (J_local Y H n p D.toExhibition)) (W_permits Y H n p)) (shorter ..|>.one_mem)
  rw [JW_at_one, Exhibition.vistaFinish, Decking.crown1]

theorem sch_high (y : Cloud A) (v : y ∈ higherOnly Y H n) :
    sch Y H D G C c (J*y) = 0 := by
  obtain ⟨s,h,hv,w⟩ := heightCertificate Y H n p D.toExhibition y v
  have H' := sch_via_same Y H D G C c _ 0 w ((shorter ..).zero_mem) ((J_high _ _ _ _ _ _ h _ _ hv).trans (map_zero _).symm)
  rw [H',map_zero]

/-- Exact unit gap; cost of J from whole words (including JW in the very
same Pol algebra, on the very same support). -/
theorem unit_gap :
    W ∈ PolAt Y H n U ∧ J ∈ PolAt Y H (n+1) U ∧
    J*W ∈ PolAt Y H (n+1) U ∧
    sch Y H D G C c (J*W) = 1 ∧
    ∀ y : Cloud A, y ∈ higherOnly Y H n → sch Y H D G C c (J*y) = 0 :=
  ⟨W_local .., J_local Y H n p D.toExhibition, (PolAt ..).mul_mem (J_local Y H n p D.toExhibition)
    (polAt_up Y H (Nat.le_succ n) (W_local ..)), sch_JW .., sch_high Y H n p D G C c⟩

end Character

end YM.CF.SatinRotation
#print axioms YM.CF.SatinRotation.unit_gap
#print axioms YM.CF.SatinRotation.vista_JW
#print axioms YM.CF.SatinRotation.vista_high
