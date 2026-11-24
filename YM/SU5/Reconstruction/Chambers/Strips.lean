import YM.SU5.Reconstruction.FirstWindows.MovingKets
/-!
# Strips as local Euclidean operators (with BOTH time edges, not time-zero!)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace Chambers
open Selected SlabMark MeshClock
variable (j : Axis)
set_option quotPrecheck false
local notation "D" => Domain Y H G
local notation "T" => flank j 0
local notation "R" => RSpace
local notation "kOff" => SingleMark -- unused
local notation "δ₁" => (timeMesh Λ)
local notation "M" => MeshClock.marks (timeMesh Λ) -- check
local notation "κ" t:max => ticket Y H G t
local notation "ξ" => coordinates Λ
local notation "V'₀" s:max => insideAt Λ l K false (flank j 0) s

-- The common time grid as Euclidean vector, visible at ANY level where length is.
def eject (j : Axis) {A : Type*} [Zero A] (x : A) : Axis→ A := Pi.single j x

@[simp] lemma eject_at {A : Type*} [Zero A] (x:A) : eject j x j=x := Pi.single_eq_same ..
@[simp] lemma eject_away {A : Type*} [Zero A] (x:A) (i : Axis) (h : i≠j) : eject j x i=0 := Pi.single_eq_of_ne h _
@[simp] lemma eject_zero {A : Type*} [Zero A] : eject j (0:A) = 0 := Pi.single_zero ..
@[simp] lemma coordinates_eject (q : MeshClock.marks (timeMesh Λ)) : coordinates Λ (eject j q)=eject j (q:ℝ) := by
  funext i; by_cases h : i=j <;> simp [h]
@[simp] lemma stamps_eject (s : ℕ) (x : ℤ) : stamps Λ s (eject j x)= eject j (notch δ₁ s x) := by
  ext1 i; by_cases h : i=j <;> simp [h,notch_zero]
lemma notch_nat_event (u : M) (p : (0:ℝ) < (u:ℝ)) : ∀ᶠ s in atTop, ∃ w : ℕ,
    0<w ∧ notch (timeMesh Λ) s (w:ℤ)=u := by
  obtain ⟨r,x,hx⟩ := notch_exists (timeMesh Λ) u
  filter_upwards [eventually_ge_atTop r] with s h
  let a := MeshClock.castor (timeMesh Λ) r s x
  have v : notch (timeMesh Λ) s a=u := (notch_up _ _ _ h _).trans hx
  have g : 0 < a := lt_of_not_ge fun q=> by
    have h := (bell_le (timeMesh Λ) s a 0).2 q
    have t : bell (timeMesh Λ) s a=u := congrArg Subtype.val v
    rw [t, bell, Int.cast_zero, zero_mul] at h; exact (not_le.mpr p) h
  exact ⟨a.toNat, by omega,by rwa [Int.toNat_of_nonneg g.le]⟩

def strip (j : Axis) (a b : ℝ) : Set RSpace := {x | a ≤ x j ∧ x j ≤ b}

lemma strip_zero (a b : ℝ) : slides (-(eject j a)) (strip j a b)=strip j 0 (b-a) := by
  ext x; constructor
  · rintro ⟨y,⟨p,w⟩,rfl⟩
    simp only [strip,Set.mem_setOf_eq,Pi.add_apply,Pi.neg_apply,eject_at]; constructor <;> linarith
  rintro ⟨s,h⟩; refine ⟨x+eject j a,?_,by simp⟩
  simp only [strip,Set.mem_setOf_eq,Pi.add_apply,eject_at]; constructor <;> linarith

lemma strip_in (b : ℝ) : strip j 0 b ⊆ flank j 0 := fun i h => h.1

variable (s w : ℕ)
local notation "height" => (whenly (timeMesh Λ) s w : ℝ)

-- exact limits of a footprint interval, standardizes side units for each spectator
lemma hull_iff_signed {S : Finset Cover} (a b : ℝ) :
    PhaseChoice.SupportedPhysically Λ l s S (strip j a b) ↔
      ∀ x∈ S, a ≤ gaugePosition Λ s x j - (reserve Λ l:ℝ)*gaugeMesh Λ s ∧
        gaugePosition Λ s x j + (reserve Λ l:ℝ)*gaugeMesh Λ s ≤ b := by
  let r : ℝ := (reserve Λ l:ℝ)*gaugeMesh Λ s
  have he : 0 ≤ r := by unfold r; have q := gaugeMesh_pos Λ s; positivity
  rw [supported_iff]
  constructor
  · intro y x h; let p:= gaugePosition Λ s x
    have hp1 : (p-eject j r) ∈ bufferedHull Λ l s S := by
      refine Set.mem_iUnion₂.mpr ⟨x,h,?_⟩; rw [shield_region_exact]; intro i _
      change p i - r ≤ p i-eject j r i ∧ p i- eject j r i≤ p i+r; by_cases h : i=j <;> simp [h, he]
      linarith
    have hp2 : (p+eject j r)∈ bufferedHull Λ l s S := by
      refine Set.mem_iUnion₂.mpr ⟨x,h,?_⟩; rw [shield_region_exact]; intro i _
      change p i-r ≤ p i+eject j r i ∧ p i + eject j r i ≤ p i+r
      by_cases h : i=j <;> simp [h, he]; linarith
    refine ⟨?_,?_⟩
    · simpa only [Pi.sub_apply,eject_at] using (show a≤ (p-eject j r) j from (y hp1).1)
    simpa only [Pi.add_apply,eject_at] using (show (p+eject j r) j ≤ b from (y hp2).2)
  intro h p hp; obtain ⟨x,e,hp⟩ := Set.mem_iUnion₂.mp hp; rw [shield_region_exact] at hp; specialize h x e
  exact ⟨h.1.trans (hp j (Set.mem_univ j)).1, (hp j (Set.mem_univ j)).2 |>.trans h.2⟩

lemma strip_seats {S : Finset Cover} :
    PhaseChoice.SupportedPhysically Λ l s S (strip j 0 (whenly (timeMesh Λ) s w : ℝ)) ↔
      Between (tent Y H) j 0 (ruler Λ.block*w) S := by
  rw [hull_iff_signed]; unfold Between
  have h := gaugeMesh_pos Λ s
  apply forall_congr' fun x=> forall_congr' fun _ => and_congr ?_ ?_
  · rw [gaugePosition,sub_nonneg,mul_le_mul_iff_left₀ h, zero_add]
    change _ ↔ ((reserve Λ l : ℕ):ℤ) ≤ _; exact_mod_cast Iff.rfl
  rw [double_clock_calibration, gaugePosition,← add_mul, mul_le_mul_iff_left₀ h]
  change _ ↔ x j+((reserve Λ l : ℕ):ℤ) ≤ _; exact_mod_cast Iff.rfl

-- Entry representation for any strip-supported location, validate after any later common rung as well
noncomputable def base (x : Entry Y H s j false w) : insideAt Λ l (tent Y H) false (flank j 0) s := fromField Y H j s x.val

lemma base_coverage (x : Entry Y H s j false w) : (base Y H j s w x).val ∈ insideAt Λ l K false (strip j 0 (height)) s := by
  obtain ⟨S,a,t⟩ := x.property; exact (mem_insideAt ..).2 ⟨⟨S,a,(strip_seats ..).2 t⟩,nofun⟩

noncomputable def startOp (f : (tent Y H |> Dome)) (h : f∈insideAt Λ l K false (strip j 0 (whenly (timeMesh Λ) s w : ℝ)) s) :
    Entry Y H s j false w := by
  let x : Tower.Field Y H s j 0 false := asField Y H j false s ⟨f,insideAt_mono (strip_in ..) h⟩
  refine ⟨x,?_⟩; obtain ⟨⟨S,t,a⟩,-⟩ := (mem_insideAt ..).1 h; exact ⟨S,t,(strip_seats ..).1 a⟩

@[simp] lemma base_start (f : Dome (tent Y H)) (h : f∈insideAt Λ l K false (strip j 0 (whenly (timeMesh Λ) s w : ℝ)) s) :
    (base Y H j s w (startOp Y H j s w f h)).val=f := rfl

lemma chart_eject {J : Calibration} (p : ℤ) (f : Dome J) :
    (reposition J (eject j p) f).val = relocate J j p f.val := by
  rw [reposition_val, chart_piece _ _ _ ((marque ..).mp f.property),eject_at]
  have he := transverse_eq J j (look j) (x:=f.val) (eject j p) (0:Trans j→ℤ) (fun i=>eject_away _ p _ i.property)
  have hp : gaea j 0 = 0 := by ext1 i; dsimp only [gaea]; split <;> rfl
  rw [he,hp,cad_zero _ _ ((marque ..).mp f.property)]

end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
