import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.TestField
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
-- elected character (axis d)
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  (D : Exhibition Y H i k I E L B)
variable (j d : Axis) (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
local notation "χ₀" => Dome (tent Y H)
local notation "Ĉ" => euclideanHalf Λ l (tent Y H) j
variable (c : (displayAlgebra Y H V G.history G.clipped d false (T d)) →⋆ₐ[ℂ] ℂ)
local notation "χ" => Selected.displacement Y H V G.history G.clipped d false (T d) c j (T j)
local notation "rχ" => resident Y H V G d false (T d) c
local notation "ρ" => indoor Y H V G.history G.clipped j false (T j) χ
local notation "P" => procession Y H V G.history G.clipped j false (T j) χ
local notation "Ω" => doorstep Y H V G.history G.clipped j false (T j) χ
local notation "Ψ" => matchGNS Y H V G j false (T j) d (T d) c
local notation "𝒱" s:max x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x
local notation "Θ" => onDrawing Y H V G D d T rχ

open MeshClock
local notation "St" => LinearMap.range (scan Y H V G D j d T c)
local notation "𝔞" => driveAlgebra Y H V G.history G.clipped j false (T j)
local notation "Δ" s:max => Selected.bud Y H V s G.history G.clipped j false (T j) χ
lemma can_report {x : ρ} : x∈ St ↔ ∃ (s : ℕ) (y : Tower.Field Y H s j 0 false), (Δ s) y=x := by
  change x∈ (St : Set (ρ)) ↔ _; rw [scan_range,stroll_exact]; simp only [mem_iUnion, Set.mem_range]

lemma scan_images {x : ρ} (p : x∈ St) :
    ∀ᶠ n : ℕ in atTop, ∃ y : Tower.Field Y H n j 0 true, (Δ n) (Selected.admit Y H n j y)=x := by
  obtain ⟨s,y,rfl⟩ := (can_report Y H V G D j d T c).mp p
  obtain ⟨b,hb,f,rfl⟩ := artist_fits_slab Y H s j false y
  obtain ⟨S,t,q⟩ := f.property
  obtain ⟨g,t,h⟩ := nearest_bud Y H V s G.history G.clipped j (T j) f hb t q
  have ht := congrArg (arrive Y H V G.history G.clipped j false (T j) χ) h
  rw [← Selected.turns, ← Selected.turns] at ht
  filter_upwards [eventually_ge_atTop (s+1)] with n hn
  exact ⟨Raise Y H G.history.circuit j 0 true (s+1) n hn g.val,
    (flourishes Y H V (s+1) G.history G.clipped j false (T j) χ n hn (Selected.composer Y H (s+1) j g).val).trans ht⟩ -- proof irrel update

lemma scan_box {s b : ℕ} (f : Entry Y H s j false b) (p : 0<b) (x : ρ) (h : x∈ St) :
    P (entrance Y H V s G.history G.clipped j false (T j) f p) x∈ St := by
  obtain ⟨i,⟨t,rfl⟩,ht⟩ := ((scan_images Y H V G D j d T c h).and (eventually_ge_atTop s)).exists
  rw [slot_high Y H V s G.history G.clipped j false (T j) χ f p i ht]
  exact (can_report Y H V G D j d T c).mpr ⟨i,_,rfl⟩
lemma scan_motion (a : Trans j) (z : marks (timeMesh Λ)) (x : ρ) (h : x∈ St) :
    P (shiftStamp Y H V G.history G.clipped j false (T j) a z) x ∈ St := by
  obtain ⟨s,i,rfl⟩ := notch_exists _ z
  obtain ⟨r,⟨y,rfl⟩,p⟩ := ((scan_images Y H V G D j d T c h).and (eventually_ge_atTop s)).exists
  rw [←notch_up (timeMesh Λ) s r p i, Selected.turns_across]; exact (can_report Y H V G D j d T c).mpr ⟨r,_,rfl⟩
lemma scan_heat (s i : ℕ) (x : ρ) (h : x∈ St) :
    (ride Y H V G.history G.clipped j false (T j) χ).E (whenly (timeMesh Λ) s i) x ∈ St := by
  rw [ride_advance, coat_mark]
  rcases Nat.eq_zero_or_pos i with q|q
  · subst i; rw [← coat_mark,←ride_advance, when_zero,(ride Y H V G.history G.clipped j false (T j) χ).eZero]; exact h
  rw [←entrance_heat Y H V s G.history G.clipped j false (T j) q]; exact scan_box Y H V G D j d T c _ q _ h

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
