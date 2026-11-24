import YM.SU5.Reconstruction.FirstWindows.Spaces
/-!
# Calibration, including compact supports, before passing to any Minkowski chart

Relate both workers' physical coordinates, keep native AP shifts. Don't read either
inner or outer cones (in order of UV→IR limits) as authorizing a moving physical mark.
No boost metric here; translates use the same fermion-unit ruler as `timeMesh`. -/
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
open MeshClock
variable {J : Calibration} {q : Bool}
variable {U W : Set RSpace}
local notation "D" => Domain Y H G

section support

/-- Tapestry uses gauge level-zero spacing as unit; use the same conversion as
PhaseChoice to matter framing (time reads in this unit). -/
def toMatterUnits (x : RSpace) : RSpace := fun j => x j / 2

theorem toMatterUnits_continuous : Continuous toMatterUnits :=
  continuous_pi fun j => (continuous_apply j).div_const _

/-- Check intercalibration. -/
theorem location_eq (Λ : Preparation) (s : ℕ) (x : Cover) :
    PhaseChoice.location Λ s x = gaugePosition Λ s x := by
  funext j
  simp only [PhaseChoice.location, gaugePosition,gaugeMesh,markZ,precisionAt]
  ring

@[simp] theorem two_mesh_prec (Λ : Preparation) (s : ℕ) :
    (2 * precisionAt Λ s) * gaugeMesh Λ s = 1 := by
  exact mul_one_div_cancel (show 2*precisionAt Λ s ≠ 0 by
    have h := positiveScale Λ s
    positivity)

def bufferedHull (Λ : Preparation) (l s : ℕ) (S : Finset Cover) : Set RSpace :=
  ⋃ x ∈ S, toMatterUnits '' Tapestry.shield Λ l s x

variable (Λ l) (s : ℕ) (S : Finset Cover)

local notation "aₜ" => gaugeMesh Λ s
local notation "pₜ" => gaugePosition Λ s
local notation "rₜ" => ((reserve Λ l : ℝ) * gaugeMesh Λ s)

lemma shifted_shield (x : Cover) (p : RSpace) :
    p ∈ Tapestry.shield Λ l s x ↔ ∀ j : Axis, |toMatterUnits p j - pₜ x j| ≤ rₜ := by
  have h (j : Axis) : |toMatterUnits p j - pₜ x j| = aₜ * |precisionAt Λ s * p j - x j| := by
    rw [show toMatterUnits p j - pₜ x j = aₜ * (precisionAt Λ s * p j - x j) from ?_, abs_mul,abs_of_pos (gaugeMesh_pos ..)]
    simp only [toMatterUnits,gaugePosition, gaugeMesh,precisionAt]
    have hp : 0 < (Λ.R.L.val:ℝ) := by exact_mod_cast Λ.R.L.property
    field_simp
  change (∀ j : Axis, _ ≤ _) ↔ _
  simp_rw [h]
  rw [mul_comm (reserve Λ l:ℝ)]
  simp only [mul_le_mul_iff_right₀ (gaugeMesh_pos Λ s)]

lemma shield_region_exact (x : Cover) : toMatterUnits '' Tapestry.shield Λ l s x =
    (univ : Set Axis).pi (fun j => Icc (gaugePosition Λ s x j - rₜ) (gaugePosition Λ s x j + rₜ)) := by
  ext p; constructor
  · rintro ⟨y,h,rfl⟩ j -
    obtain ⟨a,b⟩ := abs_le.mp ((shifted_shield Λ l s x y).1 h j)
    exact ⟨by linarith,by linarith⟩
  intro h; let y : RSpace := fun i => 2 * p i
  have hh : toMatterUnits y = p := by ext i; change 2 * p i / 2 = p i; ring
  refine ⟨y,(shifted_shield Λ l s x y).2 (fun j => ?_), hh⟩
  rw [hh,abs_le]; obtain ⟨a,b⟩ := h j (Set.mem_univ j); constructor <;> linarith

@[simp] theorem compact_hull : IsCompact (bufferedHull Λ l s S) := by
  simp_rw [bufferedHull,shield_region_exact]
  exact S.isCompact_biUnion fun i _ => isCompact_univ_pi fun _ => isCompact_Icc

theorem supported_iff : PhaseChoice.SupportedPhysically Λ l s S U ↔ bufferedHull Λ l s S ⊆ U := by
  simp_rw [bufferedHull, Set.iUnion_subset_iff, Set.image_subset_iff]
  rfl

@[simp] theorem hull_support : PhaseChoice.SupportedPhysically Λ l s S (bufferedHull Λ l s S) :=
  (supported_iff ..).2 Set.Subset.rfl

theorem hull_persists (n : ℕ) : bufferedHull Λ l (s+n) (volumeAround Λ l n S) ⊆ bufferedHull Λ l s S :=
  (supported_iff ..).1 ((hull_support Λ l s S).persists n)

theorem center_in_hull {x : Cover} (p : x ∈ S) : gaugePosition Λ s x ∈ bufferedHull Λ l s S := by
  rw [←location_eq]; exact (hull_support Λ l s S).contains p

-- use the compact support, not merely centers, in checking noncontact.
variable (j : Axis) {T : Finset Cover} {δ : ℝ}
theorem separated_hulls (h : PhysicalHush (Λ:=Λ) (l:=l) s j S T δ)
    {p w : RSpace} (a : p ∈ bufferedHull Λ l s S) (b : w ∈ bufferedHull Λ l s T) : p j + δ ≤ w j := by
  obtain ⟨x,hx,v⟩ := Set.mem_iUnion₂.mp a
  obtain ⟨y,hy,z⟩ := Set.mem_iUnion₂.mp b
  replace v : p j ≤ pₜ x j + rₜ := ((shield_region_exact Λ l s x ▸ v) j (Set.mem_univ j)).2
  replace z : pₜ y j - rₜ ≤ w j := ((shield_region_exact Λ l s y ▸ z) j (Set.mem_univ j)).1
  have e : pₜ x j + rₜ + δ ≤ pₜ y j - rₜ := h.2 0 x hx y hy
  linarith

theorem separated_disjoint (h : PhysicalHush (Λ:=Λ) (l:=l) s j S T δ) :
    Disjoint (bufferedHull Λ l s S) (bufferedHull Λ l s T) := by
  apply Set.disjoint_left.mpr
  intro p a b
  linarith [separated_hulls Λ l s S j h a b,h.1]

end support

theorem compact_domain {x : Sky K} : x ∈ D q U ↔ ∃ A : Set RSpace,
    IsCompact A ∧ A ⊆ U ∧ x ∈ D q A := by
  constructor
  · rintro ⟨s,f,p,rfl⟩
    obtain ⟨⟨S,e,h⟩,v⟩ := (mem_insideAt f s).1 p
    exact ⟨_,compact_hull Λ l s S,(supported_iff ..).1 h,
      ticket_mem Y H G ((mem_insideAt f s).2 ⟨⟨S,e,hull_support _ _ _ _⟩,v⟩)⟩
  rintro ⟨_,_,h,v⟩; exact domain_mono Y H G h v

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
