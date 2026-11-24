import YM.SU5.Six.CostBody
set_option autoImplicit false
set_option maxHeartbeats 380000
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
variable (P : Spine)
local notation "ℓ" => P.calibration.ℓ
local notation "b" => ruler P.par.block
local notation "Δ" => timeMesh P.par
local notation "κ" => P.calibration
variable (Z : Window.Family) (s n : ℕ)

/-- `F_{Z i}` at height s. -/
def incF : P.Test := P.stockS Z (P.flash n) - P.shifts 3 (P.incStep n) (P.stockS Z (P.flash n))
-- here Lean args Z,n not s
/-- Stencil budget. -/
def incS : Finset Cover :=
  (P.flash n).patio ∪ plow κ 3 (P.incStep n) (P.flash n).patio

lemma flash_real : P.stockS Z (P.flash n) ∈ enclave κ := P.celebrity (flourish _ _)
lemma incF_real : P.incF Z n ∈ enclave κ := (enclave κ).sub_mem (P.flash_real Z n)
    (P.shifts_keep 3 _ (P.flash_real Z n))
lemma incF_bay : P.incF Z n ∈ bay κ (P.incS n) true := by
  have h := P.visibility Z n
  have hw := P.shifts_support 3 (P.incStep n) _ h
  exact (bay κ _ true).sub_mem ((tallerBay _ _ _ Finset.subset_union_left) h)
    ((tallerBay _ _ _ Finset.subset_union_right) hw)

lemma flash_range (v : Cover) (hv : v ∈ (P.flash n).patio) :
    2 * ((ℓ:ℤ)+n) + 1 ≤ v 3 ∧ v 3 ≤ 2 * ((ℓ:ℤ)+2*n) + 1 := by
  obtain ⟨t,h,rfl⟩ := Cube.range_leg _ (posDir 3) (2*n) v (List.mem_toFinset.mp hv)
  simp [flash,kernel0,nodeC]; omega
lemma incS_spatial (j : Axis) (hj : j ≠ 3) (v : Cover) (hv : v ∈ P.incS n) : v j = 1 := by
  rcases mem_union.mp hv with h|h; · exact P.flash_fixed j n v h hj
  obtain ⟨y,t,rfl⟩ := plow_stays _ _ _ _ h
  rw [SlabMark.moves, if_neg hj]; exact P.flash_fixed j n y t hj
lemma incS_between : Between κ 3 0 (P.extentG n) (P.incS n) := by
  have h : 0 ≤ b*(P.incStep n) := mul_nonneg (ruler_gene _).le (Int.natCast_nonneg _)
  intro v hv
  unfold extentG
  rcases mem_union.mp hv with t | t
  · have := P.flash_range n _ t; omega
  obtain ⟨y,t',rfl⟩ := plow_stays _ _ _ _ t
  rw [SlabMark.moves, if_pos rfl, show ruler (κ).B = b by rfl]
  have := P.flash_range n _ t'; omega

lemma incS_shelter (j : Axis) :
    Between κ j (- b * P.costU n j) (b * P.costU n j) (P.incS n) := by
  intro v hv
  by_cases h : j = 3
  · subst j
    rw [neg_mul]
    have hb := P.incS_between n v hv
    have hp := P.extentG_paid n
    have hp' := P.extentG_pos n; omega
  rw [neg_mul, P.incS_spatial n j h v hv]
  have : (ℓ:ℤ) + 1 ≤ b * P.costU n j := by
    rw [costU, if_neg h,Nat.cast_add,Nat.cast_one]
    exact le_mul_of_one_le_left (by positivity) (ruler_gene _)
  omega

/-- The actual macro body `A_{Z i}` of `Macropositions`, here at s with n. -/
def incA : P.Apron := ⟨s, P.costU n, P.costU_pos n, P.incF Z n, P.incS n,
    P.incF_bay Z n, P.incF_real Z n, P.incS_shelter n⟩
lemma incA_width (j : Axis) : (P.incA Z s n).realWidth P j = P.costW s n j := rfl
lemma incF_bright : P.birthF 3 s (P.incF Z n) :=
  P.criteria 3 s (P.incF_bay Z n) (fun v hv => (P.incS_between n v hv).1) (P.incF_real Z n)

lemma incF_zero (x : P.Spectrum0 3) : P.singleState 3 s x (P.incF Z n) = 0 := by
  rw [incF, map_sub, P.slide_single, sub_self]

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
