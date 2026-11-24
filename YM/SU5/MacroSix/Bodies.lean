import YM.SU5.Aria.Grotto

/-! # The positioned macroscopic six-field bodies

Exact stock mark (`Lead` open path with the chiral letter pair), the time-*difference*
test, and `Apron`s with the widths of `the construction notes`. With the book's
`mill` in physical (fermion) units, not gauge-coordinate `markZ`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Sods Prototype

namespace Spine

variable (P : Spine) (s n : ℕ) (Z : Window.Family)
local notation "K" => P.calibration
local notation "R" => ruler P.par.block
local notation "d" => ((ruler P.par.block:ℤ):ℝ)
local notation "ℓ" => P.calibration.ℓ
local notation "M" => timeMesh P.par

/-- `a'_i` of Macropositions (on n=`r i`). Count in full ticks. -/
def advanceCount : ℕ := ⌈(n:ℝ)/((ruler P.par.block:ℤ):ℝ)⌉₊

def travelTime : ℝ≥0 := whenly (timeMesh P.par) s (P.advanceCount n)

def timeTest : P.Test := P.stockS Z (P.flash n) -
  P.shifts 3 (P.advanceCount n:ℤ) (P.stockS Z (P.flash n))

def timeSupport : Finset Cover := (P.flash n).patio ∪
  plow P.calibration 3 (P.advanceCount n) (P.flash n).patio

def timeBudget : ℕ := 1 + ⌈((2*((ℓ:ℝ)+2*(n:ℝ))+1) +
    ((ruler P.par.block:ℤ):ℝ)*(P.advanceCount n:ℝ) + (ℓ:ℝ))/((ruler P.par.block:ℤ):ℝ)⌉₊

def sixBudget (j : Axis) : ℕ := if j=3 then P.timeBudget n else ℓ+1

lemma sixBudget_pos (j : Axis) : 0 < P.sixBudget n j := by unfold sixBudget timeBudget; split <;> omega

lemma advanceCount_pos (h : 0 < n) : 0 < P.advanceCount n := by
  have hr : 0 < (d) := by exact_mod_cast ruler_gene P.par.block
  exact Nat.one_le_ceil_iff.mpr (div_pos (by exact_mod_cast h) hr)

lemma travelTime_pos (h : 0 < n) : 0 < P.travelTime s n :=
  when_pos M s (P.advanceCount n) (P.advanceCount_pos n h)

lemma timeTest_singlet : P.timeTest n Z ∈ enclave K :=
  let h : P.stockS Z (P.flash n) ∈ enclave K := P.celebrity (flourish _ _)
  (enclave K).sub_mem h (P.shifts_keep _ _ h)

lemma timeTest_bay : P.timeTest n Z ∈ bay K (P.timeSupport n) true :=
  let h : P.stockS Z (P.flash n) ∈ bay K _ true := P.visibility Z n
  (bay K _ true).sub_mem
    (tallerBay K _ true (Finset.subset_union_left (s₂:=plow K 3 (P.advanceCount n) (P.flash n).patio)) h)
    (tallerBay K _ true (Finset.subset_union_right (s₁:=(P.flash n).patio))
      (P.shifts_support 3 _ _ h))

private lemma timeSupport_estimate :
    2*((ℓ:ℤ)+2*(n:ℤ))+1 + R * (P.advanceCount n:ℤ) + (ℓ:ℤ) ≤
      R * (P.timeBudget n:ℤ) := by
  let C := (2*((ℓ:ℝ)+2*(n:ℝ))+1) + (d)*(P.advanceCount n:ℝ) + (ℓ:ℝ)
  have hr : 0 < (d) := by exact_mod_cast ruler_gene P.par.block
  have hz : C / (d) ≤ P.timeBudget n :=
    (Nat.le_ceil (C/(d))).trans (by
      exact_mod_cast (show ⌈C / (d)⌉₊ ≤ P.timeBudget n from (by unfold timeBudget C; omega)))
  rw [div_le_iff₀ hr] at hz; rw [mul_comm] at hz; unfold C at hz
  exact_mod_cast hz

lemma patio_time_upper (x : Cover) (p : x ∈ (P.flash n).patio) :
    x 3 ≤ 2*((ℓ:ℤ)+2*(n:ℤ))+1 := by
  obtain ⟨t,h,rfl⟩ := Cube.range_leg _ (posDir 3) (2*n) x (List.mem_toFinset.mp p)
  simp [flash,kernel0,nodeC]; omega

lemma timeSupport_region : Tower.region 3 0 ℓ (P.timeSupport n) := by
  intro x p
  rcases mem_union.mp p with h | h
  · exact P.flash_here n x h
  obtain ⟨u,h',rfl⟩ := plow_stays K 3 (P.advanceCount n) (P.flash n).patio h
  rw [SlabMark.moves,if_pos rfl]
  exact le_trans (P.flash_here n u h')
    (le_add_of_nonneg_right (mul_nonneg (ruler_gene _).le (Nat.cast_nonneg _)))

lemma timeSupport_vertical : Between K 3 0 (R*(P.timeBudget n:ℤ)) (P.timeSupport n) := by
  intro x p
  refine ⟨P.timeSupport_region n x p, ?_⟩
  have he := P.timeSupport_estimate n
  rcases mem_union.mp p with h | h
  · have hp := P.patio_time_upper n x h
    have hw := mul_nonneg (ruler_gene P.par.block).le (Nat.cast_nonneg (α:=ℤ) (P.advanceCount n))
    linarith
  obtain ⟨u,h',rfl⟩ := plow_stays K 3 (P.advanceCount n) (P.flash n).patio h
  have hp := P.patio_time_upper n u h'
  rw [SlabMark.moves,if_pos rfl,show ruler (K).B=R from rfl]
  linarith

lemma timeSupport_transverse (x : Cover) (p : x ∈ P.timeSupport n) (j : Axis) (q : j ≠ 3) :
    x j=1 := by
  rcases mem_union.mp p with h | h
  · exact P.flash_fixed j n _ h q
  obtain ⟨u,h',rfl⟩ := plow_stays K 3 (P.advanceCount n) (P.flash n).patio h
  rw [SlabMark.moves,if_neg q]; exact P.flash_fixed j n _ h' q

lemma timeTest_shelter (j : Axis) : Between K j (- R * (P.sixBudget n j:ℤ))
      (R * (P.sixBudget n j:ℤ)) (P.timeSupport n) := by
  unfold sixBudget; split
  · subst j; intro x p; obtain ⟨hp,h⟩ := P.timeSupport_vertical n x p
    refine ⟨le_trans ?_ hp,h⟩
    have he := mul_nonneg (ruler_gene P.par.block).le (Nat.cast_nonneg (α:=ℤ) (P.timeBudget n))
    linarith
  rename_i h
  intro x p
  rw [P.timeSupport_transverse n x p j h]
  have he : ((ℓ+1:ℕ):ℤ) ≤ R*((ℓ+1:ℕ):ℤ) := le_mul_of_one_le_left (by positivity) (ruler_gene _)
  rw [neg_mul]; omega

/-- All probes F are already positive-support singlet (in the time-3 grammar). -/
lemma timeTest_birth : P.birthF 3 s (P.timeTest n Z) :=
  P.criteria 3 s (P.timeTest_bay n Z) (P.timeSupport_region n) (P.timeTest_singlet n Z)

/-- The test body `A_{Zi}` at `s n`, with full shield widths; call at `s=c i, n=r i`. -/
def sixBody : P.Apron where
  s := s
  u := P.sixBudget n
  pos := P.sixBudget_pos n
  F := P.timeTest n Z
  S := P.timeSupport n
  bay := P.timeTest_bay n Z
  realM := P.timeTest_singlet n Z
  shelter := P.timeTest_shelter n

/-- Use also this nonnegative-real presentation. (`realWidth` in Vantage is in physical
units; only `scenery` then uses doubled coordinates.) -/
def sixWidth (j : Axis) : ℝ≥0 := whenly (timeMesh P.par) s (P.sixBudget n j)

lemma sixBody_width (j : Axis) : (P.sixBody s n Z).realWidth P j = (P.sixWidth s n j:ℝ) :=
  natural_time (timeMesh P.par) s (P.sixBudget n j)

lemma sixWidth_pos (j : Axis) : 0 < P.sixWidth s n j := when_pos M s _ (P.sixBudget_pos n j)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.sixBody
