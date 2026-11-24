import YM.CF.BProof.Physical
import YM.CF.BPress.Test
import YM.SU5.FiniteGaugeData.LocalLimit.Voyage

/-! The pressure workers evaluate exactly the same compensated functional on
common gauge-only marks. The elected histories supply a bound after their
period-dependent cutoff, with a single period-independent exponent. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py.Rate.PressureIntegration
open Function Filter Lattice Wilson Finset MeasureTheory RG
open Vault Push.SectorMeasure Skye Scree Cube Fock Tulip Vale Vale.Grace Dial Spire Lat Paige Rush Scroll Drapes
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

variable {m B L : Side} {j : ℕ} {ho : Odd L.val}
  {Y : Pricing j L ho (Thread j)} {d : ℝ}
variable (D : GramM (mid m B)) (U : Grasp Y B d) (T : Loom (mid m B))

theorem common_mark (f : Fixed.Test (mid m B)) :
    BProof.numerator D U T f = BPress.reading U D T f := rfl

theorem common_unit :
    BProof.numerator D U T 1 = Complex.exp (-D.v) * partitionZ D U T ∧
    BPress.reading U D T 1 = Complex.exp (-D.v) * partitionZ D U T :=
  ⟨BProof.numerator_one D U T, BPress.reading_one U D T⟩

/-- Normalized readings of the shared gauge-only marks lose the offset
exactly, even though the absolute raw denominator retains that factor. -/
theorem common_ratio (f : Fixed.Test (mid m B)) :
    BProof.numerator D U T f / BProof.numerator D U T 1 = Fixed.evalNormalized U D T f := by
  rw [common_mark D U T f, common_mark D U T 1, BPress.reading_one]
  exact Fixed.strip_offset U D T f

theorem raw_norm (v Z : ℂ) :
    ‖Z‖ = Real.exp v.re * ‖Complex.exp (-v) * Z‖ := by
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, Real.exp_neg,
    ← mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul]

theorem raw_floor {v Z : ℂ} {h : ℝ} (paid : h ≤ ‖Complex.exp (-v) * Z‖) :
    Real.exp v.re * h ≤ ‖Z‖ := by
  rw [raw_norm v Z]
  exact mul_le_mul_of_nonneg_left paid (Real.exp_pos _).le

open LocalLimit LocalLimit.Preparation
variable {P : Preparation} {F : (s : Side) → Scree.Loom s → Prop} (C : Course P F)

abbrev Floor (i k : ℕ) : Prop :=
  let X := ((C.voyage i).X (C.uv k)).gram 0
  let T := (C.voyage i).CapeT 0
  let h := Real.exp (-C.τ * sites (cell (C.ir i) P.block P.R.L 0))
  h ≤ ‖BProof.numerator X P.U T 1‖ ∧ h ≤ ‖BPress.reading P.U X T 1‖

theorem paid (i k : ℕ) (after : (C.voyage i).kick ≤ k) : Floor C i k := by
  have b := (C.voyage i).lower k after
  let X := ((C.voyage i).X (C.uv k)).gram 0
  let T := (C.voyage i).CapeT 0
  obtain ⟨h₁,h₂⟩ := common_unit X P.U T
  exact ⟨h₁.symm ▸ b, h₂.symm ▸ b⟩

theorem paid_on_subsequence (i : ℕ) (u : ℕ → ℕ) (hu : StrictMono u) :
    ∀ᶠ k in atTop, Floor C i (u k) :=
  (hu.tendsto_atTop.eventually_ge_atTop (C.voyage i).kick).mono
    (fun k hk => paid C i (u k) hk)

theorem raw_on_course (i k : ℕ) (after : (C.voyage i).kick ≤ k) :
    let X := ((C.voyage i).X (C.uv k)).gram 0
    Real.exp X.v.re * Real.exp (-C.τ * sites (cell (C.ir i) P.block P.R.L 0)) ≤
      ‖partitionZ X P.U ((C.voyage i).CapeT 0)‖ :=
  raw_floor ((C.voyage i).lower k after)
end YM.CF.Py.Rate.PressureIntegration
