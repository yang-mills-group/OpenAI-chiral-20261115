import YM.SU5.Aria.Grotto
/-! Tick costs for the six macro bodies at resolution s with flash n. -/
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

/-- Ceiling in macro full-tick units from an integer cost. -/
def ticksUp (d : ℤ) : ℕ := ⌈(d : ℝ) / b⌉₊
/-- `a'_i`; feed `r i`. -/
def incStep (n : ℕ) : ℕ := P.ticksUp n
/-- The physical (nonnegative) time `t'_i`. -/
def incT (s n : ℕ) : ℝ≥0 := whenly Δ s (P.incStep n)
/-- The priced furthest time gauge-coordinate (including one ℓ for shield). -/
def extentG (n : ℕ) : ℤ := 2 * ((ℓ : ℤ) + 2*n) + 1 + b * P.incStep n + ℓ
/-- Time and space steps of the boxes `I_A`. Symmetric costs. -/
def costU (n : ℕ) (j : Axis) : ℕ :=
  if j = 3 then 1 + P.ticksUp (P.extentG n) else ℓ + 1
/-- Common real widths `w`. -/
def costW (s n : ℕ) (j : Axis) : ℝ := bell Δ s (P.costU n j)

lemma ticksUp_pays (d : ℤ) : d ≤ b * P.ticksUp d := by
  have : (0 : ℝ) < b := by exact_mod_cast ruler_gene P.par.block
  have hw : (d:ℝ) ≤ (b:ℝ)*P.ticksUp d := (div_le_iff₀' this).mp (Nat.le_ceil ((d : ℝ) / b))
  exact_mod_cast hw

lemma ticksUp_le (d : ℤ) (hd : 0 ≤ d) : b * P.ticksUp d ≤ d + b := by
  have he : (0 : ℝ) < b := by exact_mod_cast ruler_gene P.par.block
  let q := P.ticksUp d
  have : (q:ℝ) ≤ (d:ℝ)/b+1 := (Nat.ceil_lt_add_one (div_nonneg (show (0:ℝ)≤(d:ℝ) by exact_mod_cast hd) he.le)).le
  have hw : (b:ℝ)*q ≤ (d:ℝ)+b := by
    rw [← le_div_iff₀' he, add_div, div_self he.ne']
    exact this
  exact_mod_cast hw

lemma incStep_pos (n : ℕ) (hn : 0 < n) : 0 < P.incStep n :=
  Nat.ceil_pos.mpr <| div_pos (by exact_mod_cast hn) (by exact_mod_cast ruler_gene P.par.block)

lemma incT_pos (s n : ℕ) (hn : 0 < n) : 0 < P.incT s n := when_pos _ _ _ <| P.incStep_pos _ hn

lemma extentG_pos (n : ℕ) : 0 < P.extentG n := by
  have := ruler_gene P.par.block
  unfold extentG; positivity

lemma costU_pos (n : ℕ) (j : Axis) : 0 < P.costU n j := by unfold costU; split <;> omega

lemma extentG_paid (n : ℕ) : P.extentG n ≤ b * P.costU n 3 := by
  simp only [costU, ↓reduceIte]
  rw [Nat.cast_add, mul_add]
  exact le_add_of_nonneg_of_le (by have := ruler_gene P.par.block; positivity) (P.ticksUp_pays _)

lemma costW_pos (s n : ℕ) (j : Axis) : 0 < P.costW s n j := by
  unfold costW
  rw [natural_time]
  exact_mod_cast when_pos _ s _ (P.costU_pos n j)

lemma tick_ratio (s n : ℕ) (m : ℤ) :
    bell Δ s m / P.dew s n = ((↑(b*m) : ℝ)/n) / 2 := by
  have he := Apron.distance_mark P s m
  change 2 * bell Δ s m = (↑(b*m) : ℝ)/precisionAt P.par s at he
  have : bell Δ s m = ((↑(b*m) : ℝ)/precisionAt P.par s) / 2 := by rw [← he]; ring
  have hp : precisionAt P.par s ≠ 0 := (positiveScale ..).ne'
  rw [this, dew]
  field_simp

variable (c r : ℕ → ℕ) (A : Launch P c r)
include A
lemma scaled_step : Tendsto (fun i => ((r i : ℕ):ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop
private lemma tendsto_paid (f : ℕ → ℤ) (u : ℝ) (hf : ∀ i, 0 ≤ f i)
    (h : Tendsto (fun i => (↑(f i):ℝ) / ↑(r i)) atTop (𝓝 u)) :
    Tendsto (fun i => (↑(b * P.ticksUp (f i)) : ℝ) / ↑(r i)) atTop (𝓝 u) := by
  have hg := h.add (tendsto_const_nhds.div_atTop (P.scaled_step c r A) (a := (b:ℝ)))
  rw [add_zero] at hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h hg ?_ ?_
  · intro i; dsimp only; apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _); exact_mod_cast P.ticksUp_pays (f i)
  intro i
  dsimp only
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast P.ticksUp_le (f i) (hf i)) (Nat.cast_nonneg _)

private lemma t_I : Tendsto (fun i => (↑(b * P.incStep (r i)) : ℝ) / ↑(r i)) atTop (𝓝 1) := by
  refine P.tendsto_paid c r A _ _ (fun _ => Int.natCast_nonneg _) ?_
  convert tendsto_const_nhds using 1
  funext i
  rw [Int.cast_natCast, div_self (show ((r i:ℕ):ℝ) ≠ 0 by exact_mod_cast (A.unitSize i).ne')]

lemma incT_ratio :
    Tendsto (fun i => (P.incT (c i) (r i):ℝ) / P.dew (c i) (r i)) atTop (𝓝 (1/2)) := by
  refine ((P.t_I c r A).div_const 2).congr (fun i => ?_)
  symm
  unfold incT
  rw [← P.tick_ratio]
  exact congrArg (· / _) (natural_time _ _ _).symm

private lemma extG_ratio : Tendsto (fun i => (↑(P.extentG (r i)):ℝ) / ↑(r i)) atTop (𝓝 5) := by
  -- numerator = 3ℓ + 1 + 4 n + b a'_i
  let z : ℝ := 3*ℓ+1
  have h := tendsto_const_nhds.div_atTop (P.scaled_step c r A) (a := z)
  have ht := (P.t_I c r A).add (h.add_const 4)
  rw [show (1 : ℝ) + (0+4) = 5 by norm_num] at ht
  refine ht.congr fun i => ?_
  have he : ((r i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (A.unitSize i).ne'
  dsimp only [z,extentG]
  field_simp; push_cast; ring

lemma costW_ratio_time :
    Tendsto (fun i => P.costW (c i) (r i) 3 / P.dew (c i) (r i)) atTop (𝓝 (5/2)) := by
  have hp := P.tendsto_paid c r A (fun i => P.extentG (r i)) _
      (fun i => (P.extentG_pos (r i)).le) (P.extG_ratio c r A)
  have ht := (tendsto_const_nhds.div_atTop (P.scaled_step c r A) (a := (b:ℝ))).add hp
  rw [zero_add] at ht
  simp_rw [costW, P.tick_ratio]
  refine (ht.div_const 2).congr fun i => ?_
  simp only [costU, ↓reduceIte, ← add_div]
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Int.cast_add]

lemma costW_ratio_space (j : Axis) (hj : j ≠ 3) :
    Tendsto (fun i => P.costW (c i) (r i) j / P.dew (c i) (r i)) atTop (𝓝 0) := by
  simp_rw [costW, P.tick_ratio, costU, if_neg hj]
  simpa only [zero_div] using
    (tendsto_const_nhds.div_atTop (P.scaled_step c r A) (a := (↑(b * ↑(ℓ+1:ℕ)):ℝ))).div_const 2

lemma costW_go (j : Axis) : Tendsto (fun i => P.costW (c i) (r i) j) atTop (𝓝 0) := by
  have ⟨z,h⟩ : ∃ z, Tendsto (fun i => P.costW (c i) (r i) j / P.dew (c i) (r i)) atTop (𝓝 z) := by
    by_cases hj : j = 3; · subst j; exact ⟨_,P.costW_ratio_time c r A⟩
    exact ⟨_,P.costW_ratio_space c r A j hj⟩
  have hz := h.mul (proper_dew P c r A)
  rw [mul_zero] at hz
  exact hz.congr fun i => div_mul_cancel₀ _ (P.dew_pos _ (A.unitSize i)).ne'

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
