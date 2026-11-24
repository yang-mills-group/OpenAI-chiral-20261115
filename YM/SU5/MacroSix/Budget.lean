import YM.SU5.MacroSix.Bodies

/-! # Body widths: rescaled and physical -/

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

variable (P : Spine) (s n : ℕ)
local notation "d" => ((ruler P.par.block:ℤ):ℝ)
local notation "ℓ" => P.calibration.ℓ
local notation "M" => timeMesh P.par

lemma gaugeRuler_pos : 0 < (d) := by exact_mod_cast ruler_gene P.par.block

lemma priceAtDew (hn : 0 < n) (m : ℕ) :
    (whenly M s m:ℝ) / P.dew s n = ((m:ℝ)/(n:ℝ)) * ((d)/2) := by
  have he := Apron.distance_mark P s (m:ℤ)
  rw [show bell M s m=(whenly M s m:ℝ) from natural_time M s m, markZ] at he
  simp only [Int.cast_mul,Int.cast_natCast] at he
  have hg : (whenly M s m:ℝ) = ((d)*(m:ℝ)/precisionAt P.par s)/2 := by linarith
  rw [hg, dew]; field_simp [(positiveScale P.par s).ne', Nat.cast_ne_zero.mpr hn.ne']

private lemma ceilEstimate (f g : ℕ → ℝ) (F : ℝ) (hg : ∀ i, 0 ≤ g i) (hf : ∀ i, 0 ≤ f i)
    (h : Tendsto g atTop atTop) (p : Tendsto (fun i ↦ f i / g i) atTop (𝓝 F)) :
    Tendsto (fun i ↦ (⌈f i⌉₊:ℝ)/g i) atTop (𝓝 F) := by
  have he := p.add ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop h)
  rw [add_zero] at he
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le p he ?_ ?_
  · intro i; exact div_le_div_of_nonneg_right (Nat.le_ceil _) (hg i)
  intro i; dsimp only; rw [← add_div]
  exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (hf i)).le (hg i)

variable {P} {c r : ℕ → ℕ} (A : Launch P c r)
include A
local notation "r'" i:max => ((r i):ℝ)

private lemma count_advance :
    Tendsto (fun i ↦ (P.advanceCount (r i):ℝ)/ r' i) atTop (𝓝 (1/(d))) := by
  have hr := P.gaugeRuler_pos
  refine ceilEstimate (fun i ↦ (r' i)/(d)) _ _ (fun i ↦ by positivity)
    (fun i ↦ by positivity) (tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop)
    (tendsto_const_nhds.congr fun i ↦ ?_)
  have he : 0 < r' i := by exact_mod_cast A.unitSize i
  field_simp

/-- t'/ρ goes to 1/2. -/
lemma scale_travel : P.dimensionS c r (fun i ↦ P.travelTime (c i) (r i)) (1/2) := by
  have hr := P.gaugeRuler_pos
  have h := (count_advance A).mul_const ((d)/2)
  rw [show 1/(d) * ((d)/2) = 1/2 by field_simp] at h
  exact h.congr fun i ↦ (P.priceAtDew (c i) (r i) (A.unitSize i) _).symm

private lemma height_ratio : Tendsto (fun i ↦ (P.timeBudget (r i):ℝ)/ r' i) atTop
    (𝓝 (5/(d))) := by
  let C : ℝ := 2*(ℓ:ℝ)+1+(ℓ:ℝ)
  let u (i : ℕ) := (P.advanceCount (r i):ℝ)
  let L (i : ℕ) := ((2*((ℓ:ℝ)+2*((r i):ℝ))+1) +(d)*u i+(ℓ:ℝ))/(d)
  have hd := P.gaugeRuler_pos
  have hm : Tendsto (fun i ↦ r' i) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop
  have hr (i : ℕ) : 0 < r' i := by exact_mod_cast A.unitSize i
  have hc : Tendsto (fun i ↦ L i/r' i) atTop (𝓝 (5/(d))) := by
    have he := ((((tendsto_const_nhds (x:=C)).div_atTop hm).add_const 4).add
      ((count_advance A).const_mul (d))).div_const (d)
    rw [show (0+4+(d)*(1/(d)))/(d) = 5/(d) from (by field_simp; ring)] at he
    refine he.congr fun i ↦ ?_
    change ((C / r' i + 4) + (d) * (u i / r' i))/(d) = _
    unfold L C; have hh := hr i; field_simp <;> ring
  have he := ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop hm).add
    (ceilEstimate L (fun i ↦ r' i) _ (fun i ↦ (hr i).le)
      (fun i ↦ by dsimp only [L,u]; positivity) hm hc)
  rw [zero_add] at he
  exact he.congr fun i ↦ by
    change 1 / r' i + _ = ((1 + ⌈L i⌉₊:ℕ):ℝ) / r' i; rw [Nat.cast_add,Nat.cast_one,add_div]

/-- Body half price in zoomed coordinates tends to `5/2` in axis 3. -/
lemma timeWidthRatio : P.dimensionS c r (fun i ↦ P.sixWidth (c i) (r i) 3) (5/2) := by
  have hd := P.gaugeRuler_pos
  have he := (height_ratio A).mul_const ((d)/2)
  rw [show 5/(d)*((d)/2)=5/2 from (by field_simp)] at he
  refine he.congr fun i ↦ ?_
  unfold sixWidth sixBudget; simp only [↓reduceIte]
  exact (P.priceAtDew (c i) (r i) (A.unitSize i) (P.timeBudget (r i))).symm

lemma spaceWidthRatio (j : Axis) (h : j ≠ 3) :
    P.dimensionS c r (fun i ↦ P.sixWidth (c i) (r i) j) 0 := by
  have hm : Tendsto (fun i ↦ r' i) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop
  have he := ((tendsto_const_nhds (x:=((ℓ+1:ℕ):ℝ))).div_atTop hm).mul_const ((d)/2)
  rw [zero_mul] at he
  refine he.congr fun i ↦ ?_
  unfold sixWidth sixBudget; simp only [if_neg h]
  exact (P.priceAtDew (c i) (r i) (A.unitSize i) _).symm

private lemma toActual {u : ℕ → ℝ≥0} {x : ℝ} (h : P.dimensionS c r u x) :
    Tendsto (fun i ↦ (u i:ℝ)) atTop (𝓝 0) := by
  have he := h.mul (P.proper_dew c r A)
  rw [mul_zero] at he
  exact he.congr fun i ↦ div_mul_cancel₀ (u i:ℝ) (P.dew_pos _ (A.unitSize i)).ne'

lemma sixWidth_vanishes (j : Axis) : Tendsto (fun i ↦ (P.sixWidth (c i) (r i) j:ℝ))
    atTop (𝓝 0) := by
  by_cases h : j=3
  · subst j; exact toActual A (timeWidthRatio A)
  exact toActual A (spaceWidthRatio A j h)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.sixWidth_vanishes
