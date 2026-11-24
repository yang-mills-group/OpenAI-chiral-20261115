import YM.SU5.FiniteGaugeData.Marked.Skylight
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Countable approximants for all wide Borel coefficients on the box. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Common
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open TopologicalSpace Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
open VolumeCape.Atlas

variable (C:Side) (D : ℕ→ℝ) (S:Finset Cover)
abbrev Purse := {f:PairsC→ℂ // Coeff true S f}

abbrev J := Lp ℂ 1 (law C S)
local instance : Fact ((1:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
private lemma amount_int (f:Purse S) (u:Courses C S) : Integrable (amount C D S f.val u) (law C S):= Env.integrableX (amount_env C D S f.property u) _
private noncomputable def dots (f:Purse S)(u:Courses C S):J C S := Integrable.toL1 _ (amount_int C D S f u)
private lemma fee (f g:Purse S): touch C D S (f.val-g.val) ≤ Fintype.card (Courses C S) * dist (dots C D S f) (dots C D S g) := by
  calc
    touch _ _ _ _ = ∑ u:Courses C S,dist (dots C D S f u) (dots C D S g u):= by
      unfold touch; apply sum_congr rfl; intro u _; rw [dist_eq_norm,dots,dots,←Integrable.toL1_sub,L1.norm_of_fun_eq_integral_norm]; rfl
    _ ≤ _ := (sum_le_sum (fun u _=> dist_le_pi_dist _ _ u)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])

lemma sample : ∃ F:ℕ→Purse S,∀ f:Purse S,∀ r:ℝ,0<r→ ∃ i:ℕ,touch C D S (f.val-(F i).val)<r:= by
  let Q:= dots C D S
  let L:= Set.range Q; let X:=L.Elem
  have p:Purse S:= ⟨fun _=>1,⟨fun p=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩⟩
  letI:Nonempty X:=⟨Set.rangeFactorization Q p⟩
  obtain ⟨V,hV⟩:= exists_dense_seq X
  choose F hf using fun i:ℕ=> (V i).property
  refine ⟨F,fun f r h=>?_⟩
  let a:ℝ:=Fintype.card (Courses C S)
  have hp:0≤a:=by unfold a; positivity
  obtain ⟨i,u⟩:=hV.exists_dist_lt (Set.rangeFactorization Q f) (ε:=r/(a+1)) (by positivity)
  refine ⟨i,lt_of_le_of_lt (fee C D S f (F i)) ?_⟩; change a*dist (Q f) (Q (F i)) < r
  change dist (Q f) (V i).val < r/(a+1) at u
  rw [hf i]; nlinarith [(lt_div_iff₀ (by linarith only [hp]:0<a+1)).1 u, dist_nonneg (x:=Q f) (y:=(V i).val)]
end YM.CF.Buffered.Afterglow.Common
