import YM.SU5.FiniteGaugeData.Stent.Agi
import YM.CF.Buffered.Stencil
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Stent.Wallet
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (R:Patch)
local notation "J"=> R.J
local notation "L"=> R.L
open Buffered Stencil
lemma markR (x y:Cover) (a:R.Points) : ‖mark R x a y‖=(mark R x a y).re ∧ (mark R x a y).im=0:= by
 have hv:0≤ R.weight a:= R.weight_nonneg ..; unfold mark; split_ifs
 · have he:0≤funds R:= by unfold funds; positivity
   rw [←Complex.ofReal_mul]; change ‖((↑(funds R * R.weight a)):ℂ)‖ = funds R*R.weight a ∧ (0:ℝ)=0
   rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg he hv)]; tauto
 all_goals simp
lemma billNorm (x y:Cover): ‖cash R x y‖=(cash R x y).re:= by
 apply le_antisymm _ (Complex.re_le_norm _)
 unfold cash; refine (norm_sum_le ..).trans (le_of_eq ((sum_congr rfl (fun i _=> (markR R x y i).1)).trans ?_)); exact Complex.re_sum .. |>.symm -- name
lemma billZero (x:Cover): (∑ l:Site R.L, ((R.L.val:ℂ)^2)⁻¹ * mode (aliasAt (0:Momentum) l) x * money J L l 0)= (((R.L.val:ℂ)^2)⁻¹ * (((Real.sqrt (L).val)⁻¹:ℝ):ℂ)) := by
 have hj:0<J:= lt_of_lt_of_le (by decide:0< (4:ℕ)) R.order_cut
 rw [sum_eq_single (0:Site R.L)]; · simp [money, Laurent.mode,alias_zero_eq,narrow]
 · intro l _ h; rw [money,alias_muff _ hj L _ R.odd_side h]; simp
 simp
set_option linter.flexible false
variable {d:ℕ} (v : LaurentRadius R.J R.L d)
include v
lemma bill_none (x:Site L){i:Cover}(h:i∉LabelSet d) : cash R (lift x) i=0:=by
 have he:= correspondent R x 0 0 i; rw [if_pos rfl,v i (lt_of_not_ge (mt (labels .. |>.2) h))] at he; exact he.symm
lemma bill_t (x:Site L): ∑ i∈ LabelSet d,cash R (lift x) i = (((R.L.val:ℂ)^2)⁻¹ * (((Real.sqrt (L).val)⁻¹:ℝ):ℂ)) :=by
 have hz:= richness R 0 (lift x); rw [billZero] at hz; unfold Laurent.read at hz; simp only [show ∀ v:Cover, Laurent.mode (0:Momentum) v=1 from fun v=>by simp [Laurent.mode],one_smul,tsum_eq_sum (s:=LabelSet d) (fun i h=>bill_none R v x h)] at hz; exact hz
lemma cash_weight (x:Site L): ∑ i∈ LabelSet d,‖cash R (lift x) i‖=((R.L.val:ℝ)^2)⁻¹ * (Real.sqrt (L).val)⁻¹:=by simp_rw [billNorm,←Complex.re_sum]; rw [bill_t R v]; set f:= (Real.sqrt (R.L.val:ℝ))⁻¹; rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,←Complex.ofReal_inv,←Complex.ofReal_mul]; rfl
#print axioms cash_weight
end YM.CF.Stent.Wallet
