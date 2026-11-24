import Mathlib
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 210000
noncomputable section
namespace Acacia
open Filter Function Finset Set
open scoped Topology NNReal BigOperators Classical ComplexConjugate
variable{A:Type*}[NormedAddCommGroup A][NormedSpace ℝ A][CompleteSpace A]
variable (f:ℝ→A)(y:ℝ)(hf:AnalyticAt ℝ f y)
include hf
lemma rate1 :∃ C:ℝ,0 < C∧∀ᶠ h:ℝ in 𝓝 0, ‖f (y+h)-f y-h • (iteratedDeriv 1 f y)‖ ≤ |h|^2*C:=by
 let g(t:ℝ):=f (y+t); have hg:AnalyticAt ℝ g 0:=(show AnalyticAt ℝ f (y+0) by rw [add_zero]; exact hf).comp (f:=fun t:ℝ=>y+t) (analyticAt_const.add analyticAt_id)
 obtain ⟨F,h,e⟩:= hg.exists_eventuallyEq_sum_add_pow_mul 2
 refine ⟨‖F 0‖+1,add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one,?_⟩
 filter_upwards [e,h.continuousAt.norm.tendsto.eventually (ge_mem_nhds (lt_add_one ‖F 0‖))] with t eq ht
 have he:f (y+t)= (f y + t • iteratedDeriv 1 f y)+ t^2 • F t:=by
    refine eq.trans ?_
    rw [show 2= (0+1)+1 from rfl,Finset.sum_range_succ,Finset.sum_range_succ, Finset.sum_range_zero]
    simp [g,iteratedDeriv_comp_const_add]
 rw [he,show (f y+t • _)+ t^2 • F t- f y -t • (iteratedDeriv 1 f y)=t^2 • F t from (by abel),norm_smul,Real.norm_eq_abs,abs_pow]
 exact mul_le_mul_of_nonneg_left ht (sq_nonneg _)
lemma rate2 {h:ℕ→ℝ}(ht:Tendsto h atTop (𝓝 0))(p:∀i,0<h i):∃ C:ℝ,0 < C∧∀ᶠ i:ℕ in atTop,
 ‖(h i)⁻¹ • (f (y+h i)-f y)-iteratedDeriv 1 f y‖≤h i*C:=by
 obtain ⟨C,k,e⟩:=rate1 f y hf
 refine ⟨C,k,(ht.eventually e).mono fun i v=>?_⟩
 let t:=h i
 have hv:0 < t:= p _
 let d:=iteratedDeriv 1 f y
 change ‖t⁻¹ • (f (y+t)-f y)-d‖≤t*C
 rw [← inv_smul_smul₀ hv.ne' d] -- tune d: rewrites d both occurrences
 -- change rhs term subtract d; combine
 rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv)]
 calc _ ≤ t⁻¹*(|t|^2*C):= mul_le_mul_of_nonneg_left v (inv_pos.mpr hv).le
      _=t*C:=by rw [abs_of_pos hv]; field
-- repeated comp
variable(Y:Type)[NormedRing Y]
-- `pow` estimate directly with norm_one if needed or comp.General.
#check inv_smul_smul₀
#print axioms rate2
end Acacia
