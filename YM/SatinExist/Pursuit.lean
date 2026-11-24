import YM.SU5.FiniteGaugeData.Stent.Minna
import YM.Pressure.Macro
/-! Quantitative pricing of the level-L alias. Toward comparing independent-Ward
 raw forecast on the SAME pure matter pair at two attained registrations. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Stent
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable (R:Patch)
namespace Drop
local notation "L" => R.L
local notation "F" => funds R
abbrev drop := funds R/(R.L.val:ℝ)^4
open Stent
lemma owns {Z:Cover}(h:wrap L Z=0):Z=R.L.val • (quotVec L Z):=by unfold quotVec; rw [dif_pos h]; obtain ⟨y,v⟩:= cover_of_eq (n:=L) 0 Z (by rw [h,map_zero]); let q : ∃ y:Cover,Z=R.L.val • y:= ⟨y,(by rwa [zero_add] at v)⟩; exact Classical.choose_spec q
lemma punches (x:Cover)(y:Cover){a:R.Points}(p:mark R x a y≠0): x+a.val=R.L.val • y:=by
 unfold mark at p; split at p; swap; exact (p rfl).elim
 next h=> split at p; swap; exact (p rfl).elim
          next z=> rw [z]; exact owns R h
lemma paid (x y:Cover): ‖cash R x y‖≤drop R:=by
 unfold cash; refine (norm_sum_le ..).trans ?_
 have hf:0≤ F:=by unfold funds; positivity
 by_cases h:∃ a:R.Points,mark R x a y≠0
 · obtain ⟨a,u⟩:=h; rw [sum_eq_single a]; swap
   · intro b w p
     rw [show mark R x b y=0 from by contrapose! p; exact Subtype.ext (add_left_cancel ((punches R x y p).trans (punches R x y u).symm)), norm_zero]
   swap; · exact fun h=>(h (mem_univ _)).elim
   unfold drop; apply (le_div_iff₀ (by positivity)).2
   unfold mark; split_ifs <;> simp only [norm_mul,Complex.norm_real,norm_zero,zero_mul,Real.norm_of_nonneg hf,Real.norm_of_nonneg (R.weight_nonneg _)]
   · rw [mul_assoc]; exact mul_le_of_le_one_right hf (YM.Pressure.light R a)
   all_goals exact hf
 push Not at h; simp_rw [h,norm_zero]; simp [drop]; positivity -- tune
lemma paid_sums (s:Finset Cover): (∑ x:Site R.L,∑ y∈s, ‖cash R (lift x) y‖) ≤ F:=by
 calc
    _ ≤ ∑ x:Site L,∑ y∈s,∑ a:R.Points, ‖mark R (lift x) a y‖ := sum_le_sum fun x _=> sum_le_sum fun y _=> norm_sum_le ..
    _ ≤ _ := by
       simp_rw [sum_comm (f:=fun y a=> ‖mark R (lift _) a y‖)] -- underscore
       rw [sum_comm, show F = ∑ a:R.Points,F*R.weight a from (by rw [←mul_sum,R.weight_sum,mul_one])] -- last rewrite contains F inside? rw on goals
       refine sum_le_sum fun i _=>?_ ; let k:= wrap L (-i.val)
       have he: ∀ j:Site L, ∀ y∈s, j≠k→mark R (lift j) i y=0 := by
          intro j y _ h; unfold mark; rw [if_neg ?_]; intro p; rw [map_add, wrap_lift] at p; exact h (by rw [show k= -wrap L i.val from map_neg _ _]; exact eq_neg_of_add_eq_zero_left p)
       have hf:0≤F:=by unfold funds; positivity
       rw [sum_eq_single k]; swap
       · intro j h p; exact sum_eq_zero fun y q=> by rw [he j y q p,norm_zero]
       swap; · simp
       let w:=quotVec L (lift k+i.val)
       by_cases h:w∈s
       · rw [sum_eq_single_of_mem w h]; unfold mark; split_ifs <;> simp_all only [norm_mul,Complex.norm_real,norm_zero,Real.norm_of_nonneg hf,Real.norm_of_nonneg (R.weight_nonneg i),le_refl] <;> try exact mul_nonneg hf (R.weight_nonneg i)
         · intro j z p; unfold mark; rw [if_neg p,ite_self,norm_zero]
       rw [sum_eq_zero]; exact mul_nonneg hf (R.weight_nonneg i); intro a g; unfold mark; rw [if_neg (fun (e : a=w)=> h (show w∈s from e ▸ g)),ite_self,norm_zero]
lemma credit : F* drop R ≤ 1 := by
 have hl:0<(R.L.val:ℝ):=by positivity
 have hs:1≤(R.L.val:ℝ):=by exact_mod_cast R.L.property
 have h:= Real.sq_sqrt hl.le; have ht:= Real.sqrt_pos.mpr hl
 have hv:F= (R.L.val:ℝ)^2/(Real.sqrt (R.L.val:ℝ)):= by
    unfold funds; simp [div_eq_mul_inv]; -- tune card
    field_simp
 rw [drop,hv]; field_simp; nlinarith
#print axioms paid_sums
end Drop
end YM.CF.Stent
