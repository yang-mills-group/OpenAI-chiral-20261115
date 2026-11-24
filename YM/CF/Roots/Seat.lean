import YM.CF.Roots.Cost
import YM.CF.Roots.Watt
import YM.CF.Mew.Char
import YM.CF.Mew.Firth
import YM.CF.Neon.LatticeFieldEstimates
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}{u t B:ℕ}{C ε η a d:ℝ}
variable {J:Type}[LinearOrder J][Fintype J]{P:BudgetPoint}{h a b v w:ℝ}
open Spire Tulip Mew
attribute [local instance] opCStarAlgebra
open scoped YM.CF.Mew
variable (R:Scree.Hub n)(T:Force n)
lemma gradeQ (Q:Scree.Force n)(f:Copy n)(p:ForceB P Q f h v)(hv:0 ≤ h):0 ≤ v:=by obtain ⟨c,t,u,b⟩:=p.costP; apply le_trans (sum_nonneg (fun i _=> mul_nonneg (by unfold Scree.tariff; positivity) (t i))) b
lemma gradeE (Q:Scree.Hub n)(f:InkD n)(p:PressB P Q f h v)(hv:0≤h): 0≤v:= (Taxi.eraF _ _ p hv 1 (ping_f P _)).grade
lemma súe(f:InkD n)(p:PressB P R f h v)(a:ℂ):PressB P R (a • f) h (‖a‖ *v):=by
 obtain ⟨v,hv,x,b⟩:=p.worth; refine ⟨fun i j u=> congrArg (a • ·) (p.term i j u), fun i => (p.fitted i).smul a, p.measureV.const_smul _,fun U t=>?_,‖a‖ • v,fun i=> mul_nonneg (norm_nonneg _) (hv i),?_ ,?_⟩
 · change a • _= hueV (tradew _ t) (a • _); rw [map_smul]; exact congrArg _ (p.gaugeV U t) -- tune namespace
 · intro U z i; exact grade_unit a R.val.1 (x _ z i)
 simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖a‖,←mul_sum]; exact mul_le_mul_of_nonneg_left b (norm_nonneg _)
lemma dúe(f:Copy n)(p:ForceB P T f h v)(a:ℂ):ForceB P T (a • f) h (‖a‖ *v):=by
 obtain ⟨v,hv,x,b⟩:=p.costP; refine ⟨fun i j u v x y=> congrArg (a • ·) (p.values _ _ _ _ x y), fun i=> (p.fitted i).smul a,fun t=>by rw [p.flagsV t,smul_zero],p.measureV.const_smul _,fun i t=>?_,fun U V t=>?_, ‖a‖ • v,fun i=> mul_nonneg (norm_nonneg _) (hv i),?_,?_⟩
 · apply p.protect; intro v; rw [Pi.smul_apply,v,smul_zero] at t; contradiction
 · change a • _= hueV (tradew _ t) (a • _); rw [map_smul]; exact congrArg _ (p.gaugeV U V t)
 · intro U z i; exact grade_unit a T.val.1.val.1 (x _ z i)
 simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖a‖,←mul_sum]; exact mul_le_mul_of_nonneg_left b (norm_nonneg _)
lemma dom_h (F G:Copy n)(p:ForceB P T F h v)(u:ForceB P T G h w):ForceB P T (F+G) h (v+w):=by
 obtain ⟨c,h,x,y⟩:=p.costP; obtain ⟨k,v,α,g⟩:=u.costP
 refine ⟨fun V W t e g z=> congrArg₂ (·+·) (p.values _ _ _ _ g z) (u.values _ _ _ _ g z),fun i=>(p.fitted i).add (u.fitted i),fun t=> by rw [p.flagsV t,u.flagsV t,add_zero],p.measureV.add u.measureV,fun i t=> ?_, fun i z y=>(congrArg₂ (·+·) (p.gaugeV i z y) (u.gaugeV i z y)).trans (map_add ..).symm,c+k,fun j=>add_nonneg (h j) (v j),fun i z j=>Prism.tack (x i z j) (α i z j),by simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add y g⟩
 by_cases w:F i=0; · refine u.protect _ ?_; intro z; rw [Pi.add_apply,w,z,add_zero] at t; contradiction
 exact p.protect _ w
lemma dom_K_fin {ι:Type*}[DecidableEq ι](I:Finset ι)(F:ι→ Copy n)(W:ι→ℝ)(u:∀ i∈I,ForceB P T (F i) h (W i)): ForceB P T (∑ i∈I,F i) h (∑ i∈I,W i):=by induction I using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact Vale.rinsed ..|insert i I x p =>rw [sum_insert x,sum_insert x]; exact dom_h _ _ _ (u i (mem_insert_self ..)) (p (fun j v=>u _ (mem_insert_of_mem v)))
-- aggregation with geometry.Mx.Fill stamp.R.Ar support sparse. X nested. incidence weights.money abstract.
section gate
end gate
end YM.CF.Roots
