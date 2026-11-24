import Mathlib
set_option autoImplicit false
noncomputable section
namespace YM.SU5.SatinWard.FieldBudgets
open Finset Function Filter
open scoped Topology Classical NNReal
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
universe u
/- If every generator of a chosen span has a uniform price in ratio to common heat-estimator cost with W x factor (choice permitted separately for each generator), one point estimator sum on ALL tested heights and footprints (in any individual norms, and even in a unit ball of this span) gets a uniform op cost. Works for singular expanses, no positive definiteness or orthogonality. -/
abbrev RangeEst (S:Set V)(W: V→ℝ)(X:Type u)[NormedAddCommGroup X][NormedSpace ℝ X](F:V→ₗ[ℝ] X)(c:ℝ):Prop:=∀ x∈S,‖F x‖ ≤ c*W x
abbrev Charge (S:Set V)(W:V→ℝ)(x:V):Prop:=∃ C:ℝ,0≤C∧∀(X:Type u) [NormedAddCommGroup X][NormedSpace ℝ X](c:ℝ),0≤c→∀ F:V→ₗ[ℝ] X,RangeEst S W X F c→ ‖F x‖≤ C*c
variable (S:Set V)(W: V→ℝ)
lemma resides (x:V)(p:x∈ Submodule.span ℝ S) : Charge.{u,_} S W x:=by
 induction p using Submodule.span_induction with
 | mem x hx => refine ⟨|W x|,abs_nonneg _,fun X _ _ c hc F h=>?_⟩; exact (h x hx).trans ((mul_le_mul_of_nonneg_left (le_abs_self (W x)) hc).trans_eq (mul_comm ..))
 | zero => refine ⟨0,le_refl _,fun X _ _ c hc F h=>?_⟩; rw [map_zero, norm_zero, zero_mul]
 | add x y _ _ hx hy=> obtain ⟨u,v,h⟩:=hx; obtain ⟨k,f,e⟩:=hy; refine ⟨u+k,add_nonneg v f,fun X _ _ c t F p'=>?_⟩; rw [map_add,add_mul]; exact (norm_add_le ..).trans (add_le_add (h X _ t F p') (e X _ t F p')) -- `class implicit`
 | smul a x _ hx=> obtain ⟨u,v,h⟩:=hx; refine ⟨|a| *u,mul_nonneg (abs_nonneg _) v,fun X _ _ c t F p'=>?_⟩; rw [map_smul,norm_smul,Real.norm_eq_abs,mul_assoc]; exact mul_le_mul_of_nonneg_left (h X _ t F p') (abs_nonneg _)
lemma omnivore : ∃ C:ℝ,0≤ C ∧ ∀ (V':Type u)[NormedAddCommGroup V'][NormedSpace ℝ V'](c:ℝ),0≤c→∀ (F:V→ₗ[ℝ] V'),RangeEst S W V' F c→∀ x ∈ Submodule.span ℝ S, ‖F x‖≤ C*c*‖x‖:=by
 let I:= Submodule.span ℝ S; let n:= Module.finrank ℝ I; let f:= Module.finBasis ℝ I; let G:= f.equivFunL; let d:=‖(G.toContinuousLinearMap)‖
 choose U h p using fun i:Fin n=> resides.{u} S W (f i).val (f i).property
 refine ⟨(∑ i:Fin n,U i)*d,mul_nonneg (sum_nonneg fun i _=>h i) (show 0 ≤ d from norm_nonneg (G.toContinuousLinearMap)),fun X _ _ c hc F h' x v=>?_⟩; let t:I:=⟨x,v⟩; let A:=(G t); let V:=F.comp I.subtype; have he: F x=∑i:Fin n,A i • F (f i).val:=by change V t=∑ i:Fin n,A i • V (f i); rw [show t=(f.equivFun).symm A from (f.equivFun.symm_apply_apply t).symm, f.equivFun_symm_apply, map_sum]; simp_rw [map_smul]; rfl
 rw [he]; unfold A; apply (norm_sum_le ..).trans; refine le_trans (b:=∑ i:Fin n,d*‖x‖*(U i*c)) (sum_le_sum fun i _=>?_) ?_
 · rw [norm_smul]; exact mul_le_mul ((norm_le_pi_norm (G t) i).trans (ContinuousLinearMap.le_opNorm (G.toContinuousLinearMap) t)) (p i X c hc F h') (norm_nonneg _) (by unfold d; positivity)
 rw [←mul_sum,←sum_mul]; exact le_of_eq (by ring)
#print axioms omnivore
end YM.SU5.SatinWard.FieldBudgets
