import YM.CF.Ember.Cargo
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type}[Fintype n][DecidableEq n]
theorem polar_h(T:Op n)(e:star T=T)(j:ℕ)(hj:1≤j)(η C:ℝ)(h:0<η)(k:0<C) : ∃ F:ℝ,∃ G:ℕ,∀ N:Side,G ≤ N.val → ∀ M:Side,∀ U:Tween T j M N η C,
 ‖(∑ x,U.valley x)/(N.val:ℝ)^4-((Matrix.trace (T*T)).re/(12*Real.pi^2))*Real.log N.val‖ ≤ F :=by
 let I:= Σ (M N:Side),Tween T j M N η C×Site N; let M (i:I):=i.1; let N(i:I):=i.2.1; let U(i:I):Tween T j (M i) (N i) η C:=i.2.2.1; let V(i:I):Site (N i):=i.2.2.2
 obtain ⟨A,E,ha,he,H⟩:= pyrite e hj h k U V
 obtain ⟨d,hd⟩:= exists_nat_gt ((10*A+2)*Real.pi)
 have ht(X:Side)(p:d≤ X.val): (10*A+2)*pinch X≤1 :=by
   have hx:(d:ℝ)≤X.val:=by exact_mod_cast p
   rw [pinch,← mul_div_assoc,div_le_iff₀ (nPos _), one_mul]; exact hd.le.trans hx
 let J:= { i:I // d≤ (N i).val∧ ‖bark (V i)‖≤10*A*pinch (N i)}
 obtain ⟨C,hc,K⟩:= campU hj h k (fun i:J=>U i.val) (fun i:J=>V i.val) (by linarith : 0<10*A) (fun i=> i.property.2) (fun i=>ht _ i.property.1)
 obtain ⟨F,L⟩:= frosted (sunS T) ha hc.le he.le; refine ⟨F,d,fun X hx m u=> L _ u.evenV ?_ ?_⟩
 · have he:= pinch_pos X; nlinarith [ht X hx]
 exact ⟨fun x e=> K ⟨⟨m,X,u,x⟩,hx,e⟩,fun x e=> H ⟨m,X,u,x⟩ e⟩
end YM.CF.Ember
