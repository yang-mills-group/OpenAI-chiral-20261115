import YM.CF.Aroma.Seeds
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N:Side}
abbrev Cab (n: Type*)(N:Side):= Op (Tx N n)
def hub (f:Equiv.Perm (Site N))(A:Site N→Op (coneA n)): Cab n N:= twist (spatialU N n) (jump f.symm (fun i=> A (f.symm i)))
def subHub(A:Site N→Op (coneA n)):= hub (Equiv.refl _) A
lemma hub_star (f:Equiv.Perm (Site N))(A:Site N→Op (coneA n)): star (hub f A)=hub f.symm fun i=>star (A (f.symm i)):=by unfold hub; rw [←map_star, jump_star]
lemma subhub_star (A:Site N→ Op (coneA n)):star (subHub A)=subHub (fun i=> star (A i)):= hub_star ..
lemma heart (f:Equiv.Perm (Site N))(A B:Site N→Op (coneA n)): subHub A*hub f B=hub f fun i=> A (f i)*B i:=by unfold subHub hub; rw [←map_mul,jump_mul]; simp -- tune
lemma lung (f:Equiv.Perm (Site N))(A B:Site N→Op (coneA n)): hub f A*subHub B=hub f fun i=> A i*B i:=by unfold subHub hub; rw [←map_mul,jump_mul]; simp
lemma hearts(f:Equiv.Perm (Site N))(A B:Site N→Op (coneA n)): hub f A*hub f.symm B=subHub fun i=> A (f.symm i)*B i:=by unfold subHub hub; rw [←map_mul,jump_mul]; simp
lemma hubsum(f:Equiv.Perm (Site N))(A B:Site N→Op (coneA n)) : hub f A+hub f B=hub f (A+B):=by unfold hub; rw [←map_add,←jump_add]; rfl
lemma hubgap (A B: Site N→Op (coneA n)): subHub A-subHub B=subHub (A-B):=by unfold subHub hub; rw [←map_sub,← jump_sub]; rfl
lemma hubrate(f:Equiv.Perm (Site N))(A:Site N→Op (coneA n))(c:ℂ): c • hub f A=hub f (c • A):=by unfold hub; simp only [twist_formula]; rw [← Matrix.smul_mul, ← Matrix.mul_smul,← jump_smul]; rfl -- defeq maybe Matrix.smul
lemma unitHub: subHub (fun _: Site N => (1:Op (coneA n)))=1:=by unfold subHub hub; simp only [Equiv.refl_symm]; rw [jump_id,map_one]
lemma trace_hub (U: Site N→ Op (coneA n)): (subHub U).trace=∑ i,(U i).trace:=by unfold subHub hub; rw [twist_formula, Matrix.trace_mul_cycle,show star _*(spatialU N n).val=1 from (spatialU N n).property.1,one_mul]; simp [Matrix.trace,Tx,jump_apply,Fintype.sum_prod_type,coneA]
lemma hubfaith(f:Equiv.Perm (Site N))(A B:Site N→Op (coneA n))(h:hub f A=hub f B): A=B:=by have hp:= (twist _).injective h; ext1 i; ext u v; simpa only [jump_apply,Equiv.symm_apply_apply,ite_true] using congrArg (fun s:Cab n N=> s (f i,u) (i,v)) hp
-- row assemble for law covariance
lemma probe(f:Equiv.Perm (Site N))(H:Cab n N)(A:Site N→Op (coneA n)) (h:∀ (x k:Site N)(i j:coneA n),∑ y:Site N,H (x,i) (y,j)*frequency k y= frequency (f k) x * A k i j):H=hub f A:=by
 apply eq_twist; ext ⟨x,i⟩ ⟨k,j⟩
 rw [Matrix.mul_apply,Matrix.mul_apply]; unfold Tx
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type (γ:=ℂ) (α₁:=Site N)] -- tune
 simp only [spatialU,Fourier, Matrix.kroneckerMap_apply,jump_apply,Equiv.symm_apply_eq]
 simp only [Matrix.of_apply, Matrix.one_apply,mul_ite,ite_mul,mul_zero,zero_mul,mul_one]
 -- simp
 simp only [Finset.sum_ite_eq,Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ,ite_true, Equiv.symm_apply_apply]
 simp only [← mul_div_assoc,← Finset.sum_div,h]; ring
end YM.CF.Aroma
