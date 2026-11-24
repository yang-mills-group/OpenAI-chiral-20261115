import YM.CF.Palot.Fond
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Ursell Push.AbsoluteSums.Graph Push.AbsoluteSums.Coef Push.AbsoluteSums.Gas
open Trees
variable {n:Side}{ι E: Type*}[Fintype ι][NormedCommRing E][NormOneClass E][NormedAlgebra ℝ E][CompleteSpace E]
abbrev Y (n:Side) := leaf (Site n)
def constrainF (S:Finset (Site n))(y:Y n):Prop:= Disjoint S y.val
abbrev gRule (i j:Y n):Prop:= ¬Disjoint i.val j.val
lemma hardG : Hard (gRule (n:=n)):=⟨fun i h=>by obtain ⟨x,g⟩:= i.property; exact Finset.disjoint_left.mp h g g,fun i j h p=>h p.symm ⟩
abbrev stern (i:Y n):Support n:= i.val
lemma testG: Tests (gRule (n:=n)) stern:=fun i j p=> Finset.not_disjoint_iff.mp p
lemma sepG(i:hook (Site n)): separated gRule i ↔ flow _ i:=by simp only [separated,gRule,not_not,flow]
def halt (W:Y n→ E)(O: Finset (Site n))(y:Y n):E:= if constrainF O y then W y else 0
def south(O:Finset (Site n))(W:Y n→ E): E:=∑ i:hook (Site n) with flow _ i ∧ Disjoint O (robe i),∏ j∈i,W j
lemma holdOne(O: Finset (Site n))(W:Y n→ E):south O W = ∑ i:hook (Site n),pace gRule (halt W O) i:=by
 unfold south; rw [sum_filter]; apply sum_congr rfl; intro j _; unfold pace; rw [sepG]
 by_cases h:flow _ j; swap; · rw [if_neg (fun g=> h g.1),if_neg h]
 rw [if_pos h]; by_cases v: Disjoint O (robe j)
 · rw [if_pos ⟨h,v⟩]; exact prod_congr rfl fun i p => (if_pos (show constrainF O i from Disjoint.mono_right (fun _ t=> mem_biUnion.mpr ⟨_,p,t⟩) v)).symm
 rw [if_neg (fun g=> v g.2)]; obtain ⟨x,t,V⟩:= Finset.not_disjoint_iff.mp v; obtain ⟨i,u,g⟩:= mem_biUnion.mp V; exact (prod_eq_zero u (show halt W O i=0 from if_neg (fun h'=>Finset.disjoint_left.mp h' t g))).symm

def tideU (X:Clusters (Y n)):Y n:=⟨unionOf stern X.2,by obtain ⟨x,g⟩:=(X.2 none).property; exact ⟨x,mem_biUnion.mpr ⟨_,mem_univ _,g⟩⟩⟩
def jingle(W:Y n→ E)(S:Y n): E:= ∑' X:Clusters (Y n),if S=tideU X then guava gRule W X else 0
lemma jugG(O: Finset (Site n))(W:Y n→ E)(X: Clusters (Y n)): guava gRule (halt W O) X= if Disjoint O (tideU X).val then guava gRule W X else 0:=by
 split_ifs with v
 · unfold guava; apply congrArg; exact prod_congr rfl fun i _=> if_pos (show constrainF O (X.2 i) from Disjoint.mono_right (fun x t=> mem_biUnion.mpr ⟨i,mem_univ _,t⟩) v)
 obtain ⟨x,t,g⟩:= Finset.not_disjoint_iff.mp v; obtain ⟨a,-,V⟩:=mem_biUnion.mp (show x∈ unionOf stern X.2 from g); unfold guava; rw [prod_eq_zero (mem_univ a) (show halt W O (X.2 a)= 0 from if_neg (fun l=> Finset.disjoint_left.mp l t V)),smul_zero]
variable {B:ℕ}{a γ δ q:ℝ}{f:Y n→ℝ}{W:Y n→ E}
lemma sung (O: Finset (Site n))(H:Ready stern B f a γ δ q)(p:0 ≤ a)(l:∀ i,‖W i‖≤ f i): south O W = exp (∑ i:Y n with Disjoint i.val O, jingle W i):=by
 rw [holdOne O W]
 have hy:= (shineP W hardG testG p l H).1; have he(i):‖halt W O i‖ ≤ f i:=by unfold halt; split_ifs; exact l i; exact norm_zero.trans_le (H.2.2.2.2.1 _)
 rw [←(shineP _ hardG testG p he H).2]; apply congrArg; unfold jingle; rw [← Summable.tsum_finsetSum]; swap; · intro i _; exact (hy.of_nonneg_of_le (fun x :Clusters (Y n)=> norm_nonneg (if i=tideU x then guava gRule W x else 0)) (fun x=> by split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _)).of_norm
 apply tsum_congr; intro X; rw [jugG]; split_ifs with j
 · symm; rw [sum_eq_single (tideU X),if_pos rfl]; exact fun i _ v=> if_neg v; exact fun v=> False.elim (v (mem_filter.mpr ⟨mem_univ _,j.symm⟩))
 symm; apply sum_eq_zero; exact fun i l=> if_neg fun (v:i=tideU X)=> j (v ▸ (mem_filter.mp l).2.symm)
end YM.CF.Palot
