import YM.CF.Hive.Hen
import YM.CF.Proa.Surf
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
open Acorn
section
variable {m:Type*}[LinearOrder m][Fintype m](G:n≃m)(X: Op m)(p:X*X=0)
include p
lemma relabelExp (w:Wave m):cartsL G.symm (acts (exp (dg X)) w)=acts (exp (dg (portW G.symm X))) (cartsL G.symm w):=by
 let P:=portW G.symm X
 have h: P*P=0:=by unfold P portW; simp only [submatrix_mul_equiv,p]; rfl
 rw [tallied X p,tallied _ h,cartsL,freezes G.symm.toEmbedding ∅ (shelfG G.symm),flexL]
 rw [show portW G.symm (1+X)=1+P by ext i j; simp [portW,P, Matrix.one_apply]]; rfl
omit p
abbrev portE(D:List (I n)):List (Oboe m):= D.map fun i=>(!(i.1),G i.2)
lemma weaveK (D:List (Acorn.I n))(w: Wave m): cartsL G.symm (acts (drum (portE G D)) w)=acts (D.map Acorn.pen).prod (cartsL G.symm w):=by
 induction D generalizing w with
 | nil=> simp [portE,drum,act_one]
 | cons j D ih=>
    let t:= (portE G D); rw [show (D.cons j).map _ = _ from rfl] -- tune
    rw [show drum (portE _ (j::D))=bell (!(j.1),G j.2)*drum t from rfl,List.map_cons,List.prod_cons,act_mul,act_mul,← ih w] -- t complication
    have hu(x:Wave m): cartsL G.symm (acts (bell (!(j.1),G j.2)) x)=acts (Acorn.pen j) (cartsL G.symm x):=by
       rcases j with ⟨u,j⟩; cases u
       · have h:= hoist_put G.symm.toEmbedding ∅ (G j) x; rw [show G.symm.toEmbedding (G j)=j by simp] at h; exact h
       have h:= hoist_t G.symm.toEmbedding ∅ (shelfG G.symm) (G j) x; rw [show G.symm.toEmbedding (G j)=j by simp] at h; exact h
    exact hu _
end
open Kennel Nacre
variable {m B L:Side}{n' j:ℕ}{Y Z:Type}{e K C a h t L':ℝ}
section
variable {D E A:Type}[TopologicalSpace D][Fintype E][DecidableEq E] [Fintype A][LinearOrder A]
abbrev Axx (E A D:Type):= Seal E × List (Oboe A) × (D→ℂ) × ℝ
def fits (X:Master D E)(O:A→ E)(S:Seal E)(x:Axx E A D):Prop:= S⊆x.1∧Grove X.frame x.1∧ Even x.2.1.length∧ (∀ i∈x.2.1,O i.2∈ x.1) ∧ Acorn.Pro X x.1 x.2.2.1 x.2.2.2
def hireC (a h:ℝ)(R:Seal E)(x:Axx E A D):ℝ:= Acorn.cost a R x.1*h^x.2.1.length*x.2.2.2
def vowC(x:Axx E A D)(u:D): FC A:= x.2.2.1 u • drum x.2.1
structure CookC(X:Master D E)(O:A→E)(R:Seal E)(a h:ℝ)(F:D→ FC A)(z:ℝ):Prop where
 items:∃ (I:Type)(_ :Fintype I)(W:I→Axx E A D), (∀ i,fits X O R (W i)) ∧ (∑ i,hireC a h R (W i)) ≤ z ∧ ∀ x, F x=∑ i,vowC (W i) x
lemma oakLift {u:Type}[LinearOrder u][Fintype u] {X:Master D E}{O:A→E}{R:Seal E}(G:u≃A)(L:D→ FC u)(p:Carries X (O ∘ G) R a h L C): ∃ F:D→ FC A, CookC X O R a h F C ∧ ∀ x:D, ∀ y:Wave A,cartsL G.symm (acts (F x) y)=acts (L x) (cartsL G.symm y):=by
 classical
 obtain ⟨i,o,W,H,T,z⟩:=p; let S:=Finset.univ.filter fun i=>(W i).2.2.2≠0; let Q(j:S):Axx E A D:=((W j).1,portE G (W j).2.1,(W j).2.2.1,(W j).2.2.2); let M(x):=∑ i:S,vowC (Q i) x; have hS(i:S):(W i).2.2.2≠0:= (mem_filter.mp i.property).2
 refine ⟨M,⟨S,inferInstance,Q,fun j=>?_,?_,fun x=>rfl⟩,fun x y=>?_⟩
 · let A:=(W j).2.1; let p:=H j; have hg:=p.2 (hS j); refine ⟨hg.1,p.1.travel (hS j),by simpa [Q,portE] using hg.2.1,fun i t=>?_,p.1⟩; obtain ⟨i,g,rfl⟩:=List.mem_map.mp t; exact hg.2.2 i g
 · have hb: ∑ i:S,hireC a h R (Q i)=∑ j∈S,Acorn.bill a h R (W j):=by rw [← sum_attach S (fun j=>Acorn.bill a h R (W j))]; refine sum_congr rfl fun i _=> ?_; unfold Q portE hireC Acorn.bill; dsimp only; rw [List.length_map]
   rw [hb,show ∑ j∈S,Acorn.bill a h R (W j)=∑ j,Acorn.bill a h R (W j) from ?_]; exact T; refine Finset.sum_subset (subset_univ S) fun i p t=>?_ ; have he:=not_not.mp fun l=>t (mem_filter.mpr ⟨p,l⟩); rw [Acorn.bill,he,mul_zero]
 rw [z,show ∑ i,valK (W i) x=∑ j:S, valK (W j) x from Eq.symm ?_]
 · unfold M; -- act sum
   rw [act_sum,act_sum]; unfold cartsL; rw [map_sum]; apply sum_congr rfl; intro i _; unfold vowC valK; rw [act_smul,act_smul,map_smul]; exact congrArg ((Q i).2.2.1 x • ·) (weaveK G (W i).2.1 y)
 rw [show (Finset.univ : Finset ↑S)=S.attach from rfl,sum_attach S (fun i=>valK (W i) x)]; refine sum_subset (subset_univ S) fun i p t=>?_ ; have he:=not_not.mp fun l=>t (mem_filter.mpr ⟨p,l⟩); have hv:= (H i).1.sumline x; rw [he] at hv; rw [valK,norm_le_zero_iff.mp hv,zero_smul]
end
end YM.CF.Hive
