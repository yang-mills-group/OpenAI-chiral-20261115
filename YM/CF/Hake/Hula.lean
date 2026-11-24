import YM.CF.Hake.Song
import YM.CF.Stilo.Bubble
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{ι n A:Type*}[LinearOrder n][Fintype n][SemilatticeSup A][OrderBot A][Fintype A][DecidableEq A]{k:ℕ}{x:E}
-- Stilo.coal budget
abbrev Lay(F G: Track A (Raid n)):= Stilo.coal F G skirt
abbrev Loan(n:Type*)[LinearOrder n](A:Type*)[SemilatticeSup A][OrderBot A][DecidableEq A]: Track A (Raid n):= Pi.single ⊥ (Pi.single ∅ 1)
def Course(k:ℕ)(F:Track A (E→FC n))(x:E)(c:Track A (Raid n)):=∀ i, Woody k (F i) x (c i)
variable {F G:Track A (E→FC n)}{c d:Track A (Raid n)}
lemma Course.posH(h:Course k F x c): 0≤ c:= fun i=>(h i).p
lemma Course.coinT(a:E): Course k (A:=A) (n:=n) (ownH _ A) a (Loan n A):= by intro i; unfold ownH Loan; simp_rw [Pi.single_apply]; split_ifs; exact Woody.uniV a; exact Woody.empty _
lemma Course.blank(a:E): Course k (n:=n) (A:=A) 0 a 0:= fun _=>Woody.empty _
lemma Course.fit(h:Course k F x c)(g:Course k G x d): Course k (F+G) x (c+d):= fun i=> (h _).addP (g i)
lemma Course.link(h:Course k F x c)(g:Course k G x d): Course k (crank F G) x (Lay c d):=by
 intro i; unfold crank Lay Stilo.coal; simp only [Finset.sum_apply]; apply Woody.sumV; intro j _; apply Woody.sumV; intro l _; simp_rw [Pi.single_apply]; split_ifs; exact (h j).pairP (g l); exact Woody.empty _
lemma Course.ride(h:Course k F x c)(v:ℂ)(p:‖v‖=1): Course k (v • F) x c:= fun i =>(h i).ride v p
lemma Course.germ(h:Course k F x c)(p:∀ i,F i =ᶠ[𝓝 x] G i): Course k G x c:= fun i=> (h i).germ (p i)
lemma Course.ListS(X:List ι)(F:ι→ Track A (E→FC n))(c:ι→ Track A (Raid n))(h:∀ i∈ X,Course k (F i) x (c i)) : Course k (X.map F).sum x (X.map c).sum:=by induction X with | nil=> exact blank _ | cons i l ih=> rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons]; exact fit (h _ (List.mem_cons_self ..)) (ih fun i p=> h i (List.mem_cons_of_mem _ p))
lemma skirtPos (F G:Raid n)(p:0≤F)(h:0≤G) : 0≤skirt F G:=by
 unfold skirt; apply sum_nonneg; intro i _; apply sum_nonneg; intro j _ l; unfold skirtB; split_ifs; rw [Pi.single_apply]; split_ifs; exact mul_nonneg (p i) (h j); rfl; exact le_rfl
variable {B:Raid n}
structure Turner (B:Raid n):Prop where
 fee:0≤B
 red:B ∅≤1
 loan i j:Disjoint i j→ B (i∪j)≤ B i* B j
abbrev joinV(b v:Raid n):= ∑ i:Finset n,b i*v i
lemma joinVone (h:Turner B):joinV B (Pi.single ∅ 1)=B ∅:=by unfold joinV; simp [Pi.single_apply,mul_ite]
lemma joinVadd(b v:Raid n):joinV B (b+v)=joinV B b+joinV B v:=by simp [joinV,mul_add,sum_add_distrib]
lemma joinVsum(F:ι→Raid n)(X: Finset ι):joinV B (∑ i∈X,F i)=∑ i∈X, joinV B (F i):=by unfold joinV; simp only [Finset.sum_apply,mul_sum]; rw [sum_comm]; -- tune ambiguity
lemma joinVlist(X:List ι)(F:ι→Raid n):joinV B (X.map F).sum=(X.map fun i=>joinV B (F i)).sum:=by induction X with| nil=> simp [joinV]| cons i l ih=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,joinVadd,ih]
lemma Turn_up (h:Turner B)(p:0≤c):0 ≤ fun i=>joinV B (c i):=by intro i; unfold joinV; exact sum_nonneg fun j _=> mul_nonneg (h.fee j) (p i j)
lemma turnS(h:Turner B)(F G:Raid n)(p:0≤F)(g:0≤G):joinV B (skirt F G)≤joinV B F*joinV B G:=by
 rw [skirt]; simp_rw [joinVsum]; unfold joinV; rw [sum_mul_sum]; apply sum_le_sum; intro i _; apply sum_le_sum; intro j _; unfold skirtB; split_ifs with f
 · simp only [Pi.single_apply, mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]; -- tune
   apply (mul_le_mul_of_nonneg_right (h.loan _ _ f) (mul_nonneg (p i) (g j))).trans; exact le_of_eq (by ring)
 simp only [Pi.zero_apply,mul_zero,sum_const_zero]; exact mul_nonneg (mul_nonneg (h.fee i) (p _)) (mul_nonneg (h.fee j) (g _))
abbrev rateT (B:Raid n)(c:Track A (Raid n)): Track A ℝ:=fun i=> joinV B (c i)
lemma tZero (h:Turner B):rateT (A:=A) B (Loan _ _) ≤ownH ℝ A:=by
 intro i; unfold rateT Loan ownH; simp_rw [Pi.single_apply]; split_ifs; rw [joinVone h]; exact h.red; exact le_of_eq (show joinV B 0=0 by simp [joinV])
lemma tFused(h:Turner B)(p:0 ≤ c)(q:0≤d): rateT B (Lay c d) ≤ crank (rateT B c) (rateT B d):=by
 intro i; unfold rateT Lay crank Stilo.coal; simp only [Finset.sum_apply]; simp_rw [joinVsum]; refine sum_le_sum fun j _=> sum_le_sum fun l _=>?_; simp_rw [Pi.single_apply]; split_ifs; exact turnS h _ _ (p _) (q _); exact le_of_eq (show joinV B 0=0 by simp [joinV])
lemma tFit :rateT B (c+d)=rateT B c+rateT B d:=funext fun i=> joinVadd _ _
lemma tList(X:List ι)(F:ι→ Track A (Raid n)):rateT B (X.map F).sum=(X.map fun i=>rateT B (F i)).sum:=by induction X with| nil=> exact funext fun i=> show joinV B 0=0 by simp [joinV]| cons i l ih=>rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,tFit,ih]
end YM.CF.Hake
