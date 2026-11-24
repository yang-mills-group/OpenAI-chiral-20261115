import YM.CF.DPress.Fees.Stride
/- Dark and Moral currency. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees.Rosy
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead Rails Wray Finance Receipt
open Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n: Side}(P:BudgetPoint){a L h θ:ℝ}
abbrev testH(o:Seat n)(x:Force n):ℝ:= if o∈(soul x).2 then mass P (soul x).2 else 0
abbrev Beta (h:ℝ) := CurrencyP (streak (n:=n) P h) (testH P)
abbrev κD (h:ℝ) := Transactions (fun i:Force n=>fun F:Copy n=>ForceB P i F h) (testH P)
lemma testD (o:Seat n)(i:Force n)(_:i∈univ):0≤testH P o i:=ite_nonneg (ccur ..) le_rfl
variable (t:1≤h)
include t
lemma totalD {f:ForceBudget n} : κD P h f a ↔ Dark Plain f P h a:=by
 have he (v:Force n→ℝ)(o:Seat n) : (∑ i,testH P o i*v i)=(∑ i:Force n, if o∈i.val.1.val.2 then P.mass i.val.1.val.2 (v i) else 0):=by apply sum_congr rfl; intro i p; unfold testH soul; split; rfl; simp
 refine ⟨fun ⟨k,v,q,H⟩=>⟨⟨v,fun i=>q i (mem_univ _),fun i=> he v i ▸ H i⟩,fun _ f=>f.elim⟩,?_⟩; intro p; obtain ⟨q,v,k⟩:=p.weight; exact ⟨le_trans (sum_nonneg (s:=(univ:Finset (Force n))) (fun i h=>mul_nonneg (testD P 0 i h) ((capD P _ i t).priceQ _ (v _)))) ((he q 0).symm ▸ k _),q,fun i _=>v i,fun i=>(he q i).symm ▸ k i⟩
lemma billF : Finance (fun f:ForceBudget n=>fun a=> Dark Plain f P h a) (Beta P h):= Finance.anti _ _ _ (Income _ _ _ (testD P) (capD P h · t)) (fun i a=> totalD P t)
lemma kX {f:ForceBudget n}(u: Dark Plain f P h a)(i:Force n): ForceB P i (f i) h a:= spending (fun i:Force n=>fun F:Copy n=>ForceB P i F h) _ _ (testD P) (capD P h · t) (totalD P t|>.2 u) i ⟨(soul i).1,by rw [testH,if_pos i.val.1.property]; exact massp P _⟩
lemma erupt (f:ℂ→ForceBudget n)(g:∀ z∈ank L, Dark Plain (f z) P h a)(v:∀ i:Force n, Listen L (fun z=>f z i) (γGood P ((soul i).2 \ i.val.2)))(u:1<L): Dark Plain (f 1-f 0) P h (a/(L-1)):= totalD P t|>.1 (results _ _ (testH P) (testD P) (capD P h · t) f (fun i p=>(totalD P t).2 (g i p)) (fun i=> chiB P h i t _ (v i) (fun z p=> kX P t (g z p) i) u) u)
end YM.CF.DPress.Fees.Rosy
