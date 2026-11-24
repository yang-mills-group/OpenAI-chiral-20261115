import YM.CF.BPress.Vesper.Crumbs
/-! Build vertex selections without altering FiniteGaugeData coefficient conventions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B D :Type}[Fintype B][DecidableEq B][Fintype D][DecidableEq D]
variable (F:B→ Finset I) (U:B→ Dough I)(v:∀ i,Flour (F i) (U i).val)
open DoughBag
abbrev TreesF(F:B→Finset I):= Σ i:B, Leaf (F i)
abbrev Sparklers(F:B→ Finset I):= Σ i:B, Dry (F i)
def kindle(R:B→B→Prop) : Leaves I (TreesF F) where
 band i:= letter i.2.val
 e i:= le_leaf i.2.property
 n i:= nodupB i.2.val
 rule:= mix R Sigma.fst
def heat : Leaves I (Sparklers F) where
 band i:= letter i.2.val
 e i:= le_leaf (nook i.2).property
 n i:= nodupB i.2.val
 rule:=silence _
abbrev pickLeaf (q:TreesF F):=crumb (U q.1).val q.2.val
abbrev arise(q:Sparklers F):TreesF F:=⟨q.1,nook q.2⟩
abbrev pickStone (q:Sparklers F):=pickLeaf F U (arise F q) -- ellipsis dummy syntax implicit? 
lemma pickStone_val(q:Sparklers F):pickStone F U q=crumb (U q.1).val q.2.val:=rfl
include v
lemma kind_raw(R:B→B→ Prop): box R U=(kindle F R).snow (pickLeaf F U):= by
 apply release R U Sigma.fst; intro i; rw [trib_sigma]; exact timber _ (v i)
abbrev digit (U:B→ Dough I)(i:B):= crumb (U i).val ∅
abbrev origin (U:B→ Dough I):= ∑ i,digit U i
lemma heat_raw : exp (∑ i,U i)= hollow (Complex.exp (origin U))* (heat F).snow (pickStone F U):=by
 letI : NormedAlgebra ℚ (Dough I):=NormedAlgebra.restrictScalars ℚ ℝ _; let H:= cake (heat F) (pickStone F U); rw [show (∑ i,U i)= hollow (origin U)+∑ i,H i from ?_]; swap; · rw [origin,hollow_sum,Fintype.sum_sigma,←sum_add_distrib]; apply sum_congr rfl; exact fun i _=> wind _ (v i)
 unfold snow; rw [show (heat F).rule=silence _ from rfl, wall,hollow_exp,exp_add,NormedSpace.exp_sum]; congr 1; apply prod_congr rfl; intro i _; exact pulse _ (tone (U i.fst) i.2)
omit v
def marital(A:Leaves I B)(T:Leaves I D) : Leaves I (B⊕ D) where
 band x := Sum.elim A.band T.band x
 e x:= by cases x; exact A.e _; exact T.e _
 n x:= by cases x; exact A.n _; exact T.n _
 rule:= sumR A.rule T.rule
lemma ardent (A:Leaves I B)(T:Leaves I D)(u:B→ℂ)(v:D→ℂ): A.snow u*T.snow v=(marital A T).snow (Sum.elim u v):=by
 unfold snow; rw [kit]; have he: Sum.elim (A.cake u) (T.cake v)= (marital A T).cake (Sum.elim u v):= by ext1 (i|i)<;>rfl
 rw [he]; rfl
end YM.CF.BPress.Vesper
