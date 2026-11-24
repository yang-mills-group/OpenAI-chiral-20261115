import YM.CF.BPress.Pine.Wood
/-! VolumeB-poly Pf rule. Auxiliary exterior (OVER LETTERS, not CAR of physics) only to price the two-type ordered Wick values. Laplace formula proved here; sign factoring of decorated Wick terms will be through THIS pure exterior and sectors. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable (l:List I){x:I}
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y]{F:Branch.Field Y}
namespace EdgeD
variable (D:EdgeD I B Y F) (K:B→ℂ)(l:List I)
local notation "ωP"=>vacuum I
-- project outgoing edge out of word test (it would give unmatched partner); permits expanding just on contributing roots. Terms with repeated letters in actual unsupported configs vanish.V.Cost.
lemma unwoven (i:I)(p:i∉ l) (A:Wave I): inner ℂ (acts (raw l) ωP) (acts (D.fromT K i).val A)=0:=by
 rw [show (fromT D K i).val=_ from sumS _ _,act_sum,inner_sum]; apply sum_eq_zero; intro j h; unfold twigD; rw [act_smul, act_mul, inner_smul_right,←act_inner,←(mem_filter.mp h).2, show star (put i)=takeF i from rfl,takes_ex l i p,inner_zero_left]; simp -- tune
lemma stair_step (T:Finset I)(i:I)(p:i∉T): D.stair K (insert i T)=(1+D.fromT K i)*D.stair K T:=prod_insert p
lemma unwound (T:Finset I)(e:l.toFinset⊆T): shape (D.bkg K) l=inner ℂ (acts (raw l) ωP) (acts (D.stair K T).val ωP):=by
 let g(A:Finset I):= inner ℂ (acts (raw l) ωP) (acts (D.stair K A).val ωP); have he(A:Finset I) (t:Disjoint A T): g (A∪T)=g T:=by
    induction A using Finset.induction_on with|empty=>rw [empty_union]|@insert i A h ih=> obtain ⟨t,u⟩:=disjoint_insert_left.mp t; unfold g; rw [insert_union,stair_step D K (A∪T) i (by simp [t,h]), add_mul,one_mul,Subalgebra.coe_add,act_add,inner_add_right, Subalgebra.coe_mul,act_mul,unwoven D K l i (fun l=>t (e (List.mem_toFinset.mpr l))), add_zero]; exact ih u
 unfold shape; rw [wood]; change g univ=g T; simpa only [union_comm Tᶜ, Finset.union_compl] using he Tᶜ (disjoint_compl_left)
-- word list outgoing ownership once-per-letter; repeats safe because tile-zero
abbrev stalk(i:I):Dough I:= (1+fromT D K i)
lemma rewind : shape (D.bkg K) l = inner ℂ (acts (raw l) ωP) (acts ((l.map (D.stalk K)).prod).val ωP):=by
 by_cases h:l.Nodup; · rw [D.unwound K l l.toFinset le_rfl, show D.stair K l.toFinset=_ from (List.prod_toFinset (D.stalk K) h)]
 unfold shape; rw [tape_zero l h]; simp
abbrev Prec(i:I):=↥(D.holds i)
def green (i:I)(e:Option (D.Prec i)): Dough I:= Option.elim e 1 (fun b=> twigD D K b.val)
-- sum options per token then product exactly
lemma spring (i:I): stalk D K i=∑ l: Option (D.Prec i), green D K i l:=by
 rw [Fintype.sum_option]; have he:= sum_attach (D.holds i) (twigD D K); change 1 + _=1 + ∑ x:D.Prec i,D.twigD K x.val; exact congrArg (fun x:Dough I=>1+x) he.symm -- tune option compass
abbrev Permits (l:List I):=↥l.toFinset
abbrev Net (D:EdgeD I B Y F)(l:List I):=∀ i:Permits l, Option (D.Prec i.val)
def glow (D:EdgeD I B Y F) (K:B→ℂ) (l:List I)(e:D.Net l) : Dough I:=∏ i:Permits l, green D K _ (e i)
lemma springP (h:l.Nodup): (l.map (D.stalk K)).prod=∑ j:D.Net l, glow D K l j:=by
 have he:=List.prod_toFinset (stalk D K) h; unfold glow; rw [← he, ←prod_attach]; simp_rw [spring]; apply Fintype.prod_sum -- tune token dependency

def lit (i:I)(e:Option (D.Prec i)):Seal Y:=Option.elim e ∅ (fun b=>D.look b.val)
-- support on key variables once per letter
abbrev location (e:D.Net l) :=univ.biUnion (fun i:Permits l=> lit D _ (e i))
lemma globe (l:List I)(e:D.Net l)(f h:B→ℂ)(p: ∀ i,D.look i⊆ location D l e → f i=h i): glow D f l e=glow D h l e:=by
 unfold glow; apply prod_congr rfl; intro i u; have he: D.lit _ (e i)⊆location D l e:=subset_biUnion_of_mem (fun i:Permits l=> lit D _ (e i)) u; unfold green; cases v:e i with|none=> rfl|some x=> rw [v] at he; apply Subtype.ext; change f x.val • _= h x.val • _; rw [p x.val he]
end EdgeD
end YM.CF.BPress.Pine
