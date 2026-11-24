import YM.CF.DPress.Fees.Fare
import YM.CF.Py.Goals
/- Finite root markets Mensura.Select.. Glue shape projections. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead Rails Wray Finance Receipt
open Push.AbsoluteSums Trees -- currency
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
section layer
variable {I J U V: Type}[Fintype I][AddCommGroup U][Module ℂ U][Nonempty J]
-- general pile → Aux Prop masks membership.Seat.R.Coinu.
variable (F:I→Credit U)(A:I→Dial U)(M:J→I→ℝ) (v:∀ j,∀ i∈(@univ I _),0≤M j i) (q:∀ i,Finance (F i) (A i))
abbrev Transactions := Measures (fun i:I=> fun x:I→ U=> F i (x i)) univ M -- tune
abbrev CurrencyP := Relay (fun i:I=>hood (fun x:I→U=> x i) (A i)) univ M
variable {L a:ℝ}(f:ℂ→ I → U)
def timely :Prop:= ∀ i:I, Brings L (fun z=>f z i) (f 1 i-f 0 i) (A i) -- maybe not used
include v q
lemma Income : Finance (Transactions F M) (CurrencyP A M):= Finance.system _ _ _ _ (fun i _=>Finance.thru (u:=fun x:I→U=> x i) (q i) (fun _ _=>rfl) (fun _ _=>rfl)) v
lemma spending {x:I→U}(p:Transactions F M x a)(i:I)(t:∃ j,1≤M j i): F i (x i) a:= by obtain ⟨j,g⟩:=t; exact Finance.qualifyZ _ _ _ M (fun i (_:i∈(@univ I _))=>Finance.thru (u:=fun x:I→ U=> x i) (q i) (fun _ _=>rfl) (fun _ _=>rfl)) v p i (mem_univ _) j g -- tune Fimplicit annotation
lemma results (r:∀ z∈ ank L,Transactions F M (f z) a) (y:timely (L:=L) A f) (k:1<L): Transactions F M (f 1-f 0) (a/(L-1)):= (Income F A M v q).earn f k r (Brings.covered _ _ fun j t=> Brings.stage _ _ fun i _=>Brings.hold (u:=fun x:I→ U=>x i) (y i)) -- tune
end layer
variable {n: Side}{a L h θ:ℝ}
variable (P:BudgetPoint)
namespace Rosy
def mass (S:Support (More n)):=currency P.B P.supportExponent S
abbrev tested(o:Seat n)(x:Hub n):ℝ:= if o=x.val.1 then mass P x.val.2 else 0
variable (h)
abbrev Account := Transactions (fun k:Hub n=> fun v:InkD n=>PressB P k v h) (tested P)
abbrev Angel(n:Side) := CurrencyP (beaming (n:=n) P h) (tested P)
variable {h}
local notation "T" => (fun _:Spire.Sweep n=> False) -- tune
abbrev Plain {n: Side} : Spire.Sweep n → Prop:=fun i=>False
variable (v0:1 ≤ h)
lemma ccur (x: ℝ){s: Side}(S:Support s)(U:ℕ):0 ≤ currency U x S:= (Real.exp_pos _).le
lemma steady {x:ℝ}(h:0≤x){s:Side}(S : Support s)(U:ℕ):1 ≤ currency U x S:= Real.one_le_exp (by positivity)
lemma massp (i :Hub n): 1≤ mass P i.val.2:=steady P.exponent_pos.le .. -- tune arguments no P
lemma testedP (o:Seat n)(i:Hub n)(_:i ∈ univ):0≤tested P o i:= ite_nonneg ((Real.exp_pos _).le) le_rfl
include v0
lemma account(f:RegBudget n): Account h P f a ↔ IncX Plain f P h a:=by
 let W (v:Hub n→ℝ)(o:Seat n): (∑ i,tested P o i * v i)=(∑ i,if o=i.val.1 then P.mass i.val.2 (v i) else 0):=by apply sum_congr rfl; intro i _; unfold tested; split; rfl; simp
 refine ⟨fun ⟨v,c,q,t⟩=>⟨⟨c,fun i=>q i (mem_univ i),fun i=>(W c i) ▸ t i⟩,fun _ x=> x.elim⟩,?_⟩; intro p; obtain ⟨v,c,q⟩:=p.weight; refine ⟨le_trans (b:=∑ i,tested P 0 i*v i) ?_ ((W v 0).symm ▸ q _), v, fun i _=>c i, fun i=>(W v i).symm ▸ q i⟩; exact sum_nonneg (fun i p=> mul_nonneg (testedP P 0 i p) ((capE P _ i v0).priceQ _ (c _))) -- tune Prop x Truth
lemma billP : Finance (fun f:RegBudget n=> fun a=>IncX Plain f P h a) (Angel h P n):= Finance.anti _ _ _ (Income _ _ _ (testedP P) (capE P h · v0)) (fun i a=>account P v0 i) -- tune binder name n.
variable {f: RegBudget n}
lemma values (t: IncX Plain f P h a)(i:Hub n): PressB P i (f i) h a:= spending (fun i:Hub n=>fun v:InkD n=>PressB P i v _) _ _ (testedP P) (capE P _ · v0) ((account P v0 f).2 t) i ⟨i.val.1, by rw [tested,if_pos rfl]; exact massp P i⟩ -- tune fix shadow
lemma approach (f:ℂ → RegBudget n)(g:∀ z ∈ank L, IncX Plain (f z) P h a)(ζ:∀ i:Hub n,Listen L (fun z=> f z i) (Good P i.val.2))(k:1<L): IncX Plain (f 1-f 0) P h (a/(L-1)):= by apply (account P v0 _).1; exact results (fun i:Hub n=>fun v:InkD n=>PressB P i v h) _ _ (testedP P) (capE P h · v0) f (fun i p=>(account P v0 _).2 (g i p)) (fun i=> renter P h i v0 _ (ζ i) (fun z p=> values P v0 (g z p) i) k) k -- tune results.q
end Rosy
end YM.CF.DPress.Fees
