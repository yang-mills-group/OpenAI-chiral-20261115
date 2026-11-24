import SatinThinShaft
import SatinThinBeacon
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
variable {n:Side}{u v h w a:ℝ}{Q:Sweep n→Prop}{p:BudgetPoint}
open QuadClock Papyrus.Franc

-- direct total of ALL output enterprises.
lemma fixedFromE {E:RegBudget n}(g:IncX Q E p h v)(b:0≤h): FixedE p h (v*(More n).val^4) E:=by
 obtain ⟨f,B,H⟩:= g.weight
 let x:= (1:Pane n); refine ⟨f,B,?_⟩; calc
     _ ≤ ∑ i:Hub n,p.mass i.val.2 (f i):= sum_le_sum fun i _=> p.loMass _ _ ((Pastry.pitch b _).trans (sky (B i) b x))
     _ = ∑ j:Seat n,∑ i:Hub n,if j=i.val.1 then p.mass i.val.2 (f i) else 0 :=by rw [sum_comm]; simp only [sum_ite_eq',sum_ite_eq,mem_univ, if_true]
     _ ≤ _ := (sum_le_sum (g:=fun _=>v) fun i _=> H i).trans_eq (by rw [sum_const,card_univ,show Fintype.card (Seat n)= _ from site_card _]; simp [mul_comm])
lemma fixedToeE {E:RegBudget n}(g:FixedE p h v E)(b:0≤h)(x:Pane n): tier h (exponentL p E x).val ≤ v:=by
 obtain ⟨f,B,H⟩:= g.pay; rw [exponentL, show ( (∑ i, _) :Cipher n).val=∑ i: Hub n, (numbE p.threshold i.val.2 (E i) x).val from pipeP (LeanV (Single n)) _ _]; calc
     _ ≤ _ := tier_sum b _ _
     _ ≤ _ := (sum_le_sum (fun i _=> sky (B i) b x)).trans H
lemma fixedFromF {E:ForceBudget n}(g:Dark Q E p h v)(b:0≤h): FixedF p h (v*(More n).val^4) E:=by
 classical
 let x:= Classical.arbitrary (Orbit n); obtain ⟨f,B,H⟩:= g.weight; have ht(i):0≤ f i:= (Pastry.pitch b _).trans (pad (B i) b x)
 let U(i:Force n):= p.mass i.val.1.val.2 (f i); let A:= v*(More n).val^4
 have hp: (∑ i,f i) ≤ A:=by
    calc
       _ ≤ ∑ i:Force n,∑ j:Seat n, if j∈i.val.1.val.2 then U i else 0:= sum_le_sum fun i _=> (p.loMass _ _ (ht i)).trans (by
         have hg : ∀ j:Seat n, 0 ≤ if j∈i.val.1.val.2 then U i else 0:=fun j=>by split; exact (ht _).trans (p.loMass _ _ (ht i)); exact le_rfl
         have he:= single_le_sum (s:= (univ:Finset (Seat n))) (fun j _=>hg j) (mem_univ i.val.1.val.1); rw [if_pos i.val.1.property] at he; exact he)
       _ ≤ _ := by rw [sum_comm]; exact (sum_le_sum (g:=fun _=>v) fun i _=> H i).trans_eq (by rw [sum_const,card_univ,show Fintype.card (Seat n)= _ from site_card _]; simp [A,mul_comm])
 exact ⟨f,B,hp⟩
lemma fixedToeF {E:ForceBudget n}(g:FixedF p h v E)(b:0≤h)(x:Orbit n): tier h (fueled p E x).val ≤ Real.exp v:=by
 classical
 obtain ⟨f,B,H⟩:= g.pay; have ht(i):0≤ f i:= (Pastry.pitch b _).trans (pad (B i) b x)
 have hh(s: Finset (Force n)): tier h ((∏ i∈s, clamp p i (E i) x).val) ≤ ∏ i∈s,f i:=by
    induction s using Finset.induction_on with
    | empty=> rw [prod_empty,prod_empty]; exact (white1 (n:=LeanV (Single n)) h).le
    | insert i s v ih=> rw [prod_insert v,prod_insert v]; exact (tier_mul b (clamp p i _ _) _).trans (mul_le_mul (pad (B i) b x) ih (Pastry.pitch b _) (ht i))
 let W(s:Finset (Force n)):= if coverF p s x.1 ∧ Set.PairwiseDisjoint (s:Set (Force n)) (fun x=> x.val.1.val.2) then ∏ j∈s, clamp p j (E j) x else 0
 change tier _ (∑ i:Finset (Force n), W i).val ≤_ -- tune ite instance
 rw [show (∑ i:Finset (Force n), W i).val=∑ i,(W i).val from pipeP (LeanV (Single n)) _ _]; apply (tier_sum b _ _).trans; apply (le_trans (b:=∑ i:Finset (Force n), ∏ j∈i,f j)); · refine sum_le_sum fun i _=>?_ ; unfold W; split; exact hh _; exact (show tier _ (0:Cipher n).val=0 from chaff _).trans_le (prod_nonneg fun i _=>ht i)
 have he: ∏ i:Force n,(f i+1)=∑ i:Finset (Force n),∏ j∈i,f j:=by rw [prod_add]; simp -- tune
 rw [←he]; refine (prod_le_prod (fun i _=>by linarith [ht i]) (g:=fun i=>Real.exp (f i)) (fun i _=>Real.add_one_le_exp _)).trans ?_; rw [← Real.exp_sum]; exact Real.exp_le_exp.mpr H
lemma fixed_uniteE {E F:RegBudget n}(t:FixedE p h w E)(u:FixedE p h v F): FixedE p h (w+v) (E+F):=by
 obtain ⟨f,x,hx⟩:= t.pay; obtain ⟨g,y,hy⟩:=u.pay; refine ⟨f+g,fun i=>Larch.prop_add p i (x i) (y i),?_⟩; simp only [Pi.add_apply,sum_add_distrib]; exact add_le_add hx hy
lemma fixed_uniteF {E F:ForceBudget n}(t:FixedF p h w E)(u:FixedF p h v F): FixedF p h (w+v) (E+F):=by
 obtain ⟨f,x,hx⟩:= t.pay; obtain ⟨g,y,hy⟩:=u.pay; refine ⟨f+g,fun i=>Roots.dom_h i _ _ (x i) (y i),?_⟩; simp only [Pi.add_apply,sum_add_distrib]; exact add_le_add hx hy
abbrev MarketR (R:GramM n)(h v:ℝ):Prop:=∃ x y z, FixedE R.p h x R.F ∧ FixedE R.p h y R.slip ∧ FixedF R.p h z R.K ∧ x+y+z ≤ v
lemma market_glow (T:Shaft (Single n))(R:GramM n)(A:Op (Single n))(X:Skye.Orbit n)(z:ℝ)(e:MarketR R h z)(u:0≤h)(t:∀ i, ‖T.glow (drawT A i)‖ ≤ h): ‖T.glow (tank A (R.board X))‖ ≤ Real.exp z:=by
 obtain ⟨x,y,s,hr,hs,hf,v⟩:=e; let Y:= Graph.actG R X; let F:=fueled R.p R.K X; have he:tier h (R.board X).val ≤ Real.exp z:=by
    change tier h ((exp Y:Dough _).val*F.val)≤ _; apply le_trans _ (Real.exp_monotone v); rw [Real.exp_add]; exact (tier_mul u _ F).trans (mul_le_mul ((dust_exp h Y u).trans (Real.exp_le_exp.mpr (show tier h Y.val≤x+y from (tier_plus u _ _).trans (add_le_add (fixedToeE hr u X.1) (fixedToeE hs u X.1))))) (fixedToeF hf u _) (Pastry.pitch u F.val) (Real.exp_pos _).le)
 exact le_trans (by simpa only [notMem_empty,if_false,mul_one,zero_mul,Real.exp_zero,mul_one] using tank_glow T A h 0 ∅ (R.board X) u le_rfl (fun i=> by simpa using t i)) he
lemma MarketR.more{R:GramM n}{x y:ℝ}(p:MarketR R h x)(w:x≤y):MarketR R h y:=by obtain ⟨a,b,c,d,e,f,g⟩:=p; exact ⟨_,_,_,d,e,f,g.trans w⟩
end YM.CF.Graph
#print axioms YM.CF.Graph.market_glow
