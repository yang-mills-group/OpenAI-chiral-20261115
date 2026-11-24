import YM.CF.Graph.Pod
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
variable {n:Side}{u v h w a:ℝ}{Q:Sweep n→Prop}{p:BudgetPoint}
lemma talp (g:0≤h)(i:Finset (Dwell n))(o:Seat n)(p:BudgetPoint): h^i.card ≤tariff p o h i:= le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by simp))
lemma sky {U:Hub n}{F:InkD n}(g:PressB p U F h w)(k:0≤h)(x: Pane n): tier h (numbE p.threshold U.val.2 F x).val ≤ w:=by
 obtain ⟨b,h,t,e⟩:=g.worth; apply le_trans _ e; unfold numbE; by_cases H:pingS p.threshold U.val.2 x; swap; · rw [Set.indicator_of_notMem (show x∉ _ from H),show tier _ (0:Cipher n).val=_ from chaff _]; exact sum_nonneg fun i _=>mul_nonneg (by unfold Scree.tariff; positivity) (h _)
 rw [Set.indicator_of_mem (show x∈ _ from H)]; refine sum_le_sum fun i _=>?_ ; apply mul_le_mul (talp k _ _ _) ?_ (norm_nonneg _) ((pow_nonneg k i.card).trans (talp k _ _ _)); have ht:=(t x H i).token 0 (by omega) 0 (fun u=>by exact u.elim0); simpa only [one_pow,one_mul,iteratedFDeriv_zero_apply,show increment x 0=x from by simp] using ht
lemma pad {U:Force n}{F:Copy n}(g:ForceB p U F h w)(k:0≤h)(x: Orbit n): tier h (clamp p U F x).val ≤ w:=by
 obtain ⟨b,h,t,e⟩:=g.costP; apply le_trans _ e; unfold clamp; split; next f=>
    refine sum_le_sum fun i _=> ?_ ; apply mul_le_mul (talp k _ _ _) ?_ (norm_nonneg _) ((pow_nonneg k i.card).trans (talp k _ _ _)); have ht:= (t x f i).token 0 (by omega) 0 (fun j=>by exact j.elim0); simpa only [one_pow,one_mul,iteratedFDeriv_zero_apply,Girt.openG_zero, show increment x.1 0=x.1 from by simp] using ht
 rw [show tier _ (0:Cipher n).val=_ from chaff _]; exact sum_nonneg fun i _=>mul_nonneg (by unfold Scree.tariff; positivity) (h _)
lemma pipeP {I:Type*}(n:Type*)[LinearOrder n][Fintype n](A:I→Dough n)(s:Finset I):(∑ i∈s,A i).val=∑ i∈s,(A i).val:= map_sum (Dough n).val _ _
lemma toeE {E:RegBudget n}(g:IncX Q E p h v)(b:0≤h)(x:Pane n): tier h (exponentL p E x).val ≤ v*(More n).val^4:=by
 obtain ⟨f,B,H⟩:= g.weight; rw [exponentL, show ( (∑ i, _) :Cipher n).val=∑ i: Hub n, (numbE p.threshold i.val.2 (E i) x).val from pipeP (LeanV (Single n)) _ _]; calc
     _ ≤ _ := tier_sum b _ _
     _ ≤ ∑ i: Hub n,p.mass i.val.2 (f i) :=sum_le_sum fun i _=> le_trans (sky (B i) b x) (p.loMass _ _ ((Pastry.pitch b _).trans (sky (B i) b x)))
     _ = ∑ j:Seat n,∑ i:Hub n,if j=i.val.1 then p.mass i.val.2 (f i) else 0 :=by rw [sum_comm]; simp only [sum_ite_eq',sum_ite_eq,mem_univ, if_true]
     _ ≤ _ := (sum_le_sum (g:=fun _=>v) fun i _=> H i).trans_eq (by rw [sum_const,card_univ,show Fintype.card (Seat n)= _ from site_card _]; simp [mul_comm])
-- sum even over subsets bounded by exp budget ignoring overlap & cover.
lemma toeF {E:ForceBudget n}(g:Dark Q E p h v)(b:0≤h)(x:Orbit n): tier h (fueled p E x).val ≤ Real.exp (v*(More n).val^4):=by
 classical
 obtain ⟨f,B,H⟩:= g.weight; have ht(i):0≤ f i:= (Pastry.pitch b _).trans (pad (B i) b x)
 let U(i:Force n):= p.mass i.val.1.val.2 (f i); let A:= v*(More n).val^4
 have hp: (∑ i,f i) ≤ A:=by
    calc
       _ ≤ ∑ i:Force n,∑ j:Seat n, if j∈i.val.1.val.2 then U i else 0:= sum_le_sum fun i _=> (p.loMass _ _ (ht i)).trans (by
         have hg : ∀ j:Seat n, 0 ≤ if j∈i.val.1.val.2 then U i else 0:=fun j=>by split; exact (ht _).trans (p.loMass _ _ (ht i)); exact le_rfl
         have he:= single_le_sum (s:= (univ:Finset (Seat n))) (fun j _=>hg j) (mem_univ i.val.1.val.1); rw [if_pos i.val.1.property] at he; exact he)
       _ ≤ _ := by rw [sum_comm]; exact (sum_le_sum (g:=fun _=>v) fun i _=> H i).trans_eq (by rw [sum_const,card_univ,show Fintype.card (Seat n)= _ from site_card _]; simp [A,mul_comm])
 have hh(s: Finset (Force n)): tier h ((∏ i∈s, clamp p i (E i) x).val) ≤ ∏ i∈s,f i:=by
    induction s using Finset.induction_on with
    | empty=> rw [prod_empty,prod_empty]; exact (white1 (n:=LeanV (Single n)) h).le
    | insert i s v ih=> rw [prod_insert v,prod_insert v]; exact (tier_mul b (clamp p i _ _) _).trans (mul_le_mul (pad (B i) b x) ih (Pastry.pitch b _) (ht i))
 let W(s:Finset (Force n)):= if coverF p s x.1 ∧ Set.PairwiseDisjoint (s:Set (Force n)) (fun x=> x.val.1.val.2) then ∏ j∈s, clamp p j (E j) x else 0
 change tier _ (∑ i:Finset (Force n), W i).val ≤_ -- tune ite instance
 rw [show (∑ i:Finset (Force n), W i).val=∑ i,(W i).val from pipeP (LeanV (Single n)) _ _]; apply (tier_sum b _ _).trans; apply (le_trans (b:=∑ i:Finset (Force n), ∏ j∈i,f j)); · refine sum_le_sum fun i _=>?_ ; unfold W; split; exact hh _; exact (show tier _ (0:Cipher n).val=0 from chaff _).trans_le (prod_nonneg fun i _=>ht i)
 have he: ∏ i:Force n,(f i+1)=∑ i:Finset (Force n),∏ j∈i,f j:=by rw [prod_add]; simp -- tune
 rw [←he]; refine (prod_le_prod (fun i _=>by linarith [ht i]) (g:=fun i=>Real.exp (f i)) (fun i _=>Real.add_one_le_exp _)).trans ?_; rw [← Real.exp_sum]; exact Real.exp_le_exp.mpr hp
end YM.CF.Graph
