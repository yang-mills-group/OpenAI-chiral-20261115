import YM.CF.DPress.FD.Law.Cash
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Filter Finset
open scoped Topology BigOperators ENNReal NNReal Classical
variable {I J:Type*}[Fintype I][Fintype J]
namespace Cash
variable (c:Cash I)
private lemma polarity{S:Setoid I}(x:I){y z:I}(h:S.r y z): S.r y x ↔ S.r z x:= ⟨fun t=> S.iseqv.trans (S.iseqv.symm h) t, fun t=> S.iseqv.trans h t⟩
lemma Pair.weaken {R T S P:Setoid I}(w:c.Pair R T)(h:∀ x y,R.r x y→ S.r x y)(v:∀ x y,T.r x y→P.r x y):Pair c S P:=fun i j=> c.region w _ _ (fun x y k=> propext (polarity i (h x y k))) (fun x y k=> propext (polarity j (v x y k)))
abbrev be_J[A:Nonempty I]: Cash I:=⟨fun _=> (Fintype.card I:ℝ)⁻¹,fun _=>by positivity,by simp⟩
def join {I': Type*}(V: Setoid I)(Q: Setoid I') :Setoid (I×I') where
 r x y:= V.r x.1 y.1 ∧ Q.r x.2 y.2
 iseqv:=⟨fun _=>⟨V.iseqv.refl _,Q.iseqv.refl _⟩,fun t=>⟨V.iseqv.symm t.1,Q.iseqv.symm t.2⟩,fun t v=>⟨V.iseqv.trans t.1 v.1,Q.iseqv.trans t.2 v.2⟩⟩
abbrev duo(c:Cash I)(f:Cash J):Cash (I×J):=⟨fun i=> c.μ i.1*f.μ i.2,fun i=>mul_nonneg (c.nn _) (f.nn _),by simp [Fintype.sum_prod_type, ←mul_sum,c.price,f.price]⟩
lemma shade (f:Cash J)(P:I→Prop)(Q:J→Prop):turn (duo c f) (fun i=> P i.1∧ Q i.2)=c.turn P*f.turn Q:=by
 unfold turn; rw [show @Finset.filter _ (fun i:I×J=>P i.1 ∧ Q i.2) (fun x=>Classical.propDecidable _) univ=(univ.filter P)×ˢ(univ.filter Q) by ext; simp,sum_product]; rw [sum_mul]; refine sum_congr rfl fun i h=>?_ ; rw [mul_sum] -- instance issue rewrite
lemma Pair.joinT {f:Cash J}{R T:Setoid I}{P Q:Setoid J}(v: Pair c R T)(w: Pair f P Q): Pair (duo c f) (join R P) (join T Q):=by
 intro x y; rw [tape (duo c f) (Q:=fun i=>(R.r i.1 x.1∧T.r i.1 y.1)∧(P.r i.2 x.2∧ Q.r i.2 y.2)) (by intro i; unfold join; try dsimp only; grind), shade c f (fun i=> R.r i x.1 ∧ T.r i y.1) (fun i=>P.r i x.2 ∧ Q.r i y.2), (show turn (duo c f) (fun i=> (join R P).r i x)= _ from shade c f (fun i=> R.r i x.1) (fun j=> P.r j x.2)),(show turn (duo c f) (fun i=> (join T Q).r i y)=_ from shade c f (fun i=> T.r i y.1) (fun j=> Q.r j y.2)),v _ _,w _ _]; ring -- tune `_`
section
variable [DecidableEq I] {K: I →Type*}[∀ i,Fintype (K i)](F:∀ i,Cash (K i))
def pi : Cash (∀ i,K i):=⟨fun v=> ∏ i,(F i).μ (v i),fun v=> Finset.prod_nonneg fun i _=> (F i).nn _,by rw [← Fintype.prod_sum]; simp [Cash.price]⟩
lemma earn(P:∀ i,K i→Prop): turn (pi F) (fun i=>∀ j,P j (i j))=∏ i,turn (F i) (P i):=by
 let S(i):= univ.filter (P i); unfold turn; change _= ∏ i,∑ j∈S i,(F i).μ j; rw [Finset.prod_univ_sum]; apply sum_congr ?_ (fun _ _=>rfl); -- router
 ext i; simp only [Fintype.mem_piFinset,mem_filter,Finset.mem_univ,true_and,S]
def allT (P:∀ i, Setoid (K i)):Setoid (∀ i,K i) where
 r x y:=∀ i,(P i).r (x i) (y i)
 iseqv:= ⟨fun x i=>(P i).iseqv.refl _,fun s i=>(P i).iseqv.symm (s i), fun p t i=> (P i).iseqv.trans (p i) (t i)⟩
lemma pity {P Q:∀ i,Setoid (K i)}(u:∀ i,Pair (F i) (P i) (Q i)): Pair (pi F) (allT P) (allT Q):=by
 intro x y; unfold allT; try dsimp only; rw [tape (pi F) (Q:=fun z=>∀ i, (P i).r (z i) (x i) ∧ (Q i).r (z i) (y i)) (fun i=> forall_and.symm)]; rw [earn F (fun i z=> (P i).r z (x i) ∧ (Q i).r z (y i)),earn F (fun i z=> (P i).r z (x i)),earn F (fun i z=>(Q i).r z (y i))]; simp_rw [u, Finset.prod_mul_distrib]
end
abbrev Up (c:Cash I):= {i:I // 0<c.μ i}
-- trim all null sampling events (output lookup valid everywhere).
lemma subs(P:I→Prop): ∑ i:Up c with P i.val,c.μ i.val = turn c P:=by
 unfold turn; simp_rw [sum_filter]; let f(i:I):=if P i then c.μ i else 0; change ∑ i:Up c, f i.val=∑ i,f i; let S:=univ.filter (fun i:I=> 0<c.μ i); rw [← Finset.sum_subtype S (by intro i; simp [S]) f]; apply sum_subset (Finset.subset_univ _); intro i _ h; unfold f; split; exact le_antisymm (le_of_not_gt (fun p=>h (mem_filter.mpr ⟨mem_univ _,p⟩))) (c.nn i); rfl

abbrev permit : Cash (Up c):=⟨fun i=>c.μ i.val,fun i=> (i.property).le,by simpa only [implies_true, Finset.filter_true,mint] using subs c (fun _=>True)⟩
def liftF (Q:Setoid I): Setoid (Up c) where
 r x y:= Q.r x.val y.val
 iseqv:=⟨fun x=> Q.iseqv.refl x.val,Q.iseqv.symm,Q.iseqv.trans⟩ -- maybe elaboration func
lemma Pair.liftF_P {R T:Setoid I}(p:Pair c R T):Pair c.permit (liftF c R) (liftF c T):=by
 intro i j; exact (subs c (fun y=> R.r y i.val∧ T.r y j.val)).trans ((p i.val j.val).trans (congrArg₂ (·*·) (Eq.symm (subs c (fun x=>R.r x i.val))) (Eq.symm (subs c (fun x=> T.r x j.val)))))
end Cash
end YM.CF.DPress.FD
