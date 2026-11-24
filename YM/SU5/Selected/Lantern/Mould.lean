import YM.SU5.Selected.Lantern.Stencil
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern.Stencil
open Function Finset
-- $M=M(r)=10r at usage. prove general exactly. k pinned to r as Deficit. Question induction budget doesn't require r>0 except cancellation with t card bound. also s large as needed independent w.
variable (m r:ℕ)(e:0<r)(h:10*r≤m)
abbrev nχ(m k:ℕ):= (m.choose k:ℂ)
def label (i:ℕ):ℂ:= ↑(bill r i)/ nχ m (load i)
variable {d:Type*}[DecidableEq d]
private lemma pool (S P:Finset d)(h:S⊆P)(n:ℕ) (p:n≤ P.card):
 ((P.powersetCard n).filter (fun i=> S⊆i)).card/(nχ P.card n)= (nχ n S.card)/ nχ P.card S.card:=by
 let X:=P.card; let Y:=S.card; have hv:Y≤X:=card_le_card h; by_cases e:Y ≤ n
 · rw [card_filter_powersetCard_subset S P n h e]; apply (div_eq_div_iff ?_ ?_).2; swap; · exact_mod_cast (Nat.choose_pos p).ne'
   swap; · exact_mod_cast (Nat.choose_pos hv).ne'
   exact_mod_cast (show (X-Y).choose (n-Y)* X.choose Y=n.choose Y*X.choose n from by rw [mul_comm (n.choose _),Nat.choose_mul e,mul_comm]) -- tune order slots
 · rw [show (filter _ _)= (∅:Finset (Finset d)) from ?_]; swap
   · refine eq_empty_iff_forall_notMem.mpr (fun i t => ?_); obtain ⟨j,q⟩:=mem_filter.mp t; exact e ((card_le_card q).trans_eq (mem_powersetCard.mp j).2)
   simp only [card_empty,Nat.cast_zero,zero_div,nχ, Nat.choose_eq_zero_of_lt (show n<S.card from not_le.mp e)]

include h in
lemma kicks {i: ℕ}(g:i<r):load i≤m:=by unfold load; omega

def coaster (S:Finset d)(V:Finset d):ℂ:= -(∑ i∈ range r, label S.card r i* ((S.powersetCard (load i)).filter (fun k=> V⊆k)).card) -- $r first then S?
#print coaster
lemma ledgerC(S V:Finset d) (p: V ⊆ S) (v: V.card < r) (z:10*r ≤ S.card): coaster r S V= if V=∅ then -1 else 0:=by
 let x:= S.card; let y:=V.card;
 have hx(i:ℕ)(e:i∈ range r): label x r i*((S.powersetCard (load i)).filter (fun k=> V⊆k)).card = (( (load i).choose y:ℕ)* bill r i :ℝ) / nχ x y:= by -- coerces product as real-cast? Lean parser
    unfold label; have he:= pool V S p (load i) (kicks _ r z (mem_range.mp e)); push_cast; rw [div_mul_eq_mul_div, mul_div_assoc]; change _; rw [he]; unfold nχ; ring_nf; rfl
 unfold coaster; change -(∑ i∈ range r,label x r i*_)=_; rw [sum_congr rfl hx,←Finset.sum_div,←Complex.ofReal_sum,cheers r V.card v]; by_cases e:V.card=0
 · simp [show y=0 from e, card_eq_zero.mp e,nχ]
 have t: V≠∅:= mt card_eq_zero.mpr e; simp [t,e]

section alg
variable {α:Type*}[CommRing α][Algebra ℂ α]
def ballet (S:Finset d)(F:d→α):α:= 1-∑ i∈range r, label S.card r i • ∑ v∈ S.powersetCard (load i), ∏ j∈v,F j
lemma dissolve (S:Finset d)(F:d→α)(p:10*r≤ S.card) (q:0<r) : ballet r S F=∑ V∈ S.powerset with r ≤ V.card, coaster r S V • ∏ j∈ V,(F j-1):=by
 let Q(V:Finset d) := ∏ j∈ V,(F j-1); let R(v:Finset d): ℂ:=coaster r S v
 let f(i:Finset d):=∑ t∈ S.powerset with t⊆ i,Q t; have he (i:Finset d)(p:i⊆S): ∏ j∈ i,F j=f i:=by
    unfold f Q; rw [show (filter _ S.powerset)=i.powerset from ?_,←prod_add_one]; simp
    ext j; simp only [mem_filter,mem_powerset]; exact and_iff_right_of_imp (fun v=> v.trans p) -- tune
 let B(i):=S.powersetCard (load i)
 have ht(i): (∑ v∈ B i,∏ j∈v,F j)=∑ v∈ S.powerset, ((B i).filter (fun j=>v⊆ j)).card • Q v:=by
    rw [sum_congr rfl (fun v t=> he v (mem_powersetCard.mp t).1)] -- maybe B unfold
    simp_rw [f,sum_filter]; rw [Finset.sum_comm]; refine sum_congr rfl (fun u t=>?_); rw [← sum_filter, Finset.sum_const] -- constant detection
 have hv:R ∅= -1:= by unfold R; rw [ledgerC r S ∅ (empty_subset _) (by simpa) p]; simp -- q ``by simpa``?
 have hl:∑ V∈S.powerset, R V • Q V = - (1:α)+(∑ V∈ S.powerset with r ≤ V.card, R V • Q V):=by
    rw [← Finset.add_sum_erase (a:= (∅:Finset d)) _ _ (by simp),hv, neg_one_smul,show Q ∅=(1:α) from rfl]; congr 1; symm; apply Finset.sum_subset
    · intro v t; rcases mem_filter.mp t with ⟨t,w⟩; refine mem_erase.mpr ⟨?_,t⟩; rintro rfl; simp at w; omega
    intro v t w; have g:= mem_erase.mp t; have h:v.card<r:= Nat.lt_of_not_ge (fun k=>w (mem_filter.mpr ⟨g.2,k⟩)); unfold R; rw [ledgerC _ _ _ (mem_powerset.mp g.2) h p, if_neg g.1,zero_smul] -- R let
 unfold ballet; apply add_left_cancel (a:= -(1:α)); rw [show (∑ v∈ S.powerset with r≤v.card,_)=∑ v∈ S.powerset with r ≤ v.card, R v • Q v from rfl,←hl]; rw [←add_sub_assoc,neg_add_cancel,zero_sub]; -- simpler use goal calc
 change -(∑ i∈range r,label S.card r i • (∑ v∈ B i,_)) =_;
 simp_rw [ht] -- wants convert nsmul to ℂ
 simp_rw [←Nat.cast_smul_eq_nsmul ℂ, smul_sum, smul_smul]; unfold R coaster; rw [sum_comm]; rw [←sum_neg_distrib]; apply sum_congr rfl; intro i _; rw [neg_smul, sum_smul]
end alg
end YM.CF.Pannier.Chancel.Lantern.Stencil
open YM.CF.Pannier.Chancel.Lantern.Stencil
#print axioms dissolve
#print axioms ledgerC
#print axioms budget
