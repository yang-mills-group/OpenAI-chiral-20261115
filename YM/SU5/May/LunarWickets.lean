import Mathlib
/- CP15. LAGRANGE price orientation (arithmetic). Elementary stable extrap over number powers. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar.Rink
open Finset Nat Function Filter Polynomial Real Complex
open scoped Topology BigOperators ENNReal Classical
variable {D j:ℕ} (p:0<j)(q:j≤D)
def fling (D:ℕ):= Ico 1 (D+1)
lemma fling_up (j':ℕ) : j'∈ fling D↔ 0<j'∧j'≤D:=by unfold fling; simp; omega
private def s2:= ((j:ℝ)^2)
private def fisc (j k:ℕ):ℝ:= (k:ℝ)^2 / |(k:ℝ)^2 - (j:ℝ)^2|
private def four (j k:ℕ):ℝ:= (k:ℝ)^4 / |(k:ℝ)^4 - (j:ℝ)^4|
local notation "w" k:max => fisc j k
local notation "γ"=> (fling D).erase j
local notation "fa" k:max => (Nat.factorial k:ℝ)
private lemma nonz (D:ℕ): (0:ℝ) < (D.factorial:ℝ):= Nat.cast_pos.mpr (factorial_pos _)
-- calculate total ∏γ squared ratios
include p q
private lemma flick {α:Type}[CommMonoid α](f:ℕ→α): (∏ i∈ (fling D).erase j,f i)=(∏ i∈ Ico 1 j,f i)*(∏ i∈ Ico (j+1) (D+1),f i):=by
 rw [show (fling D).erase j= Ico 1 j ∪ Ico (j+1) (D+1) from (by ext i; simp only [fling,mem_erase,mem_union,mem_Ico]; omega),prod_union]; apply Finset.disjoint_left.mpr; intro i e a; simp only [mem_Ico] at e a; omega
private lemma found (A:ℕ→ℝ) (B:ℝ)(v:(∏ i∈ fling D, A i)=B)(x:A j ≠0) : (∏ i∈(fling D).erase j,A i)= B/A j:=by rw [←v,←mul_prod_erase _ _ ((fling_up _).2 ⟨p,q⟩)]; field_simp
omit p q in
private lemma full (D:ℕ):(∏ i∈ fling D,(i:ℝ))= fa D:=by unfold fling; rw [← Nat.cast_prod]; exact congrArg Nat.cast (prod_Ico_id_eq_factorial D)
private lemma logN : (∏ i∈γ,(i:ℝ))= fa D/j:=found p q _ _ (full _) (by positivity)
private lemma sumH : (∏ i∈γ,((j:ℝ)+i))= fa (D+j)/fa j /(2*j):=by
 rw [found p q _ (fa (D+j)/fa j) _ (by positivity), two_mul]; -- show equality factor
 have he: fa j * (∏ i∈ fling D, ((j:ℝ)+i))=fa (D+j):=by
    rw [← full, ←full]; unfold fling; simp_rw [← Nat.cast_add]; rw [Finset.prod_Ico_add (fun i:ℕ=>(i:ℝ)),show D+1+j=D+j+1 from (by omega),show 1+j=j+1 from (by omega),prod_Ico_consecutive _ (by omega) (by omega)]
 rw [←he]; have hF:(fa j)≠0:=(nonz j).ne'; field_simp
private lemma billH:(∏ i∈γ,|(i:ℝ)-j|)= fa (j-1)*fa (D-j):=by
 rw [flick p q]; congr 1
 · rw [prod_congr rfl (show ∀ i∈Ico 1 j,|(i:ℝ)-j|=((↑(j-i:ℕ)):ℝ) from (fun i h=> by have hx: (i:ℕ) ≤ j:= (mem_Ico.mp h).2.le; rw [Nat.cast_sub hx,abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hx)), neg_sub])), Finset.prod_Ico_reflect _ _ (by omega),← full (j-1)]; unfold fling; rw [show j+1-j=1 from (by omega), show j+1-1=j from (by omega), show j-1+1=j from (by omega)]
 rw [prod_Ico_eq_prod_range, show D+1-(j+1)=D-j from (by omega)]; refine (prod_congr rfl (g:=fun i:ℕ=>(↑(i+1):ℝ)) (fun i h=>?_)).trans ?_
 · push_cast; rw [show _+_-(j:ℝ)=(i:ℝ)+1 from (by ring),abs_of_nonneg (by positivity)]
 rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]; -- tune parser i h subset
private lemma invoice : (∏ i∈γ, w i)=2*((fa D)^2 /(fa (D-j)*fa (D+j))):=by
 have h(i): w i = (i:ℝ)^2 /( |(i:ℝ)-j| *((j:ℝ)+i)) := by unfold fisc; rw [show (i:ℝ)^2-(j:ℝ)^2=((i:ℝ)-j)*(j+i) from (by ring),abs_mul,abs_of_nonneg (by positivity : 0 ≤ (↑j:ℝ)+i)]; -- tune i:ℝ casts coer in j+i! danger
 simp_rw [h,prod_div_distrib, Finset.prod_pow, prod_mul_distrib,billH p q,logN p q,sumH p q]
 have hl: fa j=(j:ℝ)*fa (j-1):=by nth_rw 1 2 [show j=j-1+1 from (by omega)]; rw [factorial_succ]; push_cast; rfl
 rw [hl]; have hx:(j:ℝ)≠0:= (by positivity); have hz(n:ℕ):(fa n)≠0:=(nonz n).ne'; field_simp
omit p
private lemma costs : (fa D)^2 ≤ fa (D-j) * fa (D+j) :=by
 induction j with
 | zero => rw [Nat.sub_zero,Nat.add_zero,sq]
 | succ j ih=>
   let a:= D-j; let b:= D+j; let c:=D-(j+1); have he:(D-j)= c+1:=by unfold c; omega
   have hp: (fa D)^2 ≤ fa (c+1)*fa b:=he ▸ ih (by omega)
   refine hp.trans ?_; rw [show D+(j+1)=b+1 from (by unfold b; omega), show D-(j+1)=c from rfl]; simp_rw [factorial_succ, Nat.cast_mul]; have hx: (↑(c+1):ℝ)≤ ↑(b+1):= by apply Nat.cast_le.mpr; unfold c b; omega
   exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (nonz _).le) (nonz _).le).trans_eq (by ring)
include p
private lemma spending : (∏ i∈γ,w i) ≤ 2:=by rw [invoice p q]; apply mul_le_of_le_one_right zero_le_two; exact (div_le_one (mul_pos (nonz _) (nonz _))).mpr (costs q)
#print axioms spending
private def staple(j i:ℕ):ℝ:= (i:ℝ)^2/((i:ℝ)^2+(j:ℝ)^2)
private lemma awareness(i:ℕ) : four j i= fisc j i*staple j i:=by
 have hp:0<(i:ℝ)^2+(j:ℝ)^2:=by positivity
 have h(i j:ℝ): i^4-j^4=(i^2-j^2)*(i^2+j^2):=by ring
 unfold four fisc staple; rw [h, abs_mul, abs_of_nonneg hp.le]; by_cases v : (i:ℝ)^2-(j:ℝ)^2=0; · rw [v]; simp
 field_simp
private lemma halves(i:ℕ)(z:i≤j): staple j i ≤1/2:=by unfold staple; rw [div_le_div_iff₀ (by positivity) zero_lt_two]; have he:(i:ℝ)^2 ≤ (j:ℝ)^2:= (by gcongr) -- gcongr inspect
                                                      linarith
private lemma lowJ : Ico 1 j ⊆ (fling D).erase j:=by intro i u; simp only [fling,mem_Ico,mem_erase] at u ⊢; omega
private lemma gradeD {T: Finset ℕ}(f:ℕ→ℝ)(t:∀ i∈T,0 ≤ f i ∧ f i ≤ 1) : 0≤∏ i∈T,f i ∧ (∏ i∈ T,f i)≤1:=⟨prod_nonneg fun i v=>(t i v).1, prod_le_one (fun i v=>(t i v).1) (fun i v=>(t i v).2)⟩ -- syntax parentheses
private lemma forward_weight : (∏ i∈γ, staple j i) ≤ (1/2:ℝ)^(j-1):=by
 rw [flick p q]; refine le_trans (mul_le_of_le_one_right (Finset.prod_nonneg (s:=Ico 1 j) (fun i _=>show 0 ≤ staple j i from (by unfold staple; positivity))) ((gradeD p q _ (fun i (_:i∈Ico (j+1) (D+1))=>?_)).2)) ?_
 · unfold staple; exact ⟨by positivity, (div_le_one (by positivity)).mpr (le_add_of_nonneg_right (sq_nonneg _))⟩
 refine (prod_le_prod (fun i _=> show 0≤ staple j i from (by unfold staple; positivity)) (fun i v=> halves p q i (mem_Ico.mp v).2.le)).trans_eq ?_; simp
lemma coating : (∏ i∈ γ, four j i) ≤ 2*(1/2:ℝ)^(j-1):=by
 simp_rw [awareness p q,prod_mul_distrib]; exact mul_le_mul (spending p q) (forward_weight p q) (prod_nonneg (fun i _=> (by unfold staple; positivity))) zero_le_two
-- polynomial accounting. z.real†. shift offsets
variable {Q:ℝ}(h:0<Q)
noncomputable def ferryD (Q:ℝ)(j:ℕ):ℝ:= -1+2*Q*(j:ℝ)^4
def sale (j:ℕ):ℂ:= ferryD Q j
omit p q
include h
lemma ferry_up : StrictMono (ferryD Q):=by intro x y p; unfold ferryD; gcongr -- maybe exact_mod_cast
lemma sale_in : Injective (fun i=> (sale (Q:=Q) i)):=by exact fun i j v=> (ferry_up h).injective (ofReal_injective v)
noncomputable def lagD(Q:ℝ)(D j:ℕ):= eval (-1) (Lagrange.basis (fling D) (fun i:ℕ=> (ferryD Q i:ℂ)) j)
private lemma divisor {i:ℕ}(v:i∈ (fling D).erase j) : ‖eval (-1:ℂ) (Lagrange.basisDivisor (ferryD Q j:ℂ) (ferryD Q i:ℂ))‖= four j i :=by
 have he: (ferryD Q j:ℝ) ≠ ferryD Q i:=fun k=> (mem_erase.mp v).1 ((ferry_up h).injective k.symm); let W(n:ℕ):ℂ:=ferryD Q n; rw [Lagrange.basisDivisor,eval_mul,eval_sub,eval_C,eval_X,eval_C,← ofReal_sub,← ofReal_inv,show (-1:ℂ)- ↑(ferryD Q i)= ↑((-1:ℝ)-ferryD Q i) from (by push_cast; rfl), ← ofReal_mul,norm_real,Real.norm_eq_abs]; unfold ferryD four; unfold ferryD at he;
 have hc:(i:ℝ)^4-(j:ℝ)^4≠0:=by intro k; apply he; rw [sub_eq_zero] at k; rw [k]
 have hZ: ‖(i:ℝ)^4‖=(i:ℝ)^4:=by rw [Real.norm_of_nonneg (by positivity)]
 rw [add_sub_add_left_eq_sub]; rw [show -1 - (-1+2*Q*(i:ℝ)^4)=-(2*Q*(i:ℝ)^4) from (by ring), show 2*Q*(j:ℝ)^4-_= -(2*Q*((i:ℝ)^4-(j:ℝ)^4)) from (by ring), inv_neg, neg_mul_neg]
 rw [inv_mul_eq_div, mul_div_mul_left _ _ (by positivity), abs_div, abs_of_nonneg (by positivity : 0 ≤ (i:ℝ)^4)] -- tune
include p q
lemma coat_budget :‖lagD Q D j‖≤ 2*(1/2:ℝ)^(j-1):=by unfold lagD Lagrange.basis; rw [eval_prod,norm_prod]; refine le_trans (le_of_eq ?_) (coating p q); exact prod_congr rfl fun i v=> divisor h v
omit p q
lemma windowPrice(D:ℕ) : (∑ i∈ fling D,‖lagD Q D i‖) ≤4 :=by
 refine (sum_le_sum (g:=fun i=> (2:ℝ)*(1/2)^(i-1)) (fun i v=>coat_budget ((fling_up i).1 v).1 ((fling_up i).1 v).2 h)).trans ?_; rw [←mul_sum,fling,sum_Ico_eq_sum_range,show D+1-1=D from (by omega)]; simp_rw [Nat.add_sub_cancel_left,geom_sum_eq (x:=(1/2:ℝ)) (by norm_num : (1/2:ℝ)≠1)]; have hy:0 ≤ (1/2:ℝ)^D:= (by positivity); rw [show 2* (((1/2:ℝ)^D-1)/(1/2-1))= (1-(1/2:ℝ)^D)*4 from (by ring)]; linarith
-- money receipts may normalize by sample Max.Borrow. no HB
lemma report {F:Polynomial ℂ} (u:F.degree< ↑D) : ∑ i∈fling D,lagD Q D i * eval (ferryD Q i:ℂ) F= eval (-1:ℂ) F:=by
 have hv:(fling D).card=D:=by simp [fling]
 let V:= Lagrange.eq_interpolate (s:=fling D) (sale_in h).injOn (show F.degree < ↑(fling D).card from hv.symm ▸ u)
 have F':= congrArg (Polynomial.eval (-1:ℂ)) V; rw [F',Lagrange.interpolate_apply,eval_finsetSum]; -- F' rewriting maybe occurrences eval lhs if ferry unification with -1? inspect
 exact sum_congr rfl fun i _=> by rw [eval_mul,eval_C]; exact mul_comm .. -- tune defin
#print axioms windowPrice
#print axioms report
end YM.CF.May.Lunar.Rink
