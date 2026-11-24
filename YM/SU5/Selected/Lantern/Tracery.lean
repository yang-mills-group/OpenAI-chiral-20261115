import YM.SU5.Selected.Lantern.Mould
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern.Stencil
open Function Finset BigOperators
variable (u:ℕ)
lemma fund_step {m i r:ℕ} (p:10*r≤m)(e:i<r) : ‖label m r i‖ ≤ (2:ℝ)^r:=by
 unfold label; rw [norm_div]; apply le_trans _ (budget r i e); rw [Complex.norm_real]; apply div_le_self (norm_nonneg _); unfold nχ; rw [Complex.norm_natCast]; exact_mod_cast Nat.choose_pos (kicks m r p e)
variable {k T:Type*}[DecidableEq k] [DecidableEq T] {N : Finset k}
lemma fund_V(V:Finset k)(h:N.card=10*u): ‖coaster u N V‖≤ (2:ℝ)^(12*u):=by
 unfold coaster; rw [norm_neg]; apply (norm_sum_le ..).trans;
 let P:=(2:ℝ)^u; let Q:= (2:ℝ)^N.card; have he: (u:ℝ) ≤ P:= by unfold P; exact_mod_cast (Nat.lt_two_pow_self (n:=u)).le
 apply ((sum_le_sum (g:=fun i=>(P*Q:ℝ)) ?_)).trans; rw [Finset.sum_const,Finset.card_range, nsmul_eq_mul]; refine (mul_le_mul_of_nonneg_right he (by unfold P Q; positivity)).trans_eq ?_; unfold P Q; rw [h,←mul_assoc, ←pow_add, ←pow_add]; congr 1; omega
 intro i w; rw [norm_mul,Complex.norm_natCast]; apply mul_le_mul (fund_step h.ge (mem_range.mp w)) _ (Nat.cast_nonneg _) (by positivity); apply (Nat.cast_le.mpr (card_le_card (show (filter _ _ ) ⊆N.powersetCard (load i) from filter_subset ..))).trans; rw [card_powersetCard]; unfold Q; exact_mod_cast Nat.choose_le_two_pow N.card _ -- annotate filter

section
-- budget stated R independent packet lengths. any linear matrix image for dirty costs. selector identity is on ambient NOT central. map multiplication ok. Also `β` need not normed comm. supply.
variable {α β:Type*} [CommRing α] [Algebra ℂ α][NormedRing β][Algebra ℂ β][NormOneClass β][NormSMulClass ℂ β] -- maybe NormedSpace
variable (G : α →ₐ[ℂ] β)(F:k→α)
private lemma norm_m (S:Finset k) {R:ℝ}(h:∀ i∈S, ‖G (F i)‖ ≤ R)(p:0≤R): ‖G (∏ i∈S,F i)‖≤R^S.card:=by
 induction S using Finset.induction_on with
 | empty=> rw [prod_empty,map_one,norm_one]; simp
 |insert i S e ih=>rw [prod_insert e,card_insert_of_notMem e,pow_succ',map_mul]; exact (norm_mul_le ..).trans (mul_le_mul (h _ (mem_insert_self ..)) (ih (fun i v=>h _ (mem_insert_of_mem v))) (norm_nonneg _) p)
include G F
lemma loads_dirty {r:ℕ}{R:ℝ}(t:r>0)(δ:1≤R)(p:N.card=10*r)(h:∀ i∈N, ‖G (F i)‖≤R):
 ‖G (ballet r N F)‖ ≤ ( (2:ℝ)^(13:ℕ) * R^(10:ℕ) )^r:=by
 unfold ballet; rw [map_sub,map_one,map_sum]; apply (norm_sub_le ..).trans; rw [norm_one]; let w:=10*r; let a:=(2:ℝ)^r; let b:=(2:ℝ)^(10*r); let F'(i):= N.powersetCard (load i);
 have hx:r≤(a:ℝ):= by unfold a; exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le
 have htR:0<R:=zero_lt_one.trans_le δ
 have H(i:ℕ)(e:i∈range r) : ‖G ( label N.card r i •∑ v∈ F' i,∏ j∈v,F j)‖ ≤ a*(b*R^w):=by
    rw [map_smul, norm_smul,map_sum]; apply mul_le_mul (fund_step p.ge (mem_range.mp e)) _ (norm_nonneg _) (by positivity)
    apply (norm_sum_le ..).trans; have hp(v:Finset k)(t:v∈ F' i): ‖G (∏ j∈v,F j)‖≤ R^w:=by
        have ht:= (mem_powersetCard.mp t).1; exact (norm_m G F v (fun j e=>h j (ht e)) htR.le).trans (pow_le_pow_right₀ δ ((card_le_card ht).trans_eq p))
    refine (sum_le_sum hp).trans ?_; rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold b F'; rw [card_powersetCard,p]; exact_mod_cast Nat.choose_le_two_pow (10*r) (load i)
 let D:=R^w; have he: 1 ≤ D:= one_le_pow₀ δ; have hp: 1 ≤ a:=(by unfold a; exact one_le_pow₀ one_le_two); have hr:1 ≤ b:=by unfold b; exact one_le_pow₀ one_le_two
 apply (add_le_add_right ((norm_sum_le ..).trans (sum_le_sum H)) _).trans; rw [sum_const,nsmul_eq_mul,card_range]; refine (add_le_add_right (mul_le_mul_of_nonneg_right hx (by unfold a b; positivity)) _).trans ?_
 rw [show ((2:ℝ)^(13:ℕ)*R^(10:ℕ))^r= a^3*b*D from ?_]; swap; · unfold a b D w; rw [mul_pow,←pow_mul,←pow_mul,←pow_mul,←pow_add]; congr 2; omega
 have ht: 2 ≤ a:= pow_one (2:ℝ) |>.symm.le.trans (pow_le_pow_right₀ one_le_two t); have hl : 1≤ a*(a*(b*D)):= one_le_mul_of_one_le_of_one_le hp (one_le_mul_of_one_le_of_one_le hp (one_le_mul_of_one_le_of_one_le hr he))
 change 1 + a*(a*(b*D))≤ a^3*b*D; nlinarith only [hl, ht, mul_le_mul_of_nonneg_right ht (zero_le_one.trans hl)]
end

section beads
-- if each F-1 `Blend` pos degree with disjoint index sets; then P has support. cost independent M interpolation values. parameterized normalize register. No nonempty hypotheses hidden.
variable {A B:Type*}[CommRing A][Algebra ℂ A][Ring B][Algebra ℂ B]
variable (f : A→ₐ[ℂ] B)(X:k→A)(K:Finset k)(g:k→Finset T)(H:T→B)
def spool (X:T→B)(S:Finset T) (k:ℕ) (F:B):Prop:= ∃ L:List T,L.Nodup ∧ (∀ i∈L,i∈S)∧ k ≤ L.length ∧ F=(L.map X).prod
lemma Spool.weaken {p q:ℕ}{V S:Finset T}{A:B}(v:spool H S p A)(h:q≤p)(f:S⊆ V):spool H V q A:=by obtain ⟨u,l,z,q',e⟩:=v; exact ⟨u,l,fun i e=>f (z i e),h.trans q',e⟩
lemma Spool.run {p q:ℕ}{V S:Finset T}{A A':B}(v:spool H S p A)(t:spool H V q A')(d: Disjoint S V):spool H (S∪ V) (p+q) (A*A'):=by
 obtain ⟨A,x,l,p,rfl⟩:=v; obtain ⟨B,y,c,e,rfl⟩:=t; have ht: List.Disjoint A B:= fun a h v=> disjoint_left.mp d (l a h) (c a v)
 exact ⟨A++B,List.nodup_append.mpr ⟨x,y,fun a v b g z=> (List.disjoint_left.mp ht) v (z.symm ▸ g)⟩,fun i h=> mem_union.mpr ((List.mem_append.mp h).elim (fun a=> Or.inl (l _ a)) (fun a=> Or.inr (c _ a))), by rw [List.length_append]; exact Nat.add_le_add p e, by rw [List.map_append,List.prod_append]⟩ -- tune

variable (r:ℕ)(R:ℝ) (p:K.card=10*r)(h:∀ i∈K,Blend (spool H (g i) 1) R (f (X i-1)))(d:Pairwise (Disjoint on g))
include h d p
lemma loads_clean (t:r>0)(r₀: 1≤R): Blend (spool H (K.biUnion g) r) ((2^(22:ℕ)*R^ (10:ℕ))^r) (f (ballet r K X)):=by
 have hr:0<R:=zero_lt_one.trans_le r₀; let V:=K.biUnion g; let x(C:Finset k):= ∏ i∈ C,(X i-1)
 let Q:= {C∈ K.powerset| r ≤ C.card}; let A:=(2:ℝ)^(12*r); let F:=R^(10*r)
 have hh(B:Finset k)(z:B⊆K): Blend (spool H (B.biUnion g) B.card) (R^B.card) (f (x B)):=by
    induction B using Finset.induction_on with
    | empty=> simp only [x,prod_empty,map_one,card_empty,pow_zero,biUnion_empty]; exact Blend.item _ ⟨[],by simp⟩ -- emptynm
    | insert a S p ih=>
       have he:S⊆K:=(subset_insert ..).trans z
       unfold x; rw [prod_insert p,map_mul,card_insert_of_notMem p, pow_succ', add_comm S.card, biUnion_insert]; apply Blend.merge _ _ _ (h a (z (mem_insert_self ..))) (ih he); intro i j X Z; apply Spool.run _ X Z _; exact disjoint_left.mpr (fun v t y=>by obtain ⟨b,u,l⟩:= mem_biUnion.mp y; exact disjoint_left.mp (d (show a≠b from fun e=> p (e.symm ▸ u))) t l) -- tune
 have hv(B)(u:B∈Q): Blend (spool H V r) (A*F) (f (coaster r K B • x B)) := by
    obtain ⟨g,w⟩:= mem_filter.mp u; have ht:=mem_powerset.mp g; rw [map_smul]; exact ((((hh B ht).smul (coaster r K B)).extendsTo (mul_le_mul (fund_V r B p) (pow_le_pow_right₀ r₀ ((card_le_card ht).trans_eq p)) (by positivity) (by positivity))).mono (fun a y=>Spool.weaken _ y w (biUnion_subset_biUnion_of_subset_left _ ht))) -- tune F unfold
 rw [dissolve _ _ _ p.ge t, map_sum]; apply (Blend.sum Q _ _ hv).extendsTo
 rw [sum_const,nsmul_eq_mul]; have hx: (Q.card:ℝ) ≤ 2^(10*r):=by exact_mod_cast (show Q.card ≤ 2^(10*r) from (card_le_card (filter_subset _ _)).trans_eq ((card_powerset K).trans (by rw [p]))) -- wrong filter
 refine (mul_le_mul_of_nonneg_right hx (by unfold A F; positivity)).trans_eq ?_; unfold A F; rw [mul_pow,←pow_mul,←pow_mul,← mul_assoc,← pow_add]; congr 2; omega
end beads
end YM.CF.Pannier.Chancel.Lantern.Stencil
open YM.CF.Pannier.Chancel.Lantern.Stencil
#print axioms loads_clean
#print axioms loads_dirty
