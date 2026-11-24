/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Minster
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5800
set_option maxHeartbeats 280000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Lattice.Corona.Hive
open Function Filter MeasureTheory NormedSpace Finset
open scoped Topology BigOperators Classical
section purse
variable {α β I:Type}[Fintype I](U:I→ℝ)(X:Finset I)
local notation "A"=> X.powerset
lemma packP_Ω (h:∀ i,0≤U i):
  (∑ J∈ X.powerset,∏ i∈J,U i) ≤ Real.exp (∑ i∈X,U i):=by
 have e: (∏ i∈X,(U i+1))=∑ J∈X.powerset,∏ i∈J,U i:=by rw [Finset.prod_add]; simp
 rw[←e,Real.exp_sum]; exact Finset.prod_le_prod (fun i _=> add_nonneg (h _) zero_le_one) (fun _ _=>Real.add_one_le_exp _)
lemma packP_i (h:∀ i,0≤U i)(i:I): (∑ J∈ X.powerset with i∈J,∏ i∈J,U i) ≤ U i*Real.exp (∑ i∈ X,U i):=by
    by_cases hi:i∈ X
    · apply le_trans _ (mul_le_mul_of_nonneg_left (packP_Ω U X h) (h i)); rw[mul_sum]
      let S:= (A).filter fun J=>i∈ J; let g(J:Finset I):=J.erase i
      apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (show S.image g⊆ A from ?_) (fun j _ _=> mul_nonneg (h _) (prod_nonneg fun i _=>h _))); swap
      · intro J p; obtain ⟨R,t,rfl⟩:= mem_image.mp p; exact mem_powerset.mpr ((erase_subset ..).trans (mem_powerset.mp (mem_filter.mp t).1))
      apply le_of_eq; rw [sum_image]; refine sum_congr rfl fun a p=>?_
      · exact (Finset.mul_prod_erase _ _ (Finset.mem_filter.mp p).2).symm -- tune
      intro a ha b hb e; exact (insert_erase (Finset.mem_filter.mp ha).2).symm.trans ((congrArg (insert i) e).trans (insert_erase (Finset.mem_filter.mp hb).2))
    rw [sum_eq_zero]; exact mul_nonneg (h _) (Real.exp_pos _).le
    intro j u; obtain ⟨k,g⟩:=mem_filter.mp u; exact False.elim (hi (mem_powerset.mp k g))
lemma packP_hit (h:∀ i,0≤ U i)(u:Finset I): (∑ J∈ A with ¬Disjoint J u,∏ i∈J,U i)≤ (∑ i∈X∩u,U i)*Real.exp (∑ i∈ X,U i) :=by
 rw [sum_mul]
 apply le_trans _ (sum_le_sum (fun i (_:i∈ X∩u)=>packP_i U X h i))
 simp_rw[sum_filter (p:=fun J=>_ ∈ J)] -- tune RHS only
 rw[sum_comm]; let S:= (A).filter fun J=> ¬Disjoint J u
 apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (show S⊆ A from filter_subset ..) (fun j _ _=>sum_nonneg fun i _=> by split; exact prod_nonneg fun _ _=> h _; exact le_rfl))
 refine Finset.sum_le_sum (fun a p=> ?_)
 obtain ⟨w,t⟩:=mem_filter.mp p; obtain ⟨i,h,hg⟩:=Finset.not_disjoint_iff.mp t
 have q₁:=show (if i∈a then ∏ i∈a,U i else 0)≤ _ from Finset.single_le_sum (f:=fun i=> if i∈a then ∏ i∈a,U i else 0) (fun j _=>by split; exact prod_nonneg (fun _ _=>‹∀ i,0≤U i› _); exact le_rfl) (mem_inter.mpr ⟨mem_powerset.mp w h,hg⟩); rwa[if_pos h] at q₁
end purse
section singular
variable {n:Side}{I:Type}[Fintype I]
variable {b:ℕ}{L:List (Site n)}{a η:ℝ}(A:Support n)(y:Site n)
variable {Ω:ℝ}
local notation "C"=> ColdB b a η L
local notation "R"=> RedB b a η L
local notation "c"=> Cube_M b
local notation "XΓ"=>ridg b A
variable (S:I→Support n)(U:I→ℝ)(p:∀ i,0≤U i)(l:Scales b a η L)(g:0≤Ω)(q:∀ y:Site n,postG S U (ColdB b a η L) y ≤ Ω)(t:Cube_M b*Ω≤1)
include l p
lemma packMerge (J:Finset I)(z:J⊆ clouds S A) : ( (∏ i∈J,U i) * (C (A∪ J.biUnion S))) ≤ C A * ∏ i∈J,beam S U C i:=by
 rw [Finset.prod_mul_distrib]; refine (mul_le_mul_of_nonneg_left (Temp_join b (a+2*ζd) η L A (add_nonneg l.a0 (by unfold ζd; norm_num)) l.pos.le S J (fun i t=> (Finset.mem_filter.mp (z t)).2)) (prod_nonneg (fun i _=>p i))).trans_eq ?_; ring
include g q t
lemma fog : Real.exp (∑ i∈clouds S A, beam S U C i)≤ridg b A:=by
 let x:=Ω; have h:=clouds_site S (beam S U C) (fun i=>mul_nonneg (p i) (Temp_p ..|>.le)) A Ω q
 apply Real.exp_monotone; apply h.trans; have hb := t
 have hx: x*cubeCt b ≤ ζd := by unfold x; rw[mul_comm]; apply le_of_mul_le_mul_right _ (inv_pos.mpr ζdp); unfold Cube_M at hb; have he:= mul_le_mul_of_nonneg_right hb ζdp.le; field_simp at * ; try linarith -- tune
 exact (mul_le_mul_of_nonneg_left (heft_card b A) g).trans (by rw[←mul_assoc]; exact mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _))
omit l p g q t in
lemma coldB_duo :ColdB b a η L A*XΓ^2≤ R A:=le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (ridg_one b A) (by norm_num:2≤4)) (Temp_p ..|>.le)) (Eq.le (coldB_le ..))
lemma guide (K:Finset (Finset I))(v:∀ x∈K,x.Nonempty)(h:∀ x∈ K,x⊆ clouds S A):
 (∑ J∈K,(∏ i∈J,U i) * C (A∪ J.biUnion S)) ≤ R A*(c*Ω):=by
 let S₀:= clouds S A; let f:= beam S U C; have p₁(i):0≤ f i:=mul_nonneg (p i) (Temp_p ..|>.le)
 apply (sum_le_sum (fun i hi=>packMerge A S U p l i (h _ hi))).trans; rw[←mul_sum]
 let G':=S₀.powerset.filter fun J=>¬ Disjoint J univ
 have z:K⊆ G':=fun i hi=> mem_filter.mpr ⟨mem_powerset.mpr (h _ hi),by obtain ⟨b,p⟩:=v i hi; exact Finset.not_disjoint_iff.mpr ⟨b,p,mem_univ _⟩⟩
 have y: (∑ i∈K,∏ j∈i,f j)≤ Ω*c * (ridg b A)^2:=by
    have E:= (Finset.sum_le_sum_of_subset_of_nonneg z (fun i _ _=>prod_nonneg fun j _=>p₁ j)).trans (packP_hit f S₀ p₁ univ)
    refine E.trans ?_; rw [inter_univ]
    have a' := (clouds_site S f p₁ A _ q).trans (mul_le_mul_of_nonneg_left (hefty b A) g)
    exact (mul_le_mul a' (fog A S U p l g q t) (Real.exp_pos _).le (le_trans (Finset.sum_nonneg fun i _=>p₁ i) a')).trans_eq (by ring)
 exact (mul_le_mul_of_nonneg_left y (Temp_p ..|>.le)).trans ((le_of_eq (show (C A)*(Ω*c* _)= (C A* (ridg b A)^2)*(c*Ω) from by ring)).trans (mul_le_mul_of_nonneg_right (coldB_duo ..) (mul_nonneg (cube_M_pos b|>.le) g))) -- tune
lemma fuel_touch(K:Finset (Finset I))(o:Site n)(u:o∈ A)(pK:∀ i∈K,i⊆ clouds S A)(h:∀ i∈ K, y∈ i.biUnion S) : (∑ J∈ K,(∏ i∈J,U i) * C (A∪ J.biUnion S)) ≤ R A *(η⁻¹* respite b (a+2*ζd) η L S U o y) :=by
 apply (sum_le_sum (fun i hi=>packMerge A S U p l i (pK _ hi))).trans
 let Q:= (clouds S A); let U₀:=univ.filter fun i=>y∈ S i
 have hz:K⊆ (Q.powerset.filter (fun i=>¬ Disjoint i U₀)):=by
    intro i hi; obtain ⟨j,p,h⟩:=mem_biUnion.mp (h i hi); exact Finset.mem_filter.mpr ⟨mem_powerset.mpr (pK _ hi),not_disjoint_iff.mpr ⟨j,p,Finset.mem_filter.mpr ⟨mem_univ _,h⟩⟩⟩
 let f:= beam S U C; have ht(i): 0 ≤ f i:=mul_nonneg (p i) (Temp_p ..|>.le)
 have he:= (Finset.sum_le_sum_of_subset_of_nonneg hz (fun i _ _=>prod_nonneg fun j _=>ht j)).trans (packP_hit f Q ht U₀)
 have hb: Q ∩ U₀=Q.filter (fun i=>y∈ S i):=by ext; simp[U₀]
 rw [hb] at he
 let Z:= respite b (a+2*ζd) η L S U o y; let Θw:=η⁻¹*Z; have hh:0≤Θw:=mul_nonneg (inv_pos.mpr l.pos).le (respite_0 S U p o y _ η L b l.pos.le)
 have hy: (∑ i∈K,∏ j∈i,f j) ≤ Θw*(ridg b A)^2:=by
    refine he.trans (le_trans (mul_le_mul (clouds_release S U p A o y (a+2*ζd) η L b l.pos u) (fog A S U p l g q t) (Real.exp_pos _).le ?_) ?_)
    · change 0≤η⁻¹ * XΓ * Z; unfold Θw at hh; nlinarith only [mul_nonneg hh (ridg_pos b A|>.le)]
    unfold Θw Z; exact Eq.le (by ring)
 rw [←mul_sum]; apply (mul_le_mul_of_nonneg_left hy (Temp_p ..|>.le)).trans; exact ((le_of_eq (show C A* (Θw*(ridg b A)^2)= (C A*(ridg b A)^2)*Θw from by ring))).trans ((mul_le_mul_of_nonneg_right (coldB_duo ..) hh))
end singular
end YM.Lattice.Corona.Hive
end
