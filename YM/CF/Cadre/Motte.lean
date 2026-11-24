import YM.CF.Cadre.Clear
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
variable {κ:ℝ}
abbrev duty (κ:ℝ)(D:Finset A):ℝ:= if D.Nonempty then κ else 1
lemma duty_i(h:1≤κ): 1≤ duty κ D:=by unfold duty; split; exact h; rfl
lemma gorge (D P Q:Finset A)(K:Finset A→ℝ)(g:Disjoint P Q):
 ∑ T∈(P∪Q).powerset,K T=∑ j∈P.powerset,∑ i∈Q.powerset,K (j∪i):=by
 rw [← sum_product']; symm; refine sum_bij (fun z _=> z.1∪z.2) ?_ ?_ ?_ (fun i _=>rfl)
 · intro ⟨x,y⟩ u; obtain ⟨a,b⟩:=mem_product.mp u; exact mem_powerset.mpr (union_subset_union (mem_powerset.mp a) (mem_powerset.mp b))
 · have ho (j:Finset A×Finset A)(p:j∈P.powerset×ˢQ.powerset):((j.1∪j.2)∩P,(j.1∪j.2)∩Q)=j:=by
       obtain ⟨x,y⟩:= mem_product.mp p; have hp:=mem_powerset.mp x; have hv:=mem_powerset.mp y; apply Prod.ext
       · change (_∪_)∩_= _; rw [union_inter_distrib_right,inter_eq_left.mpr hp, disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hv g.symm),union_empty]
       change (_∪_)∩_= _; rw [union_inter_distrib_right,inter_eq_left.mpr hv, disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hp g),empty_union]
   intro i p j v e; exact ((ho i p).symm.trans ((congrArg (fun T=> (T∩P,T∩Q)) e).trans (ho j v)))
 intro j v; refine ⟨(j∩P,j∩Q), mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,mem_powerset.mpr inter_subset_right⟩,?_⟩; change (_∩_)∪(_∩_)=_; rw [←inter_union_distrib_left, inter_eq_left.mpr (mem_powerset.mp v)]
variable (w:Palot.leaf A→Finset A→ℝ)(q:∀ i:Palot.leaf A,∀ D ⊆ i.val,0 ≤ w i D)(v:1≤κ)
abbrev roofL(κ:ℝ)(i:ΣA):ℝ:=∑ D∈i.val.powerset,duty κ D*w i D
local notation "W"=> roofL w κ
abbrev wedgeL (w:leaf A→Finset A→ℝ)(D:Finset A)(G:ΣG):= ∏ j∈G,w j (D∩j.val)
lemma wing (G:ΣG)(S T:Finset A)(p:Disjoint S (robe G)): wedgeL w (S∪T) G=wedgeL w T G:=by unfold wedgeL; refine prod_congr rfl fun i z=>?_ ; rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp (Disjoint.mono_right (coneL z) p),empty_union] -- tune Fintype
include q v
lemma rope (h:flow A F): ∑ D∈(robe F).powerset, duty κ D*wedgeL w D F ≤ tilt W F :=by
 induction F using Finset.induction_on with
 | empty=>rw [tilt,prod_empty]; unfold robe wedgeL duty; simp
 |insert i F g ih=>
    have hp:=flow_d h g; have hv:= flow_m h (subset_insert i F); have hl:0≤ W i:=sum_nonneg fun j z=>mul_nonneg (zero_le_one.trans (duty_i _ v)) (q i _ (mem_powerset.mp z)); have hx:= mul_le_mul_of_nonneg_left (ih hv) hl
    unfold tilt; rw [prod_insert g]; apply le_trans _ hx; rw [←show i.val∪robe F=robe (insert i F) by unfold robe; rw [biUnion_insert],gorge (∅:Finset A) _ _ _ hp]; -- want RHS distribute multiplication of W.Lean order
    unfold roofL; rw [sum_mul] -- tune hx
    apply sum_le_sum; intro j z; rw [mul_sum]; apply sum_le_sum; intro k l; unfold wedgeL; rw [prod_insert g]; have he:Disjoint k i.val:= Disjoint.mono_left (mem_powerset.mp l) hp.symm; rw [union_inter_distrib_right,disjoint_iff_inter_eq_empty.mp he,inter_eq_left.mpr (mem_powerset.mp z),union_empty,show (∏ t∈F,w t _) = _ from wing w F j k (Disjoint.mono_left (mem_powerset.mp z) hp)]
    have ht:0≤ wedgeL w k F:=prod_nonneg (fun i _=> q i _ inter_subset_right); have hz:duty κ (j∪k) ≤ duty κ j*duty κ k:=by
        by_cases h:j.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp h,empty_union]; simp [duty]
        have hh:= duty_i k v; rw [duty,if_pos (h.mono subset_union_left)]; nth_rw 1 [show duty κ j=κ from if_pos h]; exact le_mul_of_one_le_right (by linarith) hh
    refine (mul_le_mul_of_nonneg_right hz (mul_nonneg (q i _ (mem_powerset.mp z)) ht)).trans_eq ?_; unfold wedgeL; ring
abbrev blast(X Y:ΣA)(C:Finset ΣG)(w:leaf A→Finset A→ℝ)(D:Finset A):=∑ G∈drum X Y D∩C, wedgeL w D G
lemma nodeV(X:ΣA)(C:Finset ΣG):∑ D∈X.val.powerset,duty κ D * blast X Y C w D ≤∑ G∈drum X Y ∅∩C,tilt W G:=by
 let T:=drum X Y ∅∩ C; have he(F:ΣG)(D: Finset A): F∈drum X Y D ∩C↔ F∈T∧D⊆robe F:=by unfold T; rw [mem_inter,mem_inter,drum_p,drum_p]; simp only [empty_subset, and_true]; tauto
 have hp(D:Finset A): blast X Y C w D=∑ G∈T, if D⊆robe G then wedgeL w D G else 0:=by unfold blast; rw [←sum_filter]; apply sum_congr _ (fun _ _=> rfl); ext; rw [he,mem_filter]
 simp_rw [hp,mul_sum]; rw [sum_comm]; refine sum_le_sum fun i u=> ?_; obtain ⟨⟨h,_⟩,p',k⟩:=(drum_p ..).mp (mem_inter.mp u).1; simp_rw [mul_ite,mul_zero]; rw [←sum_filter]; refine Eq.trans_le ?_ (rope i w q v h); apply congrArg (fun A=>∑ j∈A,duty κ j*wedgeL w j i); ext j; rw [mem_filter,mem_powerset,mem_powerset,and_iff_right_of_imp]; rw [k]; exact fun s=> subset_trans s subset_union_right
end YM.CF.Cadre
