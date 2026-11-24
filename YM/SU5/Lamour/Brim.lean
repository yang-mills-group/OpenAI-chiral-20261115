import YM.SU5.Lamour.Melange
/-! # Basis-coefficient absolute price inside ANY chart -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 130000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace Flare Pannier.Chancel Velvet Pannier.Damask Pastry Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n α:Type*}[LinearOrder n][Fintype n]
def shadeK(T:Finset n)(i:n): Bool:= decide (i∉T)
def seedling(T:Finset n)(i:n):= creed (shadeK T i) (basisKet i)
def tome(T S:Finset n) := prime (seedling T) (fun _=>0) S
variable (T : Finset n){S R:Finset n}{b:Bool}{F: FC n}
@[simp] lemma shade_true (i:n):shadeK T i=true ↔ i∉T:= decide_eq_true_iff
@[simp] lemma shade_false(i:n):shadeK T i=false ↔ i∈T:=by simp [shadeK]
lemma seedTrim (i):trim (hand (shadeK T i) (cutM T)) (basisKet i):=by cases h:shadeK T i; exact (cut_basis ..).trans (if_pos ((shade_false ..).mp h)); change acts (1-cutM T) _=_; rw [←dim_cut,cut_basis,if_pos (mem_compl.mpr ((shade_true T i).1 h))]
                                                                  
lemma seed_f (i) (h:i∈T): seedling T i= put i :=by rw [seedling,(shade_false ..).2 h]; exact create_put i
lemma seed_t (i)(h:i∉T): seedling T i=takeF i:=by rw [seedling,(shade_true ..).2 h]; exact remove_take i
lemma primeC (T S:Finset n): tome T S=((S.sort (· ≤ ·)).map (seedling T)).prod:=by unfold tome prime; rw [show (fun (_:n) => (0:FC n))=0 from rfl,add_zero]
@[simp] lemma tome_nil:tome T ∅=1:=prime_nil ..
lemma tome_l(i:n)(g:Flies i S):tome T (insert i S)=seedling T i*tome T S:=by rw [tome,prime_min _ _ g,add_zero]; rfl
lemma tome_r(i:n)(g:Grass S {i}):tome T (insert i S)=tome T S*seedling T i:=by rw [tome,prime_last _ _ g,add_zero]; rfl
lemma number (S:Finset n):‖tome T S‖≤1:=by
 induction S using Finset.induction_on_min with
 | empty=> simp
 | insert i S h ih=> rw [tome_l T i h]; apply (norm_mul_le ..).trans; exact mul_le_one₀ ((cost_pe ..).trans_eq (by simp)) (norm_nonneg _) ih
open scoped symmDiff
lemma reveal (S:Finset n): ∃ u:ℂ, ‖u‖=1∧acts (star (tome T S)) (basisKet T)=u • basisKet (symmDiff T S):=by
 induction S using Finset.induction_on_max with
 | empty=> exact ⟨1,by simp,by simp [symmDiff]⟩
 | insert i S v ih=>
    have h:i∉S:=fun l=>lt_irrefl _ (v i l); obtain ⟨u,y,k⟩:=ih
    let R:=symmDiff T S
    rw [tome_r T i (show Grass S {i} from fun j w k e=>by rw [mem_singleton.mp e]; exact v _ w),star_mul,act_mul,k,map_smul]
    by_cases w:i∈ T
    · refine ⟨u*parity i R, by rw [norm_mul,y]; simp [parity,norm_pow],?_⟩
      rw [seed_f T i w,take_act]; have ht:i∈R:=by simp [R,symmDiff,h,w]
      rw [if_pos ht,smul_smul]; unfold R; rw [show symmDiff T (insert i S)=(symmDiff T S).erase i from (by ext u; by_cases e:u=i<;> simp [symmDiff,e,w,h]<;> tauto)]
    refine ⟨u*parity i R, by rw [norm_mul,y]; simp [parity,norm_pow],?_⟩
    rw [seed_t T i w,takeF,star_star,put_act]; have ht:i∉R:=by simp [R,symmDiff,h,w]
    unfold R at *; rw [if_neg ht,smul_smul]; rw [show symmDiff T (insert i S)=insert i (symmDiff T S) from (by ext u; by_cases e:u=i<;> simp [symmDiff,e,w,h]<;> tauto)]
lemma flower_dot (S R: Finset n): let P(U):= acts (star (tome T U)) (basisKet T); inner ℂ (P S) (P R)=if S=R then 1 else 0:=by
 intro P; unfold P; obtain ⟨u,t,h⟩:= reveal T S; obtain ⟨x,v,g⟩:= reveal T R; by_cases e:S=R
 · subst R; simp [inner_self_eq_norm_sq_to_K,h,norm_smul,t]
 rw [h,g,inner_smul_right,inner_smul_left,basis_inner,basis_apply,if_neg,if_neg e,mul_zero,mul_zero] -- orientation
 intro x; apply e; ext i; by_cases h:i∈T; all_goals first| skip
 all_goals have hp:= Finset.ext_iff.mp x i; simp [symmDiff, h] at hp ⊢; tauto
lemma controlled (w:Finset n→ℂ)(e:F=∑ i∈ S.powerset,w i • tome T i)(u:R⊆S): ‖w R‖ ≤ ‖F‖:=by
 let P(U):= acts (star (tome T U)) (basisKet T)
 have hv:‖P R‖=1:=by obtain ⟨u,t,h⟩:= reveal T R; simp [P,h,norm_smul,t]
 have ht: inner ℂ (P R) (acts (star F) (basisKet T))=star (w R):=by
    rw [e,star_sum,act_sum,inner_sum,sum_eq_single_of_mem _ (mem_powerset.mpr u)]; · rw [star_smul,act_smul,inner_smul_right,(flower_dot T R R),if_pos rfl,mul_one] -- let P
    intro i _ u; change inner ℂ (P R) _ = _; rw [star_smul,act_smul,inner_smul_right,(flower_dot T R i),if_neg u.symm,mul_zero]
 rw [← norm_star (w R),←ht]; exact (norm_inner_le_norm ..).trans (by rw [hv,one_mul]; exact (operate_f ..).trans_eq (by simp))
lemma think_t (i): (think T).term i=(if i∈T then (1:ℂ) else -1) • seedling T i:=by
 by_cases h:i∈ T; · rw [show (think T).term i=put i from if_pos h,if_pos h,seed_f T i h,one_smul]
 rw [show (think T).term i= -takeF i from if_neg h,if_neg h,seed_t T i h,neg_one_smul]
lemma book_fold (S:Finset n): (think T).tag S=(∏ i∈ S,(if i∈T then (1:ℂ) else -1)) • tome T S:=by
 induction S using Finset.induction_on_min with
 | empty=> simp [Poly.tag_void]
 | insert i S h ih=> rw [prod_insert (Flies.out h),tome_l T i h,Poly.tag_any _ _ _ (Flies.out h), think_t,ih,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Flies.free h,one_smul,smul_smul,mul_comm (∏ i∈S,_)]
variable {T}
theorem farm_bill (u:Fine T S b F): ∃ w:Finset n→ℂ,(∀ i⊆ S,‖w i‖≤ ‖F‖)∧ F=∑ i∈ S.powerset,w i • tome T i:=by
 obtain ⟨x,⟨w,v⟩,e⟩:= u.writer; let t(i):= w i * ∏ j∈ i,(if j∈T then (1:ℂ) else -1); have hp: F=∑ i∈ S.powerset,t i • tome T i:=by rw [e,v,map_sum]; apply sum_congr rfl; intro i p; rw [map_smul,Poly.eval_oneT,book_fold,smul_smul];
 exact ⟨t,fun _ h=> controlled T t hp h, hp⟩
-- certify tolls from pressure proofs Uniform λ^{-card}. use seed account
variable [Nonempty n]{z:ℝ}
def moldP {Z:Op n}(h:IsStarProjection Z)(u:0<z): FC n→ₐ[ℂ]FC n where
 toFun := modifyB Z z
 map_one':= by rw [modifyB,mul_one,pushV h u]
 map_add' x y:=by simp only [modifyB,mul_add,add_mul]
 map_zero':=by simp [modifyB]
 map_mul' x y:=by unfold modifyB; let X:=quant (castV Z z); let Y:=quant (castV Z z⁻¹); have hp:Y*X=1:=mul_eq_one_comm.mp (pushV h u); change X*(x*y)*Y=X*x*Y*(X*y*Y); rw [mul_assoc (X*x),←mul_assoc Y,←mul_assoc Y,hp]; simp [mul_assoc] -- tune
 commutes' c:=by simp only [modifyB, Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,mul_one,pushV h u]
lemma mold_bill {P:Op n}(x:IsStarProjection P)(p:0<z)(u:z≤1)(h:Fine T S b F): ‖modifyB P z F‖ ≤ ‖F‖*(2*(flowCost z+1))^S.card :=by
 obtain ⟨w,q,r⟩:=farm_bill h; let L:=moldP x p; let v:= flowCost z+1; have hs: 1≤v:=le_add_of_nonneg_left (flow_pos p).le; have hx(Y): ‖L (tome T Y)‖ ≤ v^Y.card:=by
    induction Y using Finset.induction_on_min with
    | empty=> simp
    | insert i Y h ih=>
       let e:Token n:= ⟨(shadeK T i,basisKet i), (cost_pe ..).trans_eq (by change ‖basisKet i‖=1; simp)⟩
       have ht:‖L (seedling T i)‖≤ v:=by change ‖modifyB P z (creed (shadeK T i) (basisKet i))‖≤v; rw [modifies_creed x p]; exact ((cost_pe ..).trans (reader_price x u p e)).trans (le_add_of_nonneg_right zero_le_one)
       rw [card_insert_of_notMem (Flies.out h),pow_succ',tome_l T i h,map_mul]; exact (norm_mul_le ..).trans (mul_le_mul ht ih (norm_nonneg _) (by linarith))
 let d:=‖F‖ * v^S.card; change ‖L F‖≤ _; nth_rw 1 [r]; rw [map_sum]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>d) (fun i ti=> ?_)).trans_eq ?_)
 · rw [map_smul,norm_smul]; exact mul_le_mul (q i (mem_powerset.mp ti)) ((hx i).trans (pow_le_pow_right₀ hs (card_le_card (mem_powerset.mp ti)))) (norm_nonneg _) (norm_nonneg _)
 rw [sum_const,nsmul_eq_mul,card_powerset]; change _=‖F‖*(2*v)^ _; push_cast; unfold d; rw [mul_pow]; ring
end YM.CF.Lamour
#print axioms YM.CF.Lamour.farm_bill
#print axioms YM.CF.Lamour.mold_bill
