import YM.SU5.Lamour.Scarf
/-! # Pay in separate Wick rooms. ANY ISSUED. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 220000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace Flare Pannier.Chancel Velvet Pannier.Damask Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[LinearOrder n][Fintype n][Fintype I][LinearOrder I]
-- 
local notation "⚒" => I ×ₗ n
def nestV(i:I):n ↪ ⚒:=⟨fun x=> toLex (i,x),fun x y h=>Prod.mk.inj (toLex.injective h)|>.2⟩
def bass (T:Finset n)(v:⚒): Bool:= shadeK T (ofLex v).2
def vpf(v:⚒): Ket n:=basisKet (ofLex v).2
def carton (i:I)(X:Finset n):Finset ⚒:= X.map (nestV i)
def glade (A:Op n)(T:Finset n): Op ⚒ := Matrix.of fun i j=> if (ofLex i).1=(ofLex j).1 then 0 else Hail (I:=⚒) (bass T) vpf A i j
def fringe(T:Finset n)(v:⚒): FC n:=seedling T (ofLex v).2
@[simp] lemma urn {X:Finset n}(i:I)(v:⚒): v∈carton i X ↔ (ofLex v).1=i ∧ (ofLex v).2∈ X:=by
 unfold carton; rw [mem_map]; refine ⟨?_,fun ⟨e,w⟩=>⟨(ofLex v).2,w,(by subst i; rfl)⟩⟩; rintro ⟨x,g,rfl⟩; exact ⟨rfl,g⟩
lemma turnP{X Y:Finset n}{i j:I}(p:i ≠ j): Disjoint (carton i X) (carton j Y):=disjoint_left.mpr fun v x y=> p (((urn ..).1 x).1.symm.trans ((urn ..).1 y).1)
lemma carton_comm(i:I)(T S:Finset n): rawT (I:=⚒) (bass T) vpf (carton i S)=tome T S:= by
 induction S using Finset.induction_on_min with
 | empty=> simp [carton,rawT,fo]
 | insert j S d ih=>
    let L:= nestV (n:=n) i; have hp:Flies (L j) (carton i S):=by
       intro k t; obtain ⟨k,w,rfl⟩:=mem_map.mp t; exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,d _ w⟩)
    rw [show carton i (insert j S)=insert (L j) (carton i S) from map_insert ..,rawT,sort_insert _ (fun v tv=> (hp v tv).le) (Flies.out hp),fo,List.map_cons,List.prod_cons, tome_l T j d]; change seedling T _*rawT _ _ _=_; rw [ih]; rfl
lemma glade_sym (A:Op n)(T:Finset n): (glade (I:=I) A T)ᵀ= -(glade A T):=by
 ext i j; unfold glade; simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]; by_cases f:(ofLex i).1=(ofLex j).1; simp [f]; rw [if_neg (Ne.symm f),if_neg f]; exact fern_comm
lemma carton_grass (i j:I)(A B:Finset n)(e:i < j) : Grass (carton i A) (carton j B):= by intro k p l u; obtain ⟨k,t,rfl⟩:=mem_map.mp p; obtain ⟨l,w,rfl⟩:=mem_map.mp u; exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl e)
lemma carton_cross {P:Op n} (T:Finset n) (p:IsStarProjection P)(i j:I)(A B:Finset n)(u:i≠j)(z:ℝ):
 let X:=glade (slant (cutM T) P z) T; let C':=Ciro (I:=⚒) (bass T) vpf P z; let A':=Airo (I:=⚒) (bass T) vpf P z
 Cross X C' A' (carton i A) (carton j B):=by
 intro X C' A' k y l v; have hk: (ofLex k).1=i:=(urn ..|>.1 y).1; have hl: (ofLex l).1=j:=(urn ..|>.1 v).1; unfold X glade; rw [Matrix.of_apply,if_neg (hk.symm ▸ (hl.symm ▸ u))]; exact facing (bass T) vpf (cutM_idp T) p (fun i=>seedTrim ..) _ k (mem_univ _) _ (mem_univ _)
lemma carton_head (X T:Finset n)(P:Op n)(i:I): Furl (glade P T) (carton i X):=by intro j h k p e; unfold glade; rw [Matrix.of_apply,if_pos (((urn ..).1 h).1.trans ((urn ..).1 p).1.symm)]
variable [Nonempty n]{R P:Op n}{z v w u y E:ℝ}{p T S:Finset n}{F:FC n}{b:Bool}
lemma boom_one {x:Wave n}(p:‖x‖=1)(h:IsStarProjection R)(u:0<z): boomR x h u 1=1 := by unfold boomR; simp; change inner ℂ x (acts 1 x)= _; simp [p]
def genBank(T:Finset n)(P:Op n)(z:ℝ)(S:Finset ⚒)(v w:ℝ):FC n→ Prop:= Grant (Ciro (I:=⚒) (bass T) vpf P z) (Airo (I:=⚒) (bass T) vpf P z) (glade (slant (cutM T) P z) T) S v w
lemma carton_v{p S:Finset n}(e:p⊆S)(i:I): carton i p⊆ carton i S := map_subset_map.mpr e
lemma bun_local (i:I){T:Finset n}(p:Bun (ray P T) S S v): Bun (Hail (bass T) vpf P) (carton i S) (carton i S) v:=by
 intro j q; obtain ⟨j,w,rfl⟩:= mem_map.mp q; unfold carton; rw [sum_map]; exact p j w
lemma grant_tome {x:Wave n}(i:I)(p:IsStarProjection P)(t:Sea P x)(h:0<z)(a:1≤w)(y:Bun (ray (slant (cutM T) P z) T) S S w)(s:0≤v)(q:v≤1): genBank T P z (carton i S) v (v*(2*w)^S.card) (modifyB (cutM T) z (tome T S-boomR x (cutM_idp T) h (tome T S) • 1)):=by
 let A:=cutM T; let D:=carton i S; let X:=tome T S; let L:= moldP (cutM_idp T) h; let b:=bass (I:=I) T; let p':=vpf (I:=I) (n:=n); let C':= Ciro b p' P z; let A':= Airo b p' P z; let H:= Hail b p' (slant A P z); let H':=glade (I:=I) (slant A P z) T; let S':=boomR x (cutM_idp T) h
 have ht(v): trim (hand (b v) A) (p' v):=seedTrim ..
 have he:Hail b p' (slant (cutM T) P z)= H:=rfl; have hh:L X=prime C' A' D:= (congrArg L (carton_comm i T S)).symm.trans (rawPrime b p' D h (cutM_idp T) ht P)
 have hl:=oatHC b p' D h (cutM_idp T) p t ht;
 change Grant C' A' H' D v _ (L (X-S' X • 1)); rw [map_sub,map_smul,map_one, show S' X=pf H D from ?_, hh,←show D.card=S.card from card_map _]; swap
 · exact  (congrArg S' (carton_comm i T S)).symm.trans hl
 exact Grant.turnRaw (glade_sym ..) (carton_head S T (slant A P z) i) (hail_turn b p' (slant A P z)) (Or.inl (cross_sub (facing _ _ (cutM_idp T) p ht z) (subset_univ _) (subset_univ _))) (bun_local i y) a s q
lemma Grant.sleet(i:I)(p:IsStarProjection P)(h:0<z)(a:1≤w)(y:Bun (ray (slant (cutM T) P z) T) S S w)(s:0≤v)(q:v≤1)(d:ℕ)(l:S.card≤d)(u: Fine T S b F)(x:Wave n)(t:Sea P x): genBank T P z (carton i S) v (‖F‖*v*(4*w)^d+‖boomR x (cutM_idp T) h F‖) (modifyB (cutM T) z F):=by
 let V:=boomR x (cutM_idp T) h; obtain ⟨W,Pw,f⟩:=farm_bill u; let g(p):= (W p) • (tome T p-V (tome T p) • 1); let Q:=carton i S; let L:=moldP (cutM_idp T) h; let B:=‖F‖*(v*(2*w)^d)
 have he:F=(∑ r∈S.powerset,g r) + V F • 1:=by
    rw [f,map_sum]; unfold g; simp_rw [smul_sub,_root_.map_smul,sum_smul, smul_smul,sum_sub_distrib] -- ℂ
    simp only [smul_eq_mul,sub_add_cancel]
 change genBank _ _ _ _ _ _ (L F); nth_rw 3 [he]; -- count?
 rw [map_add,map_smul,map_one]; change genBank _ _ _ Q _ _ ((L (∑ p∈S.powerset,g p))+_); apply Grant.plus; rw [map_sum]; refine (Grant.sumC (fun p=>L (g p)) (fun _=>B) _ (fun j u=> ?_)).up ?_
 · let C':= genBank T P z Q; let Uj:=mem_powerset.mp u; rw [show L (g j)=W j • L _ from (map_smul ..)]; apply (((grant_tome (S:=j) i p t h a (bun_sub y Uj) s q : Grant _ _ _ _ v _ _).sub (carton_v Uj i)).haze (W j)).up; unfold B; have hx:1≤2*w:= (by linarith); have ht:0≤w:=by linarith only [a]
   gcongr; apply Pw j Uj; exact Nat.le_trans (card_le_card Uj) l
 · rw [sum_const,nsmul_eq_mul,card_powerset]; push_cast; have ht:0<w:=lt_of_lt_of_le one_pos a; have hg:2^S.card ≤ (2:ℝ)^d:=pow_le_pow_right₀ (by norm_num) l; apply (mul_le_mul_of_nonneg_right hg (by unfold B; positivity)).trans_eq; unfold B; rw [show 4*w=2*(2*w) from (by ring),mul_pow (2:ℝ) (2*w)]; ring
 apply (Grant.haze Grant.one (V F)).up (by rw [mul_one]) -- tune
-- land condition via ℓ² of ray in complement. erased supports disjoint n. cross bound off
variable {d:ℕ}(φ:I→Finset n)(F:I→ FC n)(r:Finset I){V:Op n}
def skull:= r.biUnion fun i=> carton i (φ i) -- label envelope kept on unswept Wick
lemma grain_bun {φ:I→ Finset n} (g:(↑r:Set I).PairwiseDisjoint φ)(u: ∀ i∈r,Bun (ray P T) ((r.erase i).biUnion φ) (φ i) v): Bun (glade P T) (skull φ r) (skull φ r) v:=by
 intro j e; unfold skull; obtain ⟨i,v',u'⟩:= mem_biUnion.mp e; obtain ⟨j,w,rfl⟩:=mem_map.mp u';
 rw [sum_biUnion (by intro i _ j _ e; exact turnP e),←sum_erase_add _ _ v',sum_eq_zero (s:=carton i (φ i)),add_zero]; swap
 · intro k t; obtain ⟨k,w,rfl⟩:=mem_map.mp t; unfold glade nestV; simp only [Function.Embedding.coeFn_mk, Matrix.of_apply,ofLex_toLex,ite_true,norm_zero]; norm_num
 have hh:=u i v' j w; apply hh.trans'; apply le_of_eq
 rw [sum_biUnion (s:=r.erase i)]; apply sum_congr rfl; intro k p; rw [carton,sum_map]; refine sum_congr rfl fun l v=>?_ ; rw [glade,Matrix.of_apply,if_neg (show (ofLex (nestV k l)).1 ≠ (ofLex (nestV i j)).1 from (mem_erase.mp p).1)]; rfl
 exact Set.PairwiseDisjoint.subset g fun _ h=>mem_of_mem_erase h
variable {x y':Wave n}
lemma Ciro_price (x:n)(e:IsStarProjection P): ‖Ciro (shadeK T) basisKet P z x‖≤ ‖acts (wish (cutM T) P z (shadeK T x)) (basisKet x)‖:=by
 unfold Ciro leaf; apply (cost_pe ..).trans_eq; unfold cardH wish; congr 1; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [map_smul,act_smul,act_mul,seedTrim T x]
lemma Airo_price (x:n)(e:IsStarProjection P)(p:0<z): ‖Airo (shadeK T) basisKet P z x‖≤ z⁻¹:=by unfold Airo coal; apply ((cost_pe ..).trans (hand_cost _ e _)).trans_eq; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; simp
/-- cost center of *these Marks*, already subtracted flat. -/
theorem Trees (p:IsStarProjection P)(f:‖x‖=1)(e:Sea P x)(h:0<z)(l:z≤1)(k:Sea (cutM T) y')(V Z:FC n)(m:V=Z*fo F (r.sort (· ≤ ·)))(v':0<v)(q:4*v≤1)(g:(↑r:Set I).PairwiseDisjoint φ)
 (a:1≤w)(t:ℕ)(p':∀ i∈r,(φ i).card≤ t)(κ:∀ i∈r,Fine T (φ i) false (F i))
 (hc:∀ i∈r,Bun (ray (slant (cutM T) (draft P (cutM T) z) z) T) ((r.erase i).biUnion φ) (φ i) v) (hh:∀ i∈r, Bun (ray (slant (cutM T) (draft P (cutM T) z) z) T) (φ i) (φ i) w) (u:∀ i∈r,∀ j∈ φ i,‖acts (wish (cutM T) (draft P (cutM T) z) z (shadeK T j)) (basisKet j)‖≤ v)(B:I→ℝ)(y:∀ i∈r, ∀ X:Wave n,Sea (draft P (cutM T) z) X → ‖F i‖*(4*v)*(4*w)^t + ‖boomR X (cutM_idp T) h (F i)‖ ≤ B i):
 Yep ((z*v)⁻¹ * flowCost z) (acts (star V) y') x (‖modifyB (cutM T) z Z‖*(∏ i∈r,B i)*Real.exp (trade P (cutM T) z)) := by
 let Q:=cutM T; let D:= draft P Q z; let X:= skull φ r; let L:=moldP (cutM_idp T) h; let F'(i):=L (F i); let A:=Airo (I:=⚒) (bass T) vpf D z; let C':=Ciro (I:=⚒) (bass T) vpf D z; let K:=glade (I:=I) (slant Q D z) T; have hp:= (draft_lit p (cutM_idp T) h l).1
 obtain ⟨Z',v0,g0⟩:=gate_trace p (cutM_idp T) h l x e
 have he(k)(l:k∈r): Grant C' A K (carton k (φ k)) (4*v) (B k) (F' k):= (Grant.sleet k hp h a (hh k l) (show 0≤ (4*v) by positivity) q t (p' k l) (κ k l) _ v0 : Grant _ _ _ _ _ _ _).up (y k l Z' v0)
 have hg:=(Grant.gathers _ _ _ _ he (by positivity) (glade_sym ..) (fun i _=> carton_head (φ i) T _ i) (fun i _ j _ e=> ⟨carton_grass i j _ _ e, carton_cross T hp i j _ _ (ne_of_lt e) z⟩))
 refine Work v'.le ((one_le_inv₀ (by positivity)).2 (mul_le_one₀ l v'.le (by linarith))) (glade_sym (I:=I) _ _) (grain_bun r g hc) ?_ ?_ hg p e rfl k h l ?_ (fun _=> coal_letter _ _ _) (fun _ X h=> falls hp h _ _)
 · intro i d; obtain ⟨j,wJ,w⟩:= mem_biUnion.mp d; let V:= (urn ..|>.1 w).2; exact (Ciro_price (ofLex i).2 hp).trans (u j wJ _ V)
 · intro i d; change ‖A i‖ ≤ _; apply (Airo_price (ofLex i).2 hp h).trans_eq; rw [mul_inv, mul_left_comm,mul_inv_cancel₀ v'.ne',mul_one]
 -- L V eq
 change L V=L Z * fo F' _; rw [m,map_mul,fo,map_list_prod, List.map_map]; rfl
end YM.CF.Lamour
#print axioms YM.CF.Lamour.Trees
