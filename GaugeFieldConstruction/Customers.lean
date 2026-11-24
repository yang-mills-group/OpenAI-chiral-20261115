import GaugeFieldConstruction.Pillars
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Fock.Flux
open Function NormedSpace Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B T L: Op I}{b:ℝ}{w:Wave I}
lemma dg_diff (A B:Op I): dg (A-B)=dg A-dg B:= by rw [sub_eq_add_neg,dg_add,dg_neg, ←sub_eq_add_neg]
def penny (v:Bool)(P:Op I):Op I:= if v then 1-P else P
def dustAnn (v:Bool)(P:Op I)(x:Ket I): FC I:= creed v (acts (penny v P) x)
lemma dust_star (v:Bool)(P:Op I)(x:Ket I): creed v x= star (dustAnn (!v) P x)+dustAnn v P x:=by
 have hx:x=acts (1-P) x+acts P x:= by rw [act_sub,act_one,sub_add_cancel]
 cases v
 · unfold dustAnn; change create x=star (remove (acts (1-P) x))+create _; unfold remove; rw [star_star]; nth_rw 1 [hx]; rw [map_add]; rfl
 unfold dustAnn; change remove x=star (create (acts P x))+remove (acts _ x); change star (create _) =star _ +star _; nth_rw 1 [hx]; rw [map_add,star_add,add_comm]; rfl
lemma dust_kills (v:Bool)(x:Ket I)(h:IsStarProjection P)(u:Sea P w): acts (dustAnn v P x) w=0:=by
 unfold dustAnn; cases v
 · apply tarp h u.1; rw [←act_mul]; change acts (P*P) x=_; rw [h.isIdempotentElem.eq]; rfl
 apply tars h u.1; rw [←act_mul]; change acts (P*(1-P)) x=_; rw [Porth h,act_zero]
-- antiB pairing scalar. both uses genuine create/remove with signs. compatible word order.
def laceSC (b w:Bool)(x y:Ket I):ℂ:= if b=w then 0 else if b then inner ℂ x y else inner ℂ y x
lemma centSC (b w:Bool)(x y:Ket I): antiB (creed b x) (creed w y)=laceSC b w x y • 1:=by
 cases b <;> cases w
 · simp [creed,laceSC, antiB, car_create]
 · exact (add_comm _ _).trans (car y x)
 · exact car x y
 simp only [laceSC,true_iff,Bool.not_eq_false,ite_true,zero_smul]; exact car_rem ..
lemma lace_le (b c:Bool)(x y:Ket I): ‖laceSC b c x y‖ ≤ ‖x‖*‖y‖:=by unfold laceSC; split_ifs; simp only [norm_zero]; positivity; exact norm_inner_le_norm ..; exact (norm_inner_le_norm ..).trans_eq (mul_comm ..)
lemma penny_proj (h:IsStarProjection P)(v:Bool):IsStarProjection (penny v P):=by cases v; exact h; exact h.one_sub
lemma dust_char (h:IsStarProjection P)(v:Bool)(x:Ket I): ‖acts (penny v P) x‖ ≤ ‖x‖:=by
 cases isEmpty_or_nonempty I; · exact le_of_eq (by rw [Subsingleton.elim (acts _ x) x])
 apply (Flare.opy ..).trans; exact mul_le_of_le_one_left (norm_nonneg _) ((penny_proj h v).norm_le _)
-- expectation of high-cost counts.
def febrile (P:Op I)(u:Wave I):ℝ:= (inner ℂ u (acts (Flux.excite P) u)).re
lemma spend_grades (P:Op I)(h:IsStarProjection P) :
   (∑ i,star (dustAnn false P (basisKet i))*dustAnn false P (basisKet i)) +(∑ i,star (dustAnn true P (basisKet i))*dustAnn true P (basisKet i))=excite P:=by
 let Q:=1-P; let F(i:I):=acts P (basisKet i); let V(i:I):=acts Q (basisKet i)
 change (∑ i,remove (F i)* create (F i))+(∑ i,star (remove (V i))*remove (V i))= _
 have hx(A:Op I)(h:IsStarProjection A):∑ i,create (acts A (basisKet i))*remove (acts A (basisKet i))=dg A:= by rw [←prizeUV,h.isSelfAdjoint,h.isIdempotentElem.eq]
 simp_rw [show ∀ x: Ket I, remove x*create x =(inner ℂ x x) • (1:FC I)-create x*remove x from fun x=>eq_sub_of_add_eq (car x x),show ∀ x:Ket I,star (remove x)=create x from fun x=>star_star _]
 have he(i:I): inner ℂ (F i) (F i)=P i i:=by
    have hh: acts (star P) (basisKet i)= F i:= by rw [h.isSelfAdjoint]
    nth_rw 1 [← hh]; rw [act_inner,show acts P (F i)=F i from (by unfold F; rw [←act_mul,h.isIdempotentElem.eq]),basis_inner]; exact basis_act ..
 have hs:P.trace= (P.trace.re:ℂ):= Complex.ext rfl (by
    obtain ⟨U,S,e'⟩:=spot_projection P h; rw [e', trace_twist, trace_cut]; simp)
 rw [sum_sub_distrib,hx _ h,hx _ h.one_sub,←Finset.sum_smul, show (∑ i,inner ℂ (F i) (F i))= ((rband P):ℂ) from (sum_congr rfl fun i _=>he i).trans hs,Complex.coe_smul]
 have hg (x:Op I): (2:ℝ) • x=x+x:= two_smul ℝ x
 unfold excite; rw [hg P,dg_diff 1 P,dg_diff,dg_add]; abel
lemma count_penny (h:IsStarProjection P)(x:Wave I):
 (∑ i, ‖acts (dustAnn false P (basisKet i)) x‖^2)+(∑ i, ‖acts (dustAnn true P (basisKet i)) x‖^2)=febrile P x:=by
 let F(v:Bool)(i:I):= dustAnn v P (basisKet i)
 unfold febrile; rw [← spend_grades P h,act_add,inner_add_right,Complex.add_re];
 have hh(v:Bool): (inner ℂ x (acts (∑ i,star (F v i)* F v i) x)).re= ∑ i, ‖acts (F v i) x‖^2:=by
    rw [act_sum,inner_sum,Complex.re_sum]; apply sum_congr rfl; intro i _; rw [act_mul,←act_inner,star_star]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
 rw [hh false,hh true]
lemma febrile_pos (h:IsStarProjection P)(u:Wave I):0 ≤ febrile P u:= by rw [←count_penny h]; exact add_nonneg (sum_nonneg (fun i _=>sq_nonneg _)) (sum_nonneg (fun i _=>sq_nonneg _))
lemma ann_sum (v:Bool)(h:IsStarProjection P)(u:Wave I): ∑ i, ‖acts (dustAnn v P (basisKet i)) u‖^2 ≤ febrile P u:=by rw [←count_penny h]; cases v; exact le_add_of_nonneg_right (sum_nonneg (fun i _=>sq_nonneg _)); exact le_add_of_nonneg_left (sum_nonneg (fun i _=>sq_nonneg _))

section frames
variable {J:Type*}(S:Finset J){A:Op I}{C D:ℝ}
abbrev fitV (x:J → Ket I) (C:ℝ):Prop:= ∀ u:Ket I,∑ j∈S, ‖inner ℂ u (x j)‖^2 ≤ C*‖u‖^2
lemma fit_mono (x:J→ Ket I)(p:fitV S x C){L:Finset J}(f:L⊆ S) (e:C≤D): fitV L x D:=by
 intro u; exact ((sum_le_sum_of_subset_of_nonneg f (fun _ _ _=>sq_nonneg _)).trans (p u)).trans (mul_le_mul_of_nonneg_right e (sq_nonneg _))
lemma fit_move (x:J→Ket I)(v:fitV S x C)(f:0 ≤ C)(h: ‖A‖≤D) : fitV S (fun i=> acts A (x i)) (C*D^2):=by
 cases isEmpty_or_nonempty I with
 | inr u =>
    intro i; simp_rw [← act_inner]; apply (v (acts (star A) i)).trans
    have hf: ‖acts (star A) i‖ ≤ D*‖i‖:=(Flare.opy ..).trans (mul_le_mul_of_nonneg_right ((norm_star A).le.trans h) (norm_nonneg _)); rw [mul_assoc,←mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hf _) f
 | inl e=>
    intro i; rw [Subsingleton.elim i 0]; simp
-- Bessel test via coordinate extraction
lemma basis_draw {ι:Type*}[Fintype ι][DecidableEq ι](x:Ket ι): (∑ i:ι, ‖inner ℂ (basisKet i) x‖^2) = ‖x‖^2:=by
 simp_rw [basis_inner]; exact (PiLp.norm_sq_eq_of_L2 _ x).symm
lemma dust_wallet (u:Wave I)(X: J→ Ket I)(p:fitV S X C)(c:0 ≤ C)(h:IsStarProjection P)(v: Bool) : ∑ i∈S, ‖acts (dustAnn v P (X i)) u‖^2 ≤ C*febrile P u:=by
 let V(x):= acts (dustAnn v P x) u
 let Q(i):= V (basisKet i); have hp(k:Finset I): (∑ i∈S, ‖inner ℂ (basisKet k) (V (X i))‖^2) ≤ C*∑ i:I, ‖inner ℂ (basisKet k) (Q i)‖^2:=by
    let B(x:Ket I):= inner ℂ (basisKet k) (V x)
    let T:= fun i:I=>B (basisKet i)
    let H(i:I):= if v then T i else star (T i); let L:= ∑ i, H i • basisKet i
    have hf(i:I): inner ℂ (basisKet i) L = H i:=by unfold L; rw [inner_sum]; simp [inner_smul_right, apply_ite]
    have hz(v:Bool)(k:Finset I)(x:Ket I): inner ℂ (basisKet k) (acts (dustAnn v P x) u)= ∑ i, (if v then star (x i) else x i)*inner ℂ (basisKet k) (acts (dustAnn v P (basisKet i)) u):=by
       cases v
       · let S: Ket I→ₗ[ℂ] FC I := create.comp (acts P).toLinearMap
         have hp: S x=∑ i, x i • S (basisKet i):=by nth_rw 1 [←basis_expand x]; rw [map_sum]; simp only [map_smul]
         change inner ℂ _ (acts (S x) u)=_; rw [hp,act_sum,inner_sum]; apply sum_congr rfl; intro i _; rw [act_smul,inner_smul_right]; rfl
       let S': Ket I→ₗ[ℂ] FC I:= create.comp (acts (1-P)).toLinearMap
       have hp:S' x=∑ i, x i • S' (basisKet i):=by nth_rw 1 [←basis_expand x]; rw [map_sum]; simp only [map_smul]
       change inner ℂ _ (acts (star (S' x)) u)=_; rw [hp,star_sum,act_sum,inner_sum]; apply sum_congr rfl; intro i _; rw [star_smul,act_smul,inner_smul_right]; rfl
    have hB(x:Ket I): ‖B x‖= ‖inner ℂ L x‖:=by
       have hh: inner ℂ L x=∑ i:I,star (H i)*x i:= by unfold L; rw [sum_inner]; simp only [inner_smul_left,basis_inner]; rfl -- tune
       rw [show B x=∑ i,(if v then star (x i) else x i)*T i from hz v k x,hh]; cases hv:v
       · congr 1; apply sum_congr rfl; intro i _; simp [H,hv,mul_comm]
       simp only [H,hv,ite_true]; rw [←norm_star (∑ i:I,star (x i)*T i),star_sum]; congr 1; apply sum_congr rfl; intro i _; simp [star_mul]

    change (∑ i∈S, ‖B (X i)‖^2) ≤ C* ∑ i:I, ‖T i‖^2; simp_rw [hB]; apply (p L).trans_eq; rw [←basis_draw L]; simp_rw [hf]; congr 1; cases hv:v <;> simp [H,hv]
 simp_rw [← basis_draw (acts (dustAnn v P _) _)]; rw [sum_comm]; -- RHS rewrites? tune
 apply le_trans (sum_le_sum (fun k _=>hp k)) ?_
 rw [←mul_sum,sum_comm]; simp_rw [basis_draw]; exact mul_le_mul_of_nonneg_left (ann_sum v h u) c
end frames
end YM.CF.Fock.Flux
end
