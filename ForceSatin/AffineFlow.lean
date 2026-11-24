import ForceSatin.Excitation
import YM.CF.BProof.Wick.Grad
/-! Instead of paying WA.6-8 via Laurent log evaluations, interpolate the
    whole affine pencil and keep the same linear cost at every point. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Matrix Thera Verses
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false
variable {I : Type}[LinearOrder I][Fintype I][Nonempty I]
variable {J : Type*}[DecidableEq J]
private def mat (A:J→FC I)(r:ℝ) (i:J):=1+r • A i
def affineProd (A:J→FC I)(L:List J)(r:ℝ) := rollC (mat A r) L
section
variable (A:J→FC I) (L:List J)
lemma prod_cons (i:J) (r:ℝ) : affineProd A (i::L) r=(1+r • A i) * affineProd A L r:=by unfold affineProd rollC; rw [List.map_cons,List.prod_cons]; rfl
private lemma prod_nil (r:ℝ): affineProd A [] r=1:=rfl
lemma prod_start : affineProd A L 0=1:= by induction L with | nil=> exact prod_nil .. | cons i L ih=> rw [prod_cons,ih, zero_smul,add_zero,mul_one]
lemma prod_finish : affineProd A L 1=rollC (fun i=>1+A i) L:=by unfold affineProd mat; simp

variable (h:∀ i∈L,∀ j∈L,Commute (A i) (A j))
include h in
lemma extract (r:ℝ)(i:J)(p:i∈L) : affineProd A L r = (1+r • A i)*affineProd A (L.erase i) r:=by
  induction L with
  | nil=> contradiction
  | cons j L ih=>
    by_cases e:i=j; · subst j; rw [List.erase_cons_head,prod_cons]
    have hv:= h _ List.mem_cons_self _ p
    have hx : Commute (1+r • A j) (1+r • A i):= (Commute.one_left _).add_left ((Commute.one_right _).add_right ((hv.smul_left r).smul_right r))
    have ht:i∈L:=(List.mem_cons.mp p).resolve_left e
    rw [List.erase_cons_tail (by simpa [BEq.beq] using Ne.symm e), prod_cons, ih (fun i a j b=> h _ (List.mem_cons_of_mem _ a) _ (List.mem_cons_of_mem _ b)) ht, ←mul_assoc, hx.eq,mul_assoc,←prod_cons]

include h in
lemma prod_derivative (p:L.Nodup)(r:ℝ): HasDerivAt (affineProd A L) (∑ i∈ L.toFinset, A i * affineProd A (L.erase i) r) r:=by
  induction L with
  | nil=> simp only [List.toFinset_nil, Finset.sum_empty]; exact hasDerivAt_const r _
  | cons i L ih=>
     let Z:=fun r:ℝ=>1+r • A i
     have hz:HasDerivAt Z (A i) r:=by unfold Z; simpa using ((hasDerivAt_id' r).smul_const (A i)).const_add 1
     have ht:= ih (fun i p j q=> h _ (List.mem_cons_of_mem _ p) _ (List.mem_cons_of_mem _ q)) p.of_cons
     rw [show affineProd A (i::L)=(fun x=> Z x * affineProd A L x) from funext fun x=> prod_cons ..]
     refine (hz.fun_mul ht).congr_deriv ?_
     rw [List.toFinset_cons,Finset.sum_insert (by simpa using (List.nodup_cons.mp p).1),List.erase_cons_head,mul_sum]; apply congrArg; apply Finset.sum_congr rfl; intro j hj; have e:j≠i:= fun h=> (List.nodup_cons.mp p).1 (h ▸ List.mem_toFinset.mp hj)
     have he : Commute (Z r) (A j):=(Commute.one_left _).add_left ((h i List.mem_cons_self j (List.mem_cons_of_mem _ (List.mem_toFinset.mp hj))).smul_left r)
     rw [List.erase_cons_tail (by simpa [BEq.beq] using Ne.symm e),prod_cons,←mul_assoc,he.eq,mul_assoc]
end
-- t-tilt context at the checkpoint
variable {P:Op I}(T:Shaft I)(p:IsStarProjection P)
def advent (P:Op I)(T:Shaft I)(r:ℝ) (x:Wave I) := acts (grow (excitation P) (1-r)) (acts (quant T.sell) x)

include p in
lemma advent_map (r:ℝ)(A:FC I)(x: Wave I): advent P T r (acts A x)=acts (((tilt P (1-r)).foldC T).glow A) (advent P T r x):=by
  -- tilt_action copy w less imports
  unfold advent; rw [tilt_quant_exp p]; simp only [acts_scalar, ContinuousLinearMap.map_smul_of_tower]
  let K := (tilt P (1-r)).foldC T
  congr 1
  rw [←act_mul (quant (grow _ _)),←act_mul (quant (grow _ _)),←quant_mul]
  change acts (quant K.sell) (acts A x) = acts (K.glow A) (acts (quant K.sell) x)
  rw [←act_mul, ←act_mul, Shaft.glow,mul_assoc (quant K.sell * A), ←quant_mul,K.pay,quant_one,mul_one]

include p in
lemma posture_deriv (L:List J)(A:J→FC I)(h:∀ i∈L,∀ j∈L,Commute (A i) (A j))(d:L.Nodup)(x:Wave I)(r:ℝ) :
    let y l r:=advent P T r (acts (affineProd A l r) x)
    let K:=(tilt P (1-r)).foldC T
    HasDerivAt (y L) ( -(acts (excitation P) (y L r)) + ∑ i∈L.toFinset,acts (K.glow (A i)) (y (L.erase i) r)) r:=by
  intro y K; let N:=excitation P
  let f(t:ℝ):=affineProd A L t; let Z(t:ℝ):=quant T.sell * f t; let W(i:J):= affineProd A (L.erase i) r
  have he:HasDerivAt Z (quant T.sell * ∑ i∈L.toFinset,A i*W i) r:= (prod_derivative A L h d r).const_mul _
  let F(t:ℝ):=grow N (1-t)
  have hF : HasDerivAt F (- (N * F r)) r:=by
    let u:= (hasDerivAt_id' r).const_sub 1
    exact ((hasDerivAt_exp_smul_const' N (1-r)).scomp r u).congr_deriv (by simp; rfl)
  refine (BProof.Wick.act_der (e:=BProof.Wick.act_der_const he x) hF).congr_of_eventuallyEq ?_|>.congr_deriv ?_
  · filter_upwards with t; unfold y advent; rw [←act_mul (quant _)]
  congr 1
  · rw [act_neg,act_mul,show F r=grow (excitation P) (1-r) from rfl]; unfold Z; rw [act_mul]; rfl
  rw [act_mul (quant _),act_sum,map_sum,map_sum]; apply Finset.sum_congr rfl
  intro i _; rw [act_mul]; exact advent_map T p r ..


omit [Nonempty I] in
private lemma vector_pulse {x y:Wave I}{A:FC I}{B r:ℝ}(b:‖A‖≤B)(h:B ≤ 1/2) (p:r∈ Set.Icc (0:ℝ) 1)
    (e:x=y+r • acts A y) :
    (inner ℂ x (acts A y)).re ≤ (inner ℂ x (acts A x)).re + 2*B^2*‖x‖^2 := by
  have hr:‖r‖ ≤1:=by rw [Real.norm_of_nonneg p.1]; exact p.2
  have hB:0 ≤ B:=(norm_nonneg _).trans b
  have hu(w:Wave I): ‖acts A w‖ ≤ B*‖w‖:=(Graph.spentS ..).trans (mul_le_mul_of_nonneg_right b (norm_nonneg w))
  have hz:‖x-y‖ ≤ B*‖y‖:=by rw [show x-y=r • acts A y from (by rw [e]; abel),norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans (hu y)
  have hk: ‖y‖ ≤ 2*‖x‖:=by
    have he:= norm_sub_norm_le y x; rw [norm_sub_rev y] at he; linarith only [mul_le_mul_of_nonneg_right h (norm_nonneg y),he,hz]
  apply (sub_le_iff_le_add').mp; rw [←Complex.sub_re, ←inner_sub_right,←map_sub]
  apply le_trans (Complex.re_le_norm _); apply (norm_inner_le_norm ..).trans; apply (mul_le_mul_of_nonneg_left (hu (y-x)) (norm_nonneg x)).trans
  rw [norm_sub_rev]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left hk hB)) hB) (norm_nonneg _)).trans_eq ?_; ring

lemma real_norm_deriv {g:ℝ→Wave I}{r:ℝ}{x y:Wave I} (hr : x=g r)(hv:HasDerivAt g y r):
    HasDerivAt (fun t=> ‖g t‖^2) (2*(inner ℂ x y).re) r:=by
  have he:= hv.inner ℂ hv
  have hh(t:ℝ):‖g t‖^2=Complex.reCLM (inner ℂ (g t) (g t)):= by rw [inner_self_eq_norm_sq_to_K]; simp [←Complex.ofReal_pow]
  simp_rw [hh]; apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r he).congr_deriv
  change Complex.re (_ + _) = _
  rw [Complex.add_re]; simp only [hr]; nth_rw 1 [show inner ℂ y (g r)= star (inner ℂ (g r) y) from (inner_conj_symm ..).symm]; rw [show (star (inner ℂ (g r) y)).re=(inner ℂ (g r) y).re from rfl]; ring

lemma pulse_growth {f:ℝ→Wave I}(f':ℝ→Wave I)(C:ℝ)(h:∀ t∈ Set.Icc (0:ℝ) 1, HasDerivAt f (f' t) t)
 (p:∀ t∈Set.Icc (0:ℝ) 1,(inner ℂ (f t) (f' t)).re ≤ C*‖f t‖^2) : ‖f 1‖ ≤ Real.exp C * ‖f 0‖:=by
  let D: Set ℝ := Set.Icc 0 1; let G(r:ℝ):=Real.exp (-2*C*r)*‖f r‖^2
  let H(r:ℝ):= Real.exp (-2*C*r)* (2*((inner ℂ (f r) (f' r)).re-C*‖f r‖^2))
  have hg(r)(u:r∈D) : HasDerivAt G (H r) r:=by
    apply ((((hasDerivAt_id' r).const_mul (-2*C)).exp).fun_mul (real_norm_deriv rfl (h r u))).congr_deriv
    unfold H; ring
  have hx:AntitoneOn G D:=by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) (fun i h=>(hg i h).continuousAt.continuousWithinAt) (fun i h=>(hg i (interior_subset h)).differentiableAt.differentiableWithinAt) (fun i h=>?_)
    rw [(hg _ (interior_subset h)).deriv]; exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr (p i (interior_subset h))))
  have he:G 1≤G 0:= hx ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one
  apply le_of_pow_le_pow_left₀ (by decide : (2:ℕ) ≠ 0) (by positivity) ?_
  unfold G at he; rw [mul_one,mul_zero,Real.exp_zero,one_mul,show -2*C= -(C+C) from (by ring),Real.exp_neg, Real.exp_add] at he
  rw [mul_pow,sq (Real.exp C)]; exact (inv_mul_le_iff₀ (by positivity)).mp he

include p
lemma lift_adjacent (r:ℝ)(L:List J)(A:J→FC I)(x:Wave I)(i:J)(e:i∈L)(h:∀ i∈L,∀ j∈L,Commute (A i) (A j)) :
    let y l:=advent P T r (acts (affineProd A l r) x)
    let K:=(tilt P (1-r)).foldC T
    y L=y (L.erase i)+ r • acts (K.glow (A i)) (y (L.erase i)):=by
  intro y K
  dsimp only [y]; nth_rw 1 [extract A L h r i e]; rw [act_mul,advent_map T p]
  rw [←Complex.coe_smul  r (A i),Shaft.glow_sum,Shaft.glow_free,Shaft.glow_nil,act_add,act_one,act_smul,Complex.coe_smul]

theorem full_growth (A:J→FC I)(L:List J)(v:L.Nodup)(w:∀ i∈L,∀ j∈L,Commute (A i) (A j))(C D:ℝ)
    (h:C ≤ 1/2)
    (e:∀ t∈Set.Icc (0:ℝ) 1,let K:=(tilt P t).foldC T; (∀ i∈L,‖K.glow (A i)‖ ≤ C) ∧
      (∀ x:Wave I, ∑ i∈L.toFinset,(inner ℂ x (acts (K.glow (A i)) x)).re ≤ active P x + D*‖x‖^2))
    (x:Wave I) :
    ‖acts (quant T.sell) (acts (affineProd A L 1) x)‖ ≤
          Real.exp (D + 2*C^2*L.length)*‖advent P T 0 x‖:=by
  let K(r:ℝ):=(tilt P (1-r)).foldC T
  let f(l:List J)(r:ℝ):=advent P T r (acts (affineProd A l r) x)
  let Z(r:ℝ)(i:J):=acts ((K r).glow (A i)) (f (L.erase i) r)
  let H(r:ℝ):= -(acts (excitation P) (f L r))+∑ i∈ L.toFinset, Z r i
  have he(r):HasDerivAt (f L) (H r) r:= posture_deriv T p L A w v x r
  let D':= D+ 2*C^2*L.length
  have hD(r:ℝ)(hr:r∈Set.Icc (0:ℝ) 1): (inner ℂ (f L r) (H r)).re ≤ D'*‖f L r‖^2:=by
    obtain ⟨hp,ht⟩:= e (1-r) (show 1-r ∈ Set.Icc (0:ℝ) 1 from ⟨sub_nonneg.mpr hr.2, sub_le_self 1 hr.1⟩)
    specialize ht (f L r)
    unfold H; rw [inner_add_right,inner_neg_right,inner_sum,Complex.add_re, Complex.neg_re,Complex.re_sum]
    let V:=f L r; let g(i:J):=(inner ℂ V (acts ((K r).glow (A i)) V)).re; let a:=active P V; let d:=2*C^2*‖V‖^2
    change -a+ _ ≤ _
    apply le_trans (add_le_add_right (a:=-a) (sum_le_sum (g:=fun i=>g i+d) ?_))
    · rw [sum_add_distrib, sum_const, nsmul_eq_mul,List.toFinset_card_of_nodup v]; unfold D' d; change _ +(_+_ ) ≤ _*‖V‖^2; linarith only [show (∑ i∈L.toFinset,g i)≤a+D*‖V‖^2 from ht]
    intro i hi; have hj:=List.mem_toFinset.mp hi
    exact vector_pulse (hp i hj) h hr (lift_adjacent T p r L A x i hj w)
  have hk := pulse_growth H D' (fun r _=> he r) hD
  rw [show f L 1=acts (quant T.sell) (acts (affineProd A L 1) x) from (?_),show f L 0=advent P T 0 x from (by unfold f; rw [prod_start,act_one])] at hk
  exact hk
  unfold f advent; simp [grow]
end YM.CF.Papyrus.Franc.SatinForce
