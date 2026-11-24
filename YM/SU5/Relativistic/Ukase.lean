import YM.SU5.Relativistic.Raspa
import YM.CF.BProof.Garden.Settle
/-! # Cylinder and near-unique occupied compression. *All* in one T. -/
set_option autoImplicit false
set_option maxHeartbeats 270000
noncomputable section
namespace YM.CF.Papyrus.Franc.Pea
open Function Filter NormedSpace Fock Thera Finset BProof.Align BProof.Wick BProof.Garden
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
-- avoid matrix operator precedence
variable (A:Pea I)
def hat : FC I:= ((A.candy:ℂ)⁻¹ • quant A.mint.buy)
def tagH : FC I:= (A.candy:ℂ) • quant A.mint.sell
lemma intake : A.hat*A.tagH=1:=by unfold hat tagH; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, ←quant_mul,A.mint.pay, quant_one,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr A.duty.ne'),one_smul]
lemma receive : A.tagH*A.hat=1:= mul_eq_one_comm.mp A.intake
lemma star_h : IsSelfAdjoint A.hat:=by unfold IsSelfAdjoint hat; rw [star_smul,star_inv₀, show star (↑A.candy:ℂ)= (A.candy:ℂ) from Complex.conj_ofReal _, ←quant_star, show star A.mint.buy=A.mint.buy from A.tale _ _]
lemma co_tag {A B:Pea I}(p:Zones A B): p.fuse.tagH=A.tagH*B.tagH:=by unfold tagH; rw [divin p, Complex.ofReal_mul, minted p]; simp only [Shaft.foldC,quant_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; module
lemma co_hat {A B:Pea I}(p:Zones A B): p.fuse.hat=B.hat*A.hat:=by unfold hat; rw [divin p, Complex.ofReal_mul, minted p]; simp only [Shaft.foldC,quant_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, mul_inv, smul_smul]
variable (U:UNI I) (s t:Finset I)(x:A.fill=twist U (cutM s))(y:A.pour=twist U (cutM t))(h:Disjoint s t)
include x y h
private lemma cannon (k l:ℝ) (z:|1+k| ≤2)(v:|1+l|≤2) [Nonempty I] : ‖A.Φ k l‖≤2:=by
 rw [A.phile U s t x y h, twist_norm,Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr; intro i; split; rw [Complex.norm_real]; exact z; split; rw [Complex.norm_real]; exact v; simp
lemma own: A.hat=twist (quantU U) (grab s t (2⁻¹:ℂ)):=by
 let z:ℂ:=2⁻¹
 rw [← contracts (u:=z) (by unfold z; norm_num) h, offer_spec z s t h, twist_scalar,←quant_twist]; unfold hat candy; rw [A.nodes_spec _ _ x]; push_cast; rw [inv_pow,show A.mint.buy=A.Φ 1 (-(1/2:ℝ)) from rfl,A.phile _ _ _ x y h]; norm_num [z] -- tune
-- arithmetic wedge estimate
structure GlowGap (P:FC I):Prop where
  head : IsStarProjection P
  shell : A.hat*P=P
  grade : ‖A.hat*(1-P)‖≤1/2
  cap : ‖A.hat‖≤1
-- f basis
lemma glowGap : GlowGap A (twist (quantU U) (cabin s t)):=by
 let W:=twist (quantU U); let K:=permit s t; let H:=cutM K; let R(Z:Finset I):=s.card-(Z∩s).card+(Z∩t).card
 have he(i:Finset I): i∈ K ↔ R i=0:=by
    have hx:grab s t 0 i i= cabin s t i i:= congrArg (fun V:FC I=>V i i) (permit_spec ..); change i∈ permit s t ↔ _; rw [grab,cabin,cutM,Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at hx; change (0:ℂ)^R i=(if i∈permit s t then 1 else 0) at hx
    by_cases h:R i=0 <;> by_cases p:i∈ permit s t <;> simp_all only [↓reduceIte, pow_zero,h,zero_pow, not_false_eq_true,zero_ne_one,p,one_ne_zero] <;> (rw [zero_pow h] at hx; norm_num at hx)
 let Q:= grab s t (2⁻¹:ℂ); let f(i:Finset I):=(2⁻¹:ℂ)^R i; have ht:Q=Matrix.diagonal f:=rfl
 constructor
 · let V:= W H; have hx:IsStarProjection H:= cutM_idp _; exact ⟨(show V*V=V from (map_mul W H H).symm.trans (congrArg W hx.isIdempotentElem.eq)),(show star V=V from (map_star W H).symm.trans (congrArg W hx.isSelfAdjoint.star_eq))⟩
 · rw [A.own U s t x y h,←map_mul]; apply congrArg; change Q*H=H; rw [ht]; unfold H cutM; rw [Matrix.diagonal_mul_diagonal]; apply congrArg; funext i; by_cases p:i∈ K; rw [if_pos p, mul_one]; unfold f; rw [(he i).mp p,pow_zero]; simp [p] -- tune Pi
 · rw [A.own U s t x y h,←map_one (twist (quantU U)),←map_sub,←map_mul, twist_norm]; change ‖Q*(1-H)‖≤ _; rw [ht,show (1:FC I)-H=cutM Kᶜ from (by unfold H cutM; ext i j; by_cases h:i=j; subst j; by_cases p:i∈K <;> simp [p]; simp [h]),cutM,Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr; intro i; split
   next w=>rw [mul_one]; unfold f; rw [norm_pow,norm_inv,show ‖(2:ℂ)‖=(2:ℝ) from (by norm_num)]; have hg:0<R i:=Nat.pos_of_ne_zero (mt (he i).2 (mem_compl.mp w)); exact le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hg) (by simp)
   simp
 · rw [A.own _ _ _ x y h, twist_norm]; change ‖Q‖ ≤1; rw [ht,Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr; intro i; unfold f; rw [norm_pow,norm_inv,show ‖(2:ℂ)‖=(2:ℝ) from (by norm_num)]; exact pow_le_one₀ (by norm_num) (by norm_num)
omit x y h
lemma signed [Nonempty I] : ‖A.mint.sell‖≤2 ∧ ‖A.mint.buy‖≤2:=by
 obtain ⟨U,s,t,x,y,h⟩:=A.laid; exact ⟨A.cannon U s t x y h _ _ (by norm_num) (by norm_num),A.cannon U s t x y h _ _ (by norm_num) (by norm_num)⟩
-- matrix copy for even with arbitrary complement occupancy. No grading sign issue
private lemma harbor {P:FC I}(p:Sector (s∪t) false P)(h:Disjoint s t) : ∃ c:ℂ,cabin s t * P*cabin s t=c • cabin s t:=by
 let C:=cabin s t; let Y:=C* P*C; let B(x:Finset I):=basisKet x; let V:=acts P (B s)
 let d:=V.ofLp s
 have hp:C*C=C:= (cabin_proj ..).isIdempotentElem
 have hx:acts (C*P*C) (B s)=d • B s:=by
    have he:s∈permit s t:=by simp [h.symm]
    unfold C B; rw [act_mul,cabin_basis,if_pos he,act_mul]; apply sideSlot h
    intro i hi; rw [basis_act]; by_contra z; obtain ⟨j,g,y⟩:= Finset.not_subset.mp hi; have hk : j∈s := (p.dotGrade i s z j y).2 g; exact y (Finset.mem_union_left _ hk)
 have hv(l:Finset I)(g:Disjoint (s∪t) l): acts Y (B (l∪s))=d • B (l∪s):=by
    induction l using Finset.induction_on with
    | empty=> simpa only [empty_union] using hx -- tune
    | insert i r e ih=>
      have he:i∉ s∪t:=fun v=> disjoint_left.mp g v (mem_insert_self ..); have hc:i∉ r∪s:=by intro p; exact (mem_union.mp p).elim e fun j=>he (mem_union_left _ j)
      let x:=parity i (r∪s); have hy:x≠0:=by unfold x parity; exact pow_ne_zero _ (by norm_num) -- tune
      have hh:put i*Y=Y*put i:=(council (show Sector (s∪t) false Y from (((BProof.Wick.tagged (subset_union_left ..) (subset_union_right ..)).mul p).mul (tagged (subset_union_left ..) (subset_union_right ..)))) (Sector.up i (mem_singleton_self i)) (by exact Finset.disjoint_singleton_right.mpr he)).eq.symm
      have hk:insert i r∪s=insert i (r∪s):= Finset.insert_union ..
      apply smul_right_injective (Wave I) hy
      change x • _=x • _; rw [hk,←map_smul, show x • B (insert i (r ∪ s))=acts (put i) (B (r∪s)) from ((put_act i (r∪s)).trans (if_neg hc)).symm] -- phase dependent tune rhs moved under d
      rw [←act_mul, ←hh,act_mul,ih (Finset.disjoint_of_subset_right (Finset.subset_insert i r) g),map_smul]; rw [(put_act i (r∪s)|>.trans (if_neg hc))]; exact smul_comm ..
 refine ⟨d,op_columns (fun i=>?_)⟩
 rw [act_mul,cabin_basis,act_smul,cabin_basis]; split_ifs with t'
 ·
    have hh:=hv (i\s) (show Disjoint (s∪t) (i\s) from Finset.disjoint_left.mpr (fun j a x=> (Finset.mem_union.mp a).elim (fun j=> (mem_sdiff.mp x).2 j) (fun l=> Finset.disjoint_left.mp ((permit_rule ..).mp t').2 l (mem_sdiff.mp x).1)))
    rw [sdiff_union_of_subset ((permit_rule ..).mp t').1] at hh; change _= d • _; unfold Y B C at hh; rw [act_mul,cabin_basis, if_pos t'] at hh; exact hh
 simp
include x y h
lemma pen_sect {X:FC I}(g:Sector (s∪t) false (twist (star (quantU U)) X)): ∃ c:ℂ,let H:=twist (quantU U) (cabin s t); H*X*H=c • H:=by
 obtain ⟨p,f⟩:= harbor s t g h; refine ⟨p,?_⟩; intro H; have hg:= congrArg (twist (quantU U)) f; rw [map_mul,map_mul,twist_scalar, show twist _ (twist _ X)=X from (by nth_rw 1 [←star_star (quantU U)]; exact twist_inv ..)] at hg; exact hg -- tune
end YM.CF.Papyrus.Franc.Pea
#print axioms YM.CF.Papyrus.Franc.Pea.pen_sect
