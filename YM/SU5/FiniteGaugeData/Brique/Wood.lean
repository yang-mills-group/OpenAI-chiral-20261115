import YM.CF.Fock.Compressed
import YM.CF.Sedge.Aurum
import YM.CF.Flare.Wits
/-! Many-mode damping on the honest Sea, with eigenvalue formula on a purchased full/empty sector. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Fock.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
-- open Rush Scroll
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
local notation "Ω"=> Fintype.card n
local notation "Θ"=> Finset n
local notation "Γ"=> quant
variable {P:Op n} {x:Wave n} {X:ℝ}
section
variable (P X)
def scaleUp : Op n:= ((Real.exp X:ℝ):ℂ) • P + (1-P)
lemma up_mul (h:IsStarProjection P)(T:ℝ): scaleUp P X * scaleUp P T = scaleUp P (X+T):=by
  unfold scaleUp; rw [Real.exp_add,Complex.ofReal_mul]; simp only [mul_add,add_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rw [show P*P=P from h.1,show (1-P)*P=0 by rw [sub_mul,one_mul,(show P*P=P from h.1),sub_self], show P*(1-P)=0 by rw [mul_sub,mul_one,(show P*P=P from h.1),sub_self],show (1-P)*(1-P)=1-P from h.one_sub.1]; simp only [smul_zero,add_zero,zero_add,smul_smul,mul_comm]
lemma up_self: scaleUp P 0=1:=by simp [scaleUp]
lemma up_star (h:IsStarProjection P) : star (scaleUp P X)=scaleUp P X:=by
 unfold scaleUp; rw [star_add,star_smul,star_sub,star_one,h.2.star_eq,show star ((Real.exp X:ℝ):ℂ)= _ from Complex.conj_ofReal (Real.exp X)]
lemma up_cost [Nonempty n] (h:IsStarProjection P): ‖scaleUp P X‖ ≤ Real.exp X+1:=by
 refine (norm_add_le ..).trans (add_le_add ?_ (h.one_sub.norm_le _)); rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_of_le_one_right (Real.exp_pos _).le (h.norm_le _)
lemma up_twist (U:UNI n): scaleUp (twist U P) X=twist U (scaleUp P X):=by rw [scaleUp,scaleUp,map_add,map_sub,twist_scalar,map_one]
end
/- occupied sector proposition even for noncoordinate local bases (the rank can be huge). -/
def Full (P: Op n)(x:Wave n): Prop:= ∀ u:Ket n, acts P u=u → acts (create u) x=0
def Vacant (P: Op n)(x:Wave n): Prop:= ∀ u:Ket n, acts P u=u → acts (remove u) x=0
lemma Full.coordinates (S:Θ)(v:Full (cutM S) x) {T:Θ}(p:¬ S⊆T): x.ofLp T=0:=by
 obtain ⟨i,hs,ht⟩:=not_subset.mp p; have he:= congrArg (fun x:Wave n=> x.ofLp (insert i T)) (v (basisKet i) (by rw [cut_basis,if_pos hs])); dsimp only at he
 rw [create_put, put_row,if_pos (mem_insert_self ..), erase_insert ht] at he; change parity _ _*x.ofLp T=0 at he
 rw [← one_mul (x.ofLp T),← parity_sq i (insert i T),mul_assoc,he,mul_zero]
lemma Full.swirled (v: Full P x)(U:UNI n): Full (twist U P) (acts (quantU U).val x):=by
 intro q p; let y:=acts (star U.val) q; have ht:acts P y=y:= by
    have t:=congrArg (fun x=>acts (star U.val) x) p; rw [← act_starUnit U q,← swivel,act_unit] at t -- wrong pattern
    simpa [act_starUnit] using t
 rw [← show twist (quantU U) (create y)=create q by rw [twist_create, show acts U.val y=q from act_starUnit ..],← swivel,v y ht,map_zero] -- ← not needed
lemma scaleUp_cut (S:Θ) (X:ℝ): scaleUp (cutM S) X=Matrix.diagonal (fun i=> if i∈S then (((Real.exp X):ℝ):ℂ) else 1):=by
 apply op_scale_column; intro i; rw [scaleUp,act_add,act_smul,act_sub,act_one,cut_basis]; by_cases p:i∈S <;> simp [p]
private lemma prod_scale (S T:Θ)(p:T⊆S)(X:ℝ): ∏ i∈ S,(if i∈T then (((Real.exp X):ℝ):ℂ) else 1) = (((Real.exp X):ℝ):ℂ)^T.card :=by
 rw [← prod_filter]; rw [show S.filter (·∈T)= T by ext; refine mem_filter.trans ?_; grind]
 simp
lemma Full.eigen0 (S:Θ)(p:Full (cutM S) x)(X:ℝ): acts (quant (scaleUp (cutM S) X)) x = (((Real.exp X):ℝ):ℂ)^S.card • x:=by
  apply PiLp.ext; intro t; rw [scaleUp_cut,quant_diag,diag_apply]; change _ = _*x.ofLp t; by_cases g:S⊆t; rw [prod_scale t S g]; rw [Full.coordinates S p g, mul_zero,mul_zero]
lemma Full.eigen (h:IsStarProjection P)(p: Full P x)(m:ℕ)(H:P.trace=m)(X:ℝ): acts (quant (scaleUp P X)) x= (((Real.exp X):ℝ):ℂ)^m • x:=by
 obtain ⟨U,S,rfl⟩:=spot_projection _ h; let y:=acts (star (quantU U).val) x
 have hy:= Full.swirled p (star U); rw [twist_inv U (cutM S),quantU_star] at hy
 rw [up_twist,quant_twist]; nth_rw 1 2 [← act_starUnit (quantU U) x]; rw [←swivel]
 rw [trace_twist,trace_cut] at H; have xz:S.card=m:=by exact_mod_cast H
 change Full _ y at hy; change (acts ↑(quantU U)) (acts (Γ (scaleUp (cutM S) X)) y) = ((↑(Real.exp X):ℂ)^m) • (acts ↑(quantU U)) y; rw [←xz,Full.eigen0 S hy,map_smul]
-- damping comparison via FULL and Γ(A); no rank cost in wedge bound beyond Fintype card of native Single, not Wave. 
lemma Full.damped (h:IsStarProjection P)(p:Full P x)(m:ℕ)(H:P.trace=m)(X:ℝ)(y:Wave n):
   ‖inner ℂ x y‖=(Real.exp (-X))^m * ‖inner ℂ x (acts (quant (scaleUp P X)) y)‖:=by
 rw [←act_inner,←quant_star,up_star _ _ h,(p.eigen h m H X),inner_smul_left,norm_mul]; simp only [RCLike.norm_conj,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; rw [←mul_assoc,Real.exp_neg,←mul_pow,inv_mul_cancel₀ (Real.exp_ne_zero _),one_pow,one_mul]

lemma wing_opy (A:FC n)(x:Wave n) : ‖acts A x‖ ≤ ‖A‖*‖x‖:= ((acts A).le_opNorm x).trans_eq (by rw [show ‖acts A‖=‖A‖ from Matrix.l2_opNorm_toEuclideanCLM A])
lemma wingBill [Nonempty n] (C:ℝ)(t:0 ≤ C)(A:Op n)(g:‖A‖ ≤ C)(S:Θ):‖wedge A S‖ ≤ C^S.card:=by
 induction S using induction_on_min with
 | empty => simp [wedge_empty,vacuum,basisKet]; -- tune
 | insert i s h ih=>
    have ht: ‖acts A (basisKet i)‖ ≤ C:=(Flare.opy A (basisKet i)).trans (by simp [basisKet,g])
    let U:= create (acts A (basisKet i)); have hv:‖U‖≤ C:= le_trans (Flare.cost_pe false (acts A (basisKet i))) ht
    rw [wedge_min A s i h,card_insert_of_notMem (fun u=>lt_irrefl i (h i u)),pow_succ']; exact (show ‖acts U (wedge A s)‖ ≤ ‖U‖*‖wedge A s‖ from wing_opy U (wedge A s)).trans (mul_le_mul hv ih (norm_nonneg _) t)
lemma Sea_wing [Nonempty n] (h:IsStarProjection P)(u:Sea P x)(A:Op n)(C:ℝ)(hc:1≤C)(g:‖A‖ ≤ C):‖acts (quant A) x‖ ≤ C^Ω:=by
 let w:=zero_le_one.trans hc; obtain ⟨U,s,rfl⟩:= spot_projection _ h; let v:= wedge U.val s; let c:= inner ℂ v x
 have he:x=c • v:= u.1.symm.trans (act_twistLine ..); have hv: ‖c‖=1:=by
    have hp:=u.2; rw [he,norm_smul,show ‖v‖=1 from wedge_norm U s,mul_one] at hp; exact hp
 rw [he,map_smul,norm_smul,hv,one_mul,show v= acts (quant _) _ from (quant_column _ s).symm,←act_mul,←quant_mul,quant_column]; refine (wingBill C w _ ?_ _).trans (pow_le_pow_right₀ hc (card_le_univ s)); exact (norm_mul_le ..).trans (by rw [CStarRing.norm_of_mem_unitary U.property,mul_one]; exact g)
lemma Sea_upper [Nonempty n] (h:IsStarProjection P)(u:Sea P x)(A:Op n)(C:ℝ)(hc:1≤C)(g:‖A*P‖ ≤ C):‖acts (quant A) x‖ ≤ C^Ω:=by
 have e:acts (quant P) x=x:=by nth_rw 1 [← u.1]; rw [←act_mul,line_quant h]; exact u.1
 have he:= Sea_wing h u _ C hc g; rwa [quant_mul,act_mul,e] at he
end YM.CF.Fock.Brique
