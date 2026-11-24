import YM.CF.Flare.Dice
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Q:Op SpinIdx}{d:ℝ}
abbrev minA:Op SpinIdx:= 1-Aop
def warpF:= Aop * gammaOp 0
lemma A_id : IsStarProjection Aop := ⟨AOne,Aadj⟩
lemma minA_p: IsStarProjection minA:= A_id.one_sub -- tune
lemma in_f:gammaOp 0*Aop=minA*gammaOp 0:=by unfold minA; rw [Adef]; simp only [Matrix.smul_mul,Matrix.mul_smul,mul_add,sub_mul,add_mul,mul_one,one_mul,gradingSwap]; module
lemma jet_r: Aop *gammaOp 0=gammaOp 0 * minA:=by have he:=congr_arg star in_f; rw [star_mul,star_mul, (gammaAdj _).star_eq,Aadj, minA_p.isSelfAdjoint.star_eq] at he; exact he -- tune
lemma warp_l:Aop*warpF=warpF:=by unfold warpF; rw [←mul_assoc,AOne]
lemma warp_t:warpF*minA=warpF:=by unfold warpF; rw [jet_r, mul_assoc,minA_p.1]
lemma warp_sq:warpF*warpF=0:=by nth_rw 1 [← warp_t]; rw [mul_assoc,show minA*warpF=0 by unfold minA; rw [sub_mul,one_mul,warp_l,sub_self],mul_zero]
lemma warp_u:warpF*star warpF=Aop:=by unfold warpF; rw [star_mul, (gammaAdj _).star_eq,Aadj,←mul_assoc,mul_assoc Aop,gammaOne,mul_one,AOne]
lemma warp_norm:‖warpF‖≤1:=by
 have ht : ‖warpF*star warpF‖ = ‖warpF‖ * ‖warpF‖ := CStarRing.norm_self_mul_star; rw [warp_u] at ht; nlinarith [IsStarProjection.norm_le _ A_id,norm_nonneg warpF] -- name
variable {N:Side}{j:ℕ}{b:Candle}{M:Jill.Male}
def high_d(M:Jill.Male)(S:Slide N b)(i:Stag N)(j:ℕ):= disk j M (angle S i)
lemma crestQ (j)(M:Jill.Male)(S:Slide N b)(g:Even N.val)(i:Stag N): let P:=field S j M i; let d:=high_d M S i j; IsStarProjection P ∧ P.trace=Aop.trace ∧ Aop*P*Aop=d • Aop∧ minA*(1-P)*minA=d • minA:=by
 intro P d; let v:=angle S i; have hp:tmap v ∈ Next.Free.realCube Next.Free.zone := Next.Free.base_subset_realCube Next.Free.zone_pos (b_base (up_p S g i))
 have hh:=firm_bar j M.val M.property hp; refine ⟨⟨hh.1, hh.2⟩,?_,?_,?_⟩ -- trace
 · unfold P field; rw [bar_n,dateA]
 · rw [show P=field S j M i from rfl,footQ _ g]; rw [BZ.ofReal_action]; rfl
 change (minA*(1-bar j M.val (tmap v)))*minA= _; rw [(bar_side _ _ hp).2]; let Z:=zen (mixL j M.val (tmap v)); rw [show (1-Aop)*(1+Z)=minA+minA*Z from (by rw [mul_add,mul_one]), Matrix.smul_mul,add_mul,show minA*minA=minA from minA_p.1]; let B:=Z; rw [show minA*Z=Z*Aop from zenAA ..,mul_assoc Z Aop, Porth A_id,mul_zero,add_zero,express _ _ _ hp M.property,BZ.ofReal_action]; rfl
namespace Low
variable (h:IsStarProjection Q)(p:0 ≤ d)(e:Aop*Q*Aop=d • Aop)(z:minA*(1-Q)*minA=d • minA)
include z p h e
lemma opposite : warpF*Q*star (warpF)=(1-d) • Aop :=by
 have he:warpF*Q*star warpF=Aop-warpF*(1-Q)*star warpF:=by rw [mul_sub,mul_one,sub_mul,warp_u]; abel
 have hm:minA*star warpF=star warpF:=minA_p.isSelfAdjoint.star_eq ▸ (star_mul warpF minA|>.symm|>.trans (congrArg star warp_t)) -- tune
 rw [he,show warpF*(1-Q)*star warpF = warpF*(minA*(1-Q)*minA)*star warpF by
        rw [mul_assoc _ (_*minA), mul_assoc (minA*(1-Q)), hm,← mul_assoc,← mul_assoc,warp_t],z,Matrix.mul_smul, Matrix.smul_mul,warp_t,warp_u,sub_smul,one_smul]
lemma aster :‖Aop*Q‖≤Real.sqrt d:=by
 have he:Aop*Q*star (Aop*Q)=d • Aop:=by rw [star_mul,Aadj,h.2,←mul_assoc,mul_assoc _ Q Q,h.1,e]
 have hv:‖(Aop*Q)*star (Aop*Q)‖= ‖Aop*Q‖*‖Aop*Q‖:= CStarRing.norm_self_mul_star; rw [he,norm_smul,Real.norm_of_nonneg p] at hv
 nlinarith [mul_le_of_le_one_right p (IsStarProjection.norm_le _ A_id), Real.sq_sqrt p,Real.sqrt_nonneg d,norm_nonneg (Aop*Q)]
-- normalized N=(warpF*P)+ correction
variable {a:ℝ}
lemma serv (u:0<a)(t:Real.sqrt d ≤ a/16)(w:d≤1/8): let X:=a⁻¹ • (Aop*(1+a • warpF)*Q); ‖X‖ ≤ 2 ∧ ‖X*star X+minA-1‖≤1/2:=by
 intro X
 let M:=warpF*Q; let T:=Aop*Q; let F:=a⁻¹ • T; have hz':X=M+F:=by unfold X M F; rw [mul_add,Matrix.mul_smul,mul_one,warp_l,add_mul,Matrix.smul_mul,smul_add,inv_smul_smul₀ u.ne',add_comm]; -- tune
 have hp: ‖M‖≤1:=by apply (norm_mul_le ..).trans; exact le_trans (mul_le_mul warp_norm (IsStarProjection.norm_le _ h) (norm_nonneg _) zero_le_one) (by simp)
 have hg: ‖F‖≤1/16:=by
   unfold F; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_left ((aster h p e z).trans t) (by positivity)); apply le_of_eq; field_simp -- tune right
 have he:‖X‖ ≤ 2:=by rw [hz']; have ht:=norm_add_le M F; linarith
 have hx:X*star X+minA-1= - (d • Aop) + (F*star X+M*star F):=by
   rw [hz',add_mul,add_comm (F*_),star_add,mul_add M,show M*star M=(1-d) • Aop by
        unfold M; rw [star_mul,h.2, ←mul_assoc,mul_assoc _ Q Q,h.1]; exact opposite h p e z, sub_smul,one_smul]; unfold minA; abel
 have ha:‖F*star X‖ ≤ 1/16*2:= (norm_mul_le ..).trans (mul_le_mul hg ((norm_star _).trans_le he) (norm_nonneg _) (by positivity))
 have hv:‖M*star F‖≤1/16:=by apply (norm_mul_le ..).trans; rw [norm_star]; exact (mul_le_mul hp hg (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
 refine ⟨he,?_⟩; rw [hx]; apply (norm_add_le ..).trans; rw [norm_neg,norm_smul,Real.norm_of_nonneg p]; exact (add_le_add (mul_le_of_le_one_right p (IsStarProjection.norm_le _ A_id)) ((norm_add_le ..).trans (add_le_add ha hv))).trans (by linarith)
end Low
end YM.CF.Flare
