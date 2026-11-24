import YM.CF.Fock.Complement
import YM.CF.Fock.Track

/-! Trace representation of unnormalized volume sizes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]

def shrinkV (P C : Op n) := body P C * star (body P C)+(1-P)
def netsal (P C : Op n) := (invoice (shrinkV P C-1)).re/4
lemma sat_cut (s : Finset n) (C : Op n) : shrinkV (cutM s) C=padded s C*star (padded s C) := by
  unfold shrinkV body padded; rw [cut_real]
  let P := cutM s; let Q := 1-P; let A := P*C*P
  have h := cutM_idp s; have he : IsStarProjection Q := h.one_sub
  have hQ : star Q=Q := he.isSelfAdjoint; have hP : P*Q=0 := Porth h
  have hb : A*Q=0 := by unfold A; rw [mul_assoc,hP,mul_zero]
  -- is A*Q cross? star: (A+Q)*(star A+Q), yes.
  have hv : Q*star A=0 := by nth_rw 1 [←hQ]; rw [←star_mul,hb,star_zero]
  change A*star A+Q=(A+Q)*star (A+Q); rw [star_add,hQ,mul_add, add_mul,add_mul, hb,hv,he.isIdempotentElem,zero_add,add_zero]
lemma sat_turn (U : UNI n) (P C : Op n) : shrinkV (twist U P) (congrC U C)=twist U (shrinkV P C) := by
  rw [shrinkV,shrinkV,map_add,map_sub,map_one,board_twist,congr_form, twist_formula U (body P C*star (body P C)), star_mul,star_star,star_mul]; congr 1
  simp only [←mul_assoc]; rw [mul_assoc (U.val*body P C),show star _*(ccU U).val=1 from (ccU U).property.1,mul_one]
lemma determinant_filled {P : Op n} (h : IsStarProjection P) {C : Op n} (g : Cᵀ= -C) :
    ‖(shrinkV P C).det‖=‖filled P C‖^4 := by
  obtain ⟨U,s,rfl⟩ := spot_projection P h
  let Q := cutM s; let V := star U; let A := congrC V C
  rw [←det_twist V,←sat_turn]; rw [show twist V (twist U Q)=Q from twist_inv ..]
  rw [sat_cut,Matrix.det_mul, placed, norm_smul,stratum_pf,wedge_norm,mul_one]
  simp only [norm_mul, Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose,norm_star]
  change _=‖pf A s‖^4; rw [←principal A, ←pf_square s A (skew_form g),norm_pow]; ring
variable [Nonempty n]
lemma sat_gap {P : Op n} (h : IsStarProjection P) (U : UNI n) (e : ‖stage P U.val-U.val‖ ≤ 1/3) : ‖shrinkV P U.val-1‖ ≤ 7/9 := by
  let S := stage P U.val
  have hS : body P U.val=P*S := (stage_left h _).symm
  have hk : star P=P := h.isSelfAdjoint
  have ht : shrinkV P U.val-1=P*(S*star S-1)*P := by
    rw [shrinkV,hS,star_mul,hk,mul_sub,mul_one,sub_mul,h.isIdempotentElem]; simp only [mul_assoc]; abel
  rw [ht]; have hs : ‖P‖≤1 := h.norm_le _
  have hb : ‖S‖ ≤ 1/3+1 := (norm_le_norm_sub_add S U.val).trans (add_le_add e (by rw [CStarRing.norm_of_mem_unitary U.property]))
  have H : ‖S*star S-1‖ ≤ 7/9 := by
    have he : ‖star S-star U.val‖ ≤ 1/3 := by rw [←star_sub,norm_star]; exact e
    rw [←show U.val*star U.val=1 from U.property.2,show S*star S-U.val*star U.val=S*(star S-star U.val)+(S-U.val)*star U.val by rw [mul_sub,sub_mul]; abel]
    apply (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul hb he (norm_nonneg _) ((norm_nonneg S).trans hb))) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right e (norm_nonneg (star U.val))))).trans ?_)
    rw [norm_star,CStarRing.norm_of_mem_unitary U.property]; norm_num
  apply (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans (mul_le_mul hs H (norm_nonneg _) zero_le_one)) hs (norm_nonneg _) (by positivity)).trans ?_); rw [one_mul,mul_one]
lemma to_sal {P C : Op n} (h : IsStarProjection P) (g : Cᵀ= -C) (e : ‖shrinkV P C-1‖ < 1) :
    Real.exp (netsal P C)=‖filled P C‖ := by
  unfold netsal; let r := invoice (shrinkV P C-1); apply pow_left_inj₀ (Real.exp_pos _).le (norm_nonneg _) (show 4≠0 by decide) |>.mp
  rw [←Real.exp_nat_mul]; push_cast
  change Real.exp (4*(r.re/4))=_; rw [show 4*(r.re/4)=r.re by ring, ←Complex.norm_exp]
  unfold r; rw [factor _ e,add_sub_cancel]; exact determinant_filled h g
end YM.CF.Fock
