import YM.CF.BProof.Bias.Tide
/-! Discrete nonzero fiber graph at each q. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side} (j:ℕ)(M:Male)(h:1≤j)(x:Site N)
abbrev hat(x:Site N):= Jill.disk j M (pm x)
abbrev red (j:ℕ)(M:Male)(x:Site N):= Fir.bar j M.val (mel x)
abbrev sky := Fir.Aop
lemma sky_h : IsStarProjection sky:=⟨AOne,Aadj⟩
lemma sky_pos : sky≠0 := by unfold sky; rw [← pill_plus]; intro h; have ht:= Matrix.ext_iff.mpr h 0 0; simp [pill,spHalf,cutM,plusHalf] at ht
lemma sprojNorm{I:Type}[Fintype I][DecidableEq I][Nonempty I]{A:Op I}(h:IsStarProjection A)(g:A≠0): ‖A‖=1:=by
 have h1:= norm_pos_iff.mpr g; have h2:= norm_mul_le A A; rw [h.isIdempotentElem.eq] at h2; have h3:‖A‖≤1:=h.norm_le A; nlinarith
lemma red_h : IsStarProjection (red j M x) := by have h:= firm_bar j M.val M.property (base_zone (mel_h x)); exact ⟨h.1,h.2⟩
include h in
lemma hat_p : 0 < hat j M x:=by obtain ⟨c,C,e,-,k⟩:=feed h; exact (mul_pos e (pow_pos (norm_pos_iff.mpr (pm_nonzero x)) _)).trans_le (k x M).2.2
lemma red_y : sky*red j M x * sky = hat j M x • sky := by unfold sky; rw [←pill_plus]; exact lowFull M (pm x) (mel_h x) true
lemma red_o : (1-sky)*(1-red j M x) *(1-sky)= hat j M x • (1-sky):=by change (1-Aop) * _ * (1-Aop)=_; rw [← pill_minus]; exact lowFull M (pm x) (mel_h x) false
lemma hat_e : hat j M x ≤ 1:=by
 let A:=red j M x; let d:=hat j M x; have ht: ‖sky*A*sky‖ ≤1:= calc
    _ ≤ ‖sky‖*‖A‖ *‖sky‖:= le_trans (norm_mul_le ..) (mul_le_mul_of_nonneg_right (norm_mul_le ..) (norm_nonneg _))
    _ ≤ 1:= by rw [sprojNorm sky_h sky_pos,one_mul,mul_one]; exact (red_h ..).norm_le _
 rw [show sky*A*sky =d • sky from red_y ..,norm_smul, Real.norm_of_nonneg (show 0≤d from norm_nonneg _),sprojNorm sky_h sky_pos,mul_one] at ht; exact ht
def zag(x:Site N): Op SpinIdx:=let d:=hat j M x; d⁻¹ • ((1-sky)*red j M x*sky)
lemma zag_yes : zag j M x*sky=zag j M x:=by unfold zag; rw [Algebra.smul_mul_assoc,mul_assoc,sky_h.isIdempotentElem]
lemma sky_comp : sky*(1-sky)=0:= by rw [mul_sub,mul_one,sky_h.1.eq,sub_self]
lemma zag_off : sky*zag j M x=0:=by unfold zag; rw [Algebra.mul_smul_comm,←mul_assoc,←mul_assoc,sky_comp]; simp
include h
lemma zag_at : zag j M x*red j M x=(1-sky)*red j M x := by
 let S:= red j M x; let B:=sky; let Y:=1-sky; let d:=hat j M x; have he:0 <d:= hat_p j M h x
 have ht:Y*S*Y=(1-d) • Y := by
    have hl:Y*(1-S)*Y=d • Y:=red_o ..; rw [mul_sub Y 1 S,mul_one Y,sub_mul Y (Y*S) Y,sky_h.one_sub.isIdempotentElem.eq] at hl; rw [sub_smul,one_smul,←hl,sub_sub_cancel] -- tune
 have hv:B*S+Y*S=S:=by unfold B Y; noncomm_ring
 have hs: (Y*S*B)*S=d • (Y*S):= by
    have hx:Y*S*B*S+Y*S*Y*S=Y*S:=by rw [mul_assoc (Y*S),mul_assoc (Y*S) Y S, ← mul_add,hv,mul_assoc,(red_h ..).isIdempotentElem]
    rw [ht,Algebra.smul_mul_assoc,sub_smul,one_smul] at hx; rw [eq_sub_of_add_eq hx]; abel
 change d⁻¹ • _ * S=Y*S; rw [Algebra.smul_mul_assoc,hs,inv_smul_smul₀ he.ne']
lemma zag_col : sky+zag j M x=(hat j M x)⁻¹ • (red j M x*sky):=by
 let Z:= (1-sky)*red j M x; let A:=red j M x; let d:=hat j M x; have he:A*sky= Z*sky+ d • sky := by rw [← show sky*A*sky=d • sky from red_y ..]; unfold Z A; noncomm_ring
 change sky+d⁻¹ • (Z*sky)=d⁻¹ • (A*sky); rw [he,smul_add,inv_smul_smul₀ (hat_p j M h x).ne',add_comm]
lemma zag_ready : red j M x*(sky+zag j M x)=sky+zag j M x:=by rw [zag_col j M h x,Algebra.mul_smul_comm,←mul_assoc,(red_h ..).isIdempotentElem]
lemma zag_recur : zag j M x= (1-sky)*red j M x*sky+zag j M x*(sky-sky*red j M x*sky):= by
 rw [mul_sub,zag_yes,←mul_assoc,← mul_assoc,zag_yes,zag_at j M h x]; abel
lemma zag_gram : star (zag j M x)*zag j M x=((hat j M x)⁻¹-1) • sky :=by
 -- use graph column norm
 let d:=hat j M x; let Q:=sky; let Z:= zag j M x; let A:=red j M x; have he: d≠0:=(hat_p j M h x).ne'; have ht : star (Q+Z)*(Q+Z) =d⁻¹ • Q := calc
    _ = star (d⁻¹ • (A*Q))*(d⁻¹ • (A*Q)) := by rw [show Q+Z =d⁻¹ • (A*Q) from zag_col j M h x]
    _ = _:=by rw [star_smul,star_trivial,star_mul,sky_h.isSelfAdjoint,(red_h ..).isSelfAdjoint,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,←mul_assoc,mul_assoc _ A A,(red_h ..).1.eq,show Q*A*Q =d • Q from red_y ..,inv_smul_smul₀ he]
 have hu:star Z*Q=0:=by nth_rw 1 [←show star Q=Q from sky_h.isSelfAdjoint]; rw [←star_mul,show Q*Z=0 from zag_off ..,star_zero]
 change star Z * Z= _; rw [star_add,sky_h.isSelfAdjoint, add_mul,mul_add,mul_add, hu,zero_add, show Q*Z=0 from zag_off ..,add_zero,sky_h.1.eq] at ht; rw [sub_smul,one_smul]; exact eq_sub_of_add_eq (by rwa [add_comm]) -- tune
lemma zag_norm : ‖zag j M x‖^2=(hat j M x)⁻¹-1 :=by
 rw [pow_two,←CStarRing.norm_star_mul_self,zag_gram j M h x,norm_smul,sprojNorm sky_h sky_pos,mul_one,Real.norm_of_nonneg (sub_nonneg.mpr (one_le_inv₀ (hat_p j M h x) |>.2 (hat_e ..)))]
end YM.CF.BProof.Bias
