import ForceSatin.HomeTilt
import YM.CF.Sault.Gilt
import YM.CF.Sedge.Aurum
import YM.CF.Flare.Wits
/-! In the Ward/checker computation, keep exact excitation-number cost on the
`Single` Fock spaces, not a momentum-window positivity assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Matrix Thera Verses
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {I : Type} [LinearOrder I] [Fintype I]

/-- Classify as in HomeTilt. `particles (1-P)` and `holes P`.
 Keep `excitation` number cost in *forms*, so can pay even for a full Bessel family of annihilators. -/
def particles (P : Op I)(x : Wave I) := (inner ℂ x (acts (dg P) x)).re
def holes (P : Op I)(x : Wave I) := rankPrice P * ‖x‖^2 - particles P x

def active (P : Op I)(x : Wave I) := (inner ℂ x (acts (excitation P) x)).re

lemma active_split (P : Op I)(x : Wave I) : active P x = particles (1-P) x + holes P x := by
  unfold active excitation tiltSymbol holes particles
  rw [sub_eq_add_neg (1-P), dg_add, dg_neg,act_add,act_add,act_neg, acts_scalar,act_one]
  rw [inner_add_right,inner_add_right,inner_neg_right,←Complex.coe_smul,inner_smul_right]
  simp only [Complex.add_re, Complex.neg_re,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero]
  change _*(RCLike.re (K:=ℂ) (inner ℂ x x))+_= _
  rw [inner_self_eq_norm_sq]; ring

lemma particles_basis (A : Op I) (x : Wave I) :
    particles (A*star A) x = ∑ i:I, ‖acts (Fock.remove (acts A (basisKet i))) x‖^2 := by
  unfold particles; rw [prizeUV,act_sum,inner_sum,Complex.re_sum]
  apply sum_congr rfl; intro i _; rw [act_mul,←act_inner]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _

lemma holes_basis (A : Op I) (x : Wave I) : holes (A * star A) x = ∑ i:I, ‖acts (create (acts A (basisKet i))) x‖^2 := by
  have he : rankPrice (A * star A)= ∑ i:I, ‖acts A (basisKet i)‖^2 := by
    unfold rankPrice; rw [Matrix.trace_mul_comm,Matrix.trace,Complex.re_sum]; apply sum_congr rfl; intro i _; unfold Matrix.diag; rw [←basis_act (star A*A) i i,←basis_inner,act_mul, ←act_inner,star_star]; exact inner_self_eq_norm_sq (𝕜:=ℂ) _
  unfold holes; rw [he,particles_basis,Finset.sum_mul]; apply sub_eq_of_eq_add; rw [←Finset.sum_add_distrib]; exact sum_congr rfl (fun i _=> (Flare.snow _ x).symm)

lemma particles_sum (P A:Op I)(x : Wave I):particles (P+A) x=particles P x+particles A x:= by rw [particles,dg_add, act_add,inner_add_right]; rfl
lemma holes_sum (P A:Op I)(x : Wave I):holes (P+A) x=holes P x+holes A x:=by
  unfold holes rankPrice; rw [particles_sum,Matrix.trace_add,Complex.add_re]; ring
lemma particles_scale (c:ℝ)(P:Op I)(x:Wave I): particles (c • P) x=c*particles P x:=by
  unfold particles; rw [dg_scale, acts_scalar,←Complex.coe_smul,inner_smul_right]; simp
lemma holes_scale (c:ℝ)(P:Op I)(x:Wave I): holes (c • P) x=c*holes P x:=by
  unfold holes rankPrice; rw [particles_scale,Matrix.trace_smul,Complex.real_smul,Complex.mul_re]; simp; ring

lemma particles_pays (P:Op I)(x : Wave I) (h : 0 ≤ P) : 0≤particles P x := by
  obtain ⟨W,s⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  rw [s]; nth_rw 2 [←star_star W]; rw [particles_basis]
  exact sum_nonneg (fun i _=>sq_nonneg _)
lemma holes_pays (P:Op I)(x : Wave I) (h : 0 ≤ P) : 0≤holes P x:=by
  obtain ⟨W,s⟩:= CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  rw [s]; nth_rw 2 [←star_star W]; rw [holes_basis]; exact sum_nonneg (fun i _=>sq_nonneg _)
lemma particles_order {P B : Op I} (h:P ≤ B) (x : Wave I) : particles P x ≤ particles B x := by
  rw [show B=P+(B-P) from (add_sub_cancel ..).symm, particles_sum]; exact le_add_of_nonneg_right (particles_pays _ _ (sub_nonneg.mpr h))
lemma holes_order {P B : Op I} (h:P ≤ B) (x : Wave I) : holes P x ≤ holes B x := by
  rw [show B=P+(B-P) from (add_sub_cancel ..).symm, holes_sum]; exact le_add_of_nonneg_right (holes_pays _ _ (sub_nonneg.mpr h))

variable {P : Op I}(p : IsStarProjection P)
include p
lemma active_pay (x : Wave I) : 0 ≤ active P x := by rw [active_split]; exact add_nonneg (particles_pays _ _ p.one_sub.nonneg) (holes_pays _ _ p.nonneg)

lemma excitation_kills {q:Wave I}(t:Sea P q) : acts (excitation P) q=0 := by
  have hP:P*tiltSymbol P = -P:=by unfold tiltSymbol; rw [mul_sub,mul_sub,mul_one,p.isIdempotentElem.eq,sub_self,zero_sub]
  have he:Commute P (tiltSymbol P):= ((Commute.one_right _).sub_right (Commute.refl _)).sub_right (Commute.refl _)
  have hv:(rankPrice P : ℂ)= Matrix.trace P:=by
    obtain ⟨U,s,H⟩:=spot_projection P p
    rw [rankPrice,H,trace_twist,trace_cut]; simp
  rw [excitation,act_add,acts_scalar,act_one,Sault.loft_v _ he p q t,hP,Matrix.trace_neg,←Complex.coe_smul,hv,neg_smul,add_neg_cancel]

lemma grow_flat {q:Wave I}(t:Sea P q)(r:ℝ) : acts (grow (excitation P) r) q=q:=
  pier (by rw [acts_scalar,excitation_kills p t,smul_zero] : acts (r • excitation P) q=0)

lemma glow_flat_price (F:FC I) {q:Wave I}(t:Sea P q)(r:ℝ) :
    inner ℂ q (acts ((tilt P r).glow F) q) = inner ℂ q (acts F q) := by
  set V:=grow (excitation P) r
  let T:= tilt P r
  have h : V*F = T.glow F * V := by
    rw [show V=Real.exp (r*rankPrice P) • quant T.sell from tilt_quant_exp p r, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    apply congrArg; unfold Shaft.glow; rw [mul_assoc (quant T.sell*F), ←quant_mul,T.pay,quant_one,mul_one]
  have hv:IsSelfAdjoint V:=by
    unfold IsSelfAdjoint V grow; rw [star_exp,star_smul,star_trivial,(excitation_real p).star_eq]
  have hk:= show acts V q=q from grow_flat p t r
  change inner ℂ q (acts (T.glow F) q)=_
  nth_rw 2 [←hk]; rw [←act_mul,←h,act_mul,←act_inner,hv.star_eq,hk]

variable [Nonempty I]
lemma gram_order_left {K : Op I} {B:ℝ}(t:‖K‖ ≤ B) : P*K*star (P*K) ≤ B^2 • P:=by
  calc
    _=P*(K*star K)*star P:=by rw [star_mul,mul_assoc,mul_assoc,mul_assoc]
    _ ≤ P*(B^2 • (1:Op I))*star P:=by
      apply Dial.seal_up
      apply (op_le_norm_one (show IsSelfAdjoint (K*star K) from by unfold IsSelfAdjoint; rw [star_mul,star_star])).trans (smul_le_smul_of_nonneg_right _ zero_le_one)
      rw [pow_two]; exact (norm_mul_le ..).trans (mul_le_mul t ((norm_star _).le.trans t) (norm_nonneg _) ((norm_nonneg _).trans t))
    _= _:=by rw [Algebra.mul_smul_comm,mul_one,Algebra.smul_mul_assoc,p.isSelfAdjoint,p.isIdempotentElem.eq]

lemma bessel_particle {K : Op I} {B:ℝ}(t:‖K‖≤B)(x:Wave I) :
    ∑ i:I, ‖acts (Fock.remove (acts (1-P) (acts K (basisKet i)))) x‖^2 ≤ B^2 * active P x := by
  simp_rw [←act_mul (1-P)]; rw [←particles_basis]
  apply le_trans (particles_order (gram_order_left p.one_sub t) _); rw [particles_scale,active_split]
  gcongr; exact le_add_of_nonneg_right (holes_pays _ _ p.nonneg)
lemma bessel_hole {K : Op I} {B:ℝ}(t:‖K‖≤B)(x:Wave I) :
    ∑ i:I, ‖acts (create (acts P (acts K (basisKet i)))) x‖^2 ≤ B^2 * active P x := by
  simp_rw [←act_mul P]; rw [←holes_basis]
  apply le_trans (holes_order (gram_order_left p t) _); rw [holes_scale,active_split]
  gcongr; exact le_add_of_nonneg_left (particles_pays _ _ p.one_sub.nonneg)

end YM.CF.Papyrus.Franc.SatinForce
