import YM.CF.Sault.Mural
import YM.CF.Hest.Boat
import YM.CF.Scree.Locus
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- general dΓ form
lemma urn_stop (f:n→FC (LeanV n))(b:Bool)(P:Op n): acts (urn f (trailM b) P) (vacuum _)=0:=by unfold urn; rw [act_sum]; apply sum_eq_zero; intro i _; rw [act_sum]; apply sum_eq_zero; intro j _; rw [act_smul,act_mul,trailM,← remove_take,vacuum_take,map_zero,smul_zero]
lemma air (F A B C R:Op n): acts (forge F A B C R) (vacuum _)=acts (faceD true false A+Matrix.trace F • 1) (vacuum _):=by unfold forge; rw [act_add,act_add,act_add,act_sub,urn_stop,urn_stop,urn_stop,add_zero,sub_zero,add_zero,act_add]
variable {P:Op n}
lemma loft_v (A:Op n)(t:Commute P A)(p:IsStarProjection P)(x:Wave n)(s:Sea P x) : acts (dg A) x=Matrix.trace (P*A) • x:=by
 let v:=nursery P p; let q:=vacuum (LeanV n)
 have he:Kennel.capT P A=0:=by unfold Kennel.capT; rw [mul_assoc, ←t.eq, ←mul_assoc,sub_mul,one_mul,p.isIdempotentElem.eq,sub_self,zero_mul]
 have hu:dg (0:Op n)=0:=by unfold dg dyad; simp
 have ht:v.eval (faceD true false A)=0:=by change v.cook (Hest.boat _) = _; rw [show v.cook _=_ from Hest.birth ..,he,hu]
 nth_rw 1 [←runL (nursery P p) x]; rw [←loft p _ _ s, air, loaf, map_add, map_smul, Poly.eval_one, ht, zero_add,act_smul,act_one]
lemma vert(A:FC n)(z:ℂ):exp (z • 1+A)=Complex.exp z • exp A:=by
  letI : NormedAlgebra ℚ (FC n):= NormedAlgebra.restrictScalars ℚ ℂ (FC n)
  let f : ℂ→+* FC n:= algebraMap ℂ _
  have he t : f t=t • 1 := Algebra.algebraMap_eq_smul_one _
  have hp : Continuous f := by apply continuous_iff_continuousAt.mpr; intro x; have H : (f:ℂ→FC n)=fun x=>x • 1 := funext he; rw [H]; exact continuousAt_id.smul continuousAt_const
  rw [exp_add_of_commute ((Commute.one_left A).smul_left z), ←he, ←map_exp f hp, he,Algebra.smul_mul_assoc,one_mul,Complex.exp_eq_exp_ℂ]
lemma mast_v(A:Op n)(t: Commute P A)(p:IsStarProjection P)(s: IsSelfAdjoint A)(x: Wave n)(w:Sea P x):skyGlow x (exp A) x=Complex.exp (Matrix.trace (P*A)):=by
 let T:=dg A; let z:=Matrix.trace (P*A); let C:= T-z • 1; have he:(acts C) x=0:=by unfold C; rw [act_sub,act_smul,act_one,loft_v A t p x w,sub_self]
 unfold skyGlow; rw [← dg_exp s,show exp (dg A)= _ from (show exp (dg A)=Complex.exp z • exp C by conv_lhs=>rw [show dg A=z • 1+C by unfold C T; abel,vert]),act_smul,pier he,inner_smul_right,inner_self_eq_norm_sq_to_K,w.2]; simp; rfl -- tune
open Thera Tap Dial
variable {N:Side}
lemma bet(U:Op Slot)(v:Scree.Phys N)(p:star U=U): let A:= -(plankP N U); scaleZ U v=acts (exp (dg A-Matrix.trace (tickA N * A) • 1)) v:=by
 intro A; let C:=tickA N; have ht:IsStarProjection C:=by unfold C; rw [touchP]; exact cutM_idp _
 have hu:IsSelfAdjoint A:= by change star A=A; unfold A; rw [star_neg, plank_h p] -- tune
 let z:=Matrix.trace (C*A); let x:=mateK N
 unfold scaleZ; change (skyGlow x (exp A) x)⁻¹ • _= _; rw [mast_v A ((plank_tick U).neg_right) ht hu x (tickB N), ←dg_exp hu,show dg A-z • 1= -z • 1+dg A from (by rw [neg_smul,sub_eq_add_neg,add_comm]),vert,act_smul,Complex.exp_neg] -- tune
-- balanced scalar local.Sym viable.
abbrev rise (P K:Op n):= (2:ℂ)⁻¹ • (P*K+K*P-K)
abbrev tally (P Q K U:Op n):=rise P K-rise Q U
lemma lease (A C:Op n)(i: IsStarProjection P)(h:TagG P A)(x:Wave n)(s:Sea P x)(F:Wave (LeanV n))(Q:Op n):let K:=(1-A)*Q*(1+A); let T:=nursery P i; let y:= acts (exp (dg A)) x; let L:=ballL T y; let U:=C*Q
 L (acts (forge (tally P C K Q) K (K*(1-P)) (P*K) (P*K*(1-P))) F)=acts (dg Q-Matrix.trace U • 1) (L F):=by
 intro K T y L U; rw [show forge _ _ _ _ _=forge (P*K-U) K (K*(1-P)) (P*K) (P*K*(1-P)) from ?_]; exact plume i A C h x s F Q -- explicit
 have he:K.trace=Q.trace:=by unfold K; rw [Matrix.trace_mul_comm, ←mul_assoc,mul_eq_one_comm.mp h.mud,one_mul]
 have hu:Matrix.trace (tally P C K Q)= Matrix.trace (P*K-U):=by unfold tally rise U; simp only [Matrix.trace_sub,Matrix.trace_add, Matrix.trace_smul, Matrix.trace_mul_comm K P,Matrix.trace_mul_comm Q C, he, smul_eq_mul]; ring
 unfold forge; rw [hu]
end YM.CF.Sault
