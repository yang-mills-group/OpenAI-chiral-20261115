import YM.SU5.Selected.Dais.Lines
import YM.CF.Thera.Hang
/-! Lettuce PF occupation-number tilt for use in Kepx. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dais.Parity
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Thera
open Pannier.Chancel (Letter Marque)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ContDiff InnerProductSpace ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I][Nonempty I]{P B K Q:Op I}{F:FC I}{g r t e u:ℝ}
def cards (P:Op I)(t:ℝ): Op I:= P+t • (1-P)
lemma pal_r (a:ℝ)(p:IsStarProjection P): IsSelfAdjoint (cards P a):=p.isSelfAdjoint.add (IsSelfAdjoint.smul (star_trivial a) p.one_sub.isSelfAdjoint) -- order
lemma card_spend (p:IsStarProjection P)(a b:ℝ):cards P a*cards P b= cards P (a*b):=by
 have hP:P*P=P:=p.isIdempotentElem; have hp:(1-P)*(1-P)=1-P:=p.one_sub.isIdempotentElem
 unfold cards; simp only [_root_.mul_add,_root_.add_mul,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,hP,hp,smul_smul,_root_.mul_comm a b]; rw [mul_sub,_root_.mul_one,hP,sub_self,sub_mul,_root_.one_mul,hP,sub_self,smul_zero,_root_.add_zero,_root_.zero_add,smul_smul] -- ambiguity
@[simp] lemma simple (P:Op I): cards P 1=1:=by unfold cards; rw [one_smul]; abel
lemma card_twist (t:ℝ)(P:Op I)(U:UNI I): twist U (cards P t)=cards (twist U P) t:=by
 unfold cards; rw [map_add,map_smul, map_sub,map_one] -- name
-- grip determinant operator: signed orientation supply not assumed.
def grip (P Q:Op I)(t:ℝ):= P* cards Q (t^2)*P+(1-P)
lemma grip_twist (t:ℝ)(P Q:Op I)(U:UNI I): twist U (grip P Q t)=grip (twist U P) (twist U Q) t:=by simp only [grip,card_twist,map_add,map_sub,map_one,map_mul]
lemma price_wave (a:ℝ)(p:IsStarProjection P)(g:IsStarProjection Q)(x:Wave I)(h:Sea P x):
 ‖acts (quant (cards Q a)) x‖^2=(grip P Q a).det.re:=by
 let U:= cards Q a; have hp:star U*U=cards Q (a^2):= by rw [pal_r a g,sq,card_spend g a a] -- tune IsSelfAdj star_eq
 let v:= acts (quant U) x; have hx:(grip P Q a).det= inner ℂ v v:=by
    unfold grip; rw [←meadow p x h,←hp]; unfold skyGlow v; rw [quant_mul,quant_star,act_mul, ←act_inner (star (quant U)),star_star] -- direction
 rw [hx,inner_self_eq_norm_sq_to_K]; change _=((‖v‖:ℂ)^2).re; rw [←Complex.ofReal_pow,Complex.ofReal_re]
lemma grip_base (p:IsStarProjection P)(g:IsStarProjection Q)(s:0≤t)(u:t≤1): t^2 • (1:Op I) ≤ grip P Q t :=by
 let c₀:=(1-t^2); have hv:0≤c₀:= by unfold c₀; nlinarith
 let X:=P*Q*P+(1-P); have h0:0 ≤ X:=by apply add_nonneg _ p.one_sub.nonneg; have ht:= star_left_conjugate_nonneg g.nonneg P; rw [p.isSelfAdjoint] at ht; exact ht
                                                     -- P*Q*star P vs etc
 have hp : grip P Q t= t^2 • (1:Op I)+c₀ • X:=by
   have hp:P*P=P:=p.isIdempotentElem; unfold grip cards X c₀; simp only [Matrix.mul_add,Matrix.mul_sub,smul_add,smul_sub,sub_smul,Matrix.add_mul,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,_root_.mul_one,_root_.one_mul,one_smul,hp]; abel
 rw [hp]; exact le_add_of_nonneg_right (smul_nonneg hv h0)
lemma grip_lives (p:IsStarProjection P)(g:IsStarProjection Q)(s:0<t)(u:t≤1): (grip P Q t).PosDef:= renovate (pow_pos s _) (grip_base p g s.le u)
lemma grip_mono {X:Op I}(p:IsStarProjection P)(s:0 ≤ t)(u:t≤1)(e':0≤e)(U:Op I)(v: Commute P U)(w:‖(Q-X)*U‖≤e): ‖(grip P Q t-grip P X t)*U‖ ≤ e:=by
 have he(a:Op I): ‖P*a‖ ≤ ‖a‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
 have hh(a:Op I): ‖a*P‖≤‖a‖:=(norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (p.norm_le _))
 let c:=1-t^2; have hc:0≤c:=by unfold c; nlinarith; -- syntaxes
 rw [show (grip P Q t-grip P X t)*U=c • (P*((Q-X)*U)*P) from ?_ ,norm_smul,Real.norm_of_nonneg hc]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self 1 (sq_nonneg t))); exact (hh _).trans ((he _).trans w)
 unfold grip cards; rw [add_sub_add_right_eq_sub,←sub_mul,←mul_sub, show Q+_ - (X+_)= c • (Q-X) from ?_]; swap; · unfold c; module
 simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc,v.eq]
end YM.CF.Dais.Parity
#print axioms YM.CF.Dais.Parity.grip_lives
#print axioms YM.CF.Dais.Parity.price_wave
