import YM.SU5.Reconstruction.Trap.Polar
/-!
# Polar algebra & passing
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K H D S:Hilbert}
-- unitary-without group subtype syntactic overhead
def Pays (P:K.Op) := star P*P=1 ∧ P*star P=1
lemma Pays.units {P:K.Op}(p:Pays P): P∈ unitary K.Op:=p
-- Pos weight concentration. ALL c
noncomputable def Mint (P:K.Op) (c:ℝ): K.Op:= (1-P)+(c:ℂ) • P
namespace Mint
variable (c d:ℝ) {P A:K.Op}(p:IsStarProjection P)
include p
lemma exact_s (z:ℝ): Mint P z*P=(z:ℂ) • P:= by unfold Mint; rw [add_mul,sub_mul,one_mul,Algebra.smul_mul_assoc,p.1.eq,sub_self,zero_add]
omit p
lemma full {f g : K.Op}(h:Commute f g) (c:ℝ): Commute (Mint f c) g:=
    ((Commute.one_left _).sub_left h).add_left (h.smul_left _)
lemma mints {Z:K.Op} : Commute (Mint Z c) Z:= Mint.full (Commute.refl _) _
@[simp] lemma at_base : Mint P 1 = 1:=by simp [Mint]
include p
lemma fuse : Mint P c * Mint P d=Mint P (c*d) := by
 nth_rw 2 [Mint]; rw [mul_add,mul_sub,mul_one,Algebra.mul_smul_comm, exact_s p,smul_smul,mul_comm (d:ℂ)]; unfold Mint; push_cast; abel
lemma star_rate : star (Mint P c) = Mint P c:= by
 unfold Mint; rw [star_add,star_sub,star_smul,star_one,p.2.star_eq]; simp
lemma award (c:ℝ)(h:0≤c): 0≤Mint P c:=by
 have r:Real.sqrt c * Real.sqrt c=c:= Real.mul_self_sqrt h; rw [←r,←fuse _ _ p]; nth_rw 1 [← star_rate _ p]; exact star_mul_self_nonneg _
end Mint
namespace Clasp
variable (C:Clasp K H D)
section
variable {f u : H.Op}{g v : D.Op}{P:H.Op}{Q:D.Op}
local notation "Z" => C.bring P Q
lemma gather_mul (p:C.Pass f g)(q:C.Pass u v): C.bring (f*u) (g*v)=C.bring f g * C.bring u v := by
 ext1 x; apply C.j
 have he (a:H.Op)(b:D.Op)(p:C.Pass a b) (x:K) : C.l (C.bring a b x)=a (C.l x):= DFunLike.congr_fun (C.sustain a b|>.1 p).1 x
 rw [he _ _ (p.times q)]; change f (u (C.l x))= C.l (C.bring f g (C.bring u v x)); rw [he _ _ p, he _ _ q] -- tune
lemma gather_star : star (C.bring f g)=C.bring (star f) (star g):= by
 unfold bring; rw [star_add]; change (C.l.adjoint.comp _).adjoint+ (C.r.adjoint.comp _).adjoint= _
 simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_assoc]; rfl
lemma gather_one : C.bring 1 1=1:= by ext1 x; exact C.calculation _
lemma supplies {f u:H.Op}{g v:D.Op}(p:C.Pass f g)(q:C.Pass u v)(e: Commute f u)(h:Commute g v): Commute (C.bring f g) (C.bring u v):= by rw [commute_iff_eq,←gather_mul C p q,←gather_mul C q p,e.eq,h.eq]
variable (e : C.Pass P Q)
lemma groupProj (p:IsStarProjection P)(q:IsStarProjection Q) (h:C.Pass P Q): IsStarProjection (C.bring P Q):= by
 constructor
 · change _*_= _; rw [← gather_mul C h h,p.1.eq,q.1.eq]
 change star _=_; rw [gather_star,p.2.star_eq,q.2.star_eq]
lemma tie (x:ℝ)(f:IsStarProjection P)(g:IsStarProjection Q)(e:C.Pass P Q) : C.Pass (Mint P x) (Mint Q x):= (C.one.sub e).add (e.scale _)
-- simpler transport of left-right in terminals
lemma packComm {X:H.Op}{R:K.Op}(h:C.l.comp R=X.comp C.l)(p:IsSelfAdjoint X)(q:IsSelfAdjoint R) : Commute C.angle R:= by
 have hp: X.adjoint=X:=p; have he:R.adjoint=R:=q
 have hu:= congrArg ContinuousLinearMap.adjoint h
 rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp, hp,he] at hu; change (C.l.adjoint.comp _).comp R = R.comp (C.l.adjoint.comp _); rw [ContinuousLinearMap.comp_assoc,← ContinuousLinearMap.comp_assoc R,hu,h, ContinuousLinearMap.comp_assoc]
lemma capProj (p:IsStarProjection P)(q:IsStarProjection Q)(h:C.Pass P Q):
  Commute C.angle (C.bring P Q) ∧ C.Left.toContinuousLinearEquiv.toContinuousLinearMap.comp Z=P.comp C.Left.toContinuousLinearEquiv.toContinuousLinearMap ∧
   C.Right.toContinuousLinearEquiv.toContinuousLinearMap.comp Z=Q.comp C.Right.toContinuousLinearEquiv.toContinuousLinearMap:= by
 obtain ⟨a,b⟩:= (C.sustain ..).1 h
 have u:Commute C.angle (C.bring P Q):= C.packComm a p.2 (C.groupProj p q h).2
 have v:Commute (peel C.l) (C.bring P Q) := rootComm u
 have w:Commute (peel C.r) (C.bring P Q):= rootComm (by rw [C.complement]; exact (Commute.one_left Z).sub_left u)
 refine ⟨u,dense_cancel (peel C.l) (peel_dense C.l C.j) ?_,dense_cancel (peel C.r) (peel_dense C.r C.k) ?_⟩
 · ext1 x; change C.Left (Z (peel C.l x))=P (C.Left (peel C.l x))
   rw [show Z (peel C.l x)=peel C.l (Z x) from DFunLike.congr_fun v.eq.symm x,C.left_done,C.left_done]; exact DFunLike.congr_fun a x
 ext1 x; change C.Right (Z (peel C.r x))=Q (C.Right (peel C.r x)); rw [show Z (peel C.r x)=peel C.r (Z x) from DFunLike.congr_fun w.eq.symm x,C.right_done,C.right_done]; exact DFunLike.congr_fun b x
end
section collect
-- one passage; for both observer `U`s, prepare even reverse purchase. No positivity of movers! q price dilation from c chosen independently, requires stamp output.
variable {P:H.Op}{Q:D.Op} {U:H.Op}{V:D.Op}{c:ℝ}
structure ScalePass (P:H.Op)(Q:D.Op)(U:H.Op)(V:D.Op)(c:ℝ):Prop where
 lap:IsStarProjection P
 rap:IsStarProjection Q
 dialog:C.Pass P Q
 pos : 0<c
 leftU:Pays U
 rightU:Pays V
 lc: Commute U P
 rc: Commute V Q
 given:C.Pass U (V*Mint Q c)
 wants:C.Pass (star U) (Mint Q c⁻¹*star V)
local notation "W"=> C.bring U (V*Mint Q c)
variable (h:ScalePass C P Q U V c)
include h
lemma lanes_comm : Commute (C.bring P Q) (C.bring U (V*Mint Q c)) := by
 apply C.supplies h.dialog h.given h.lc.symm; exact h.rc.symm.mul_right (Mint.mints c).symm
lemma routeU : Bijective (C.bring U (V * Mint Q c)) := by
 let M:= C.bring (star U) (Mint Q c⁻¹*star V); have hg: M*W=1:=by
   unfold M; rw [← C.gather_mul h.wants h.given, ←mul_assoc _ _ (Mint Q c), mul_assoc _ (star V),h.rightU.1,h.leftU.1,mul_one,Mint.fuse _ _ h.rap,inv_mul_cancel₀ h.pos.ne',Mint.at_base,C.gather_one]
 have hh: W*M=1:=by
   unfold M; rw [← C.gather_mul h.given h.wants, mul_assoc,← mul_assoc _ (Mint Q c⁻¹),Mint.fuse _ _ h.rap,mul_inv_cancel₀ h.pos.ne',Mint.at_base,one_mul,h.rightU.2,h.leftU.2,C.gather_one]
 exact ⟨LeftInverse.injective (g:= M) (fun x => DFunLike.congr_fun hg x), RightInverse.surjective (g:=M) (f:=W) (fun x => DFunLike.congr_fun hh x)⟩ -- tune
end collect
end Clasp
end YM.CrossedFrame
