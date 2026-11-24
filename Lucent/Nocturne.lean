import Lucent.Cadence
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Pannier.Chancel Rous Pressure
open Peaks Scree
open RG Buffered.Afterglow
open Lamour Lamour.Bridge
open Morn Journey
variable {P:Preparation}{I J:Type}

open Stencil
def dawn (S:Stencil I):Stencil I:=castDown (castDown S)
def dusk (S:Stencil I):Stencil I:=castDown (dawn S)
def night (S:Stencil I):Stencil (I⊕I):=remake Sum.inl (dusk S)*remake Sum.inr (dawn S)
abbrev forwardS (W:I→Staff)(z:ℤ):I→Staff:=rods z (rods 0 W)
abbrev otherS (W:I→Staff)(z:ℤ):I→Staff:=rods 0 (forwardS W z)
def replayS (W:I→Staff)(z:ℤ): (I⊕I)→Staff:=Sum.elim (otherS W z) (forwardS W z)
variable {W:I→Staff}{S:Stencil I}{m a b l:ℕ} {B:ℝ}
lemma dawnPay (h:S.degree m a): (dawn S).degree m a:=castGrade (castGrade h)
lemma duskPay (h:S.degree m a): (dusk S).degree m a:=castGrade (dawnPay h)
lemma nightPay (h:S.degree m a): (night S).degree (m+m) (a+a):=((duskPay h).remake _).mul ((dawnPay h).remake _)
variable (z:ℤ)
lemma dawnSong (h:Singing W S):Singing (forwardS W z) (dawn S):= singingCast _ _ _ (singingCast _ _ _ h)
lemma duskSong (h:Singing W S):Singing (otherS W z) (dusk S):=singingCast _ _ _ (dawnSong _ h)
lemma nightSong (h:Singing W S):Singing (replayS W z) (night S):= Singing.both _ (singingRemake _ _ _ (duskSong z h)) (singingRemake _ _ _ (dawnSong z h))

lemma dawnCost (h:Squad B W b l):Squad (B+2*|↑z|) (forwardS W z) b l:=((h.rods 0).rods z).mono (by simp)
lemma duskCost (h:Squad B W b l): Squad (B+2*|↑z|) (otherS W z) b l:= ((dawnCost z h).rods 0).mono (by simp)
lemma nightCost(h:Squad B W b l): Squad (B+2*|↑z|) (replayS W z) b l:= (duskCost z h).union (dawnCost z h)

variable (S) (v t R:ℝ)(b m a:ℕ)
lemma fluent_charge (F:Papal.Weaver) (r:ℂ): fluent 3 z (r • F)=star r • fluent 3 z F:=funext fun n=> funext fun _ => theta_smul .. -- tune
lemma maxStar : star (maxZoom R m a)= maxZoom R m a:= by unfold maxZoom; rw [star_mul',star_pow,star_pow,star_pow,star_div₀,star_pow]; norm_num
lemma dawnMove (h:dayStars W): traction 3 z (qr W v R t S m a b) = qr (forwardS W z) v R t (dawn S) m a b:=by
 unfold qr traction; rw [fluent_charge,fluent_charge,star_star,cast_wide _ _ _ _ _ _ h,cast_wide z (rods 0 W) _ _ _ _ (show dayStars (rods 0 W) from h)]; try rfl
lemma duskMove (h:dayStars W): fluent 3 0 (traction 3 z (qr W v R t S m a b))=qr (otherS W z) v R t (dusk S) m a b:=by
 rw [dawnMove _ _ _ _ _ _ _ _ h, qr, fluent_charge,maxStar, cast_wide _ (forwardS W z) _ _ _ _ h]; rfl

lemma maxM (R:ℝ)(m m' a d:ℕ):maxZoom R (m+m') (a+d) = maxZoom R m a * maxZoom R m' d:=by unfold maxZoom; rw [pow_add,pow_add]; ring
lemma qr_mul (S T:Stencil I)(d g:ℕ) :
    qr W v R t (S*T) (m+d) (a+g) b =qr W v R t S m a b * qr W v R t T d g b:= by rw [qr, qr, qr,maxM, kite_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_smul]
lemma nightMove (B:Side)(u:ℕ)(h:dayStars W):
    father B 3 (qr W v R t S m a b) u= qr (replayS W (Heat.gaugeShift B u)) v R t (night S) (m+m) (a+a) b:=by
 unfold father takeoff; rw [duskMove _ _ _ _ _ _ _ _ h,dawnMove _ _ _ _ _ _ _ _ h,night,qr_mul]; unfold qr; rw [kite_readdress,kite_readdress]; try rfl
