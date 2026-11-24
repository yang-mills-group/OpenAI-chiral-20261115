import YM.SU5.Reconstruction.Crease.Turns
import YM.SU5.Reconstruction.Anvil.Display
/-! # Net preparations billed via points on the chosen (not just canonical) Mink axis. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap OS Semigroup Picket Anvil
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)
local notation "U"=> trans S
@[simp] lemma mail (p:E4): U p * U (-p)=1:= by rw [← trans_sum,add_neg_cancel]; exact S.unit.origin
@[simp] lemma mail_inv (p:E4): U (-p)* U p= 1:= by rw [← trans_sum,neg_add_cancel]; exact S.unit.origin
noncomputable def parcelUp (p:E4)(A:H.Op): H.Op:= U p * A * U (-p)
local notation "ξ"=> parcelUp S
lemma parcel_star (p:E4)(x:H.Op): star (ξ p x)=ξ p (star x):= by rw [parcelUp,parcelUp,star_mul,star_mul,trans_star,trans_star,neg_neg,mul_assoc]
@[simp] lemma parcel_zero (A:H.Op): ξ 0 A=A:=by unfold parcelUp; rw [neg_zero,show U 0 =1 from S.unit.origin,one_mul,mul_one]
lemma parcel_charge (x:E4)(p:H.Op): ‖parcelUp S x p‖ ≤ ‖p‖:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro v; unfold parcelUp; simp only [Picket.trans, mul_apply_eq_comp, S.unit.unitary]; simpa only [S.unit.unitary] using p.le_opNorm (S.unit.translation (-x) v)
lemma parcel_mul (p:E4)(x y:H.Op): ξ p (x*y)= ξ p x*ξ p y:= by
 unfold parcelUp; simp only [mul_assoc,← mul_assoc (U (-p)) (U p),mail_inv,one_mul]
lemma parcel_add (p q:E4)(x:H.Op): ξ (p+q) x=ξ p (ξ q x):= by unfold parcelUp; rw [neg_add_rev,trans_sum,trans_sum]; simp only [mul_assoc]
lemma parcel_went (p:E4)(x:H.Op): ξ (-p) (ξ p x)=x:= by rw [← parcel_add,neg_add_cancel,parcel_zero]
@[simp] lemma parcel_inv (p:E4)(x:H.Op): ξ p (ξ (-p) x)=x:= by rw [← parcel_add,add_neg_cancel,parcel_zero]
lemma inParcel {p:E4}(x y:H.Op)(e:y * trans S p= trans S p * x): parcelUp S p x=y:= by rw [parcelUp,← e,mul_assoc, mail,mul_one]
-- via SEP a. charges M
variable (a:Axis)
def eyebrow (p:E4): Meter:= fun i=>if i=a then 0 else p i
@[simp] lemma eyebrow_neg(x:E4): eyebrow a (-x)= -(eyebrow a x):= by ext1 i; by_cases v:i=a<;> simp [eyebrow,v]
lemma eye_amount (p:E4): Anvil.position (a:=a) (eyebrow a p) (p a)=p:= by
 ext1 v; unfold Anvil.position; by_cases h:v=a
 · subst v; simp only [PiLp.add_apply,PiLp.smul_apply, show ((rimPay a (eyebrow a p)).val) a=0 from (rimPay ..).property, zero_add]; simp
 simp [Anvil.rimPay_at _ _ _ h,h,eyebrow]
-- shadow a: explicit (S:..)
lemma salute (S:OS.Semigroup H a)(x:E4):polarize S (eyebrow a x) (x a)= trans S x:=by rw [physical_shifts, (show (rimPay a (eyebrow a x)).val+(x a) • basis a=x from eye_amount a x)]
lemma atParcel (S:OS.Semigroup H a)(x:E4)(A:H.Op) : sunny S (eyebrow a x) (x a) A= parcelUp S x A:= by
 unfold sunny parcelUp; rw [salute,← eyebrow_neg]; exact congrArg (fun q=> trans S x*A*q) (salute a S (-x)) -- need simp
end YM.BridgeClub
