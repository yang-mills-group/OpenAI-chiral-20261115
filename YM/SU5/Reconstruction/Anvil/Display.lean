import YM.SU5.Reconstruction.Anvil.Plate
/-! # real transl-frame resource symmetry. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace Picket OS Semigroup Price Terrain ConePrice Analysis Sail
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {a:Axis} {H:Hilbert} (S:OS.Semigroup H a)
local notation "v"=> S.U
variable (x y:Meter) (t u:ℝ)
def position := ((rimPay a x).val:E4)+ t • basis a
lemma position_add : position (a:=a) x t +position (a:=a) y u= position (a:=a) (x+y) (t+u):= by rw [position,position,position,rimPay_add,add_smul]; push_cast; abel
lemma physical_shifts : polarize S x t= Picket.trans S ((rimPay a x).val+t • basis a):=by
 unfold polarize Picket.trans
 rw [← S.unit.sends ((rimPay a x).val) (t • basis a)] -- need unfold trans
 rw [ConePrice.translation]; have h:= Picket.trans_time t S; unfold Picket.trans at h; rw [h]; rfl
local notation "φ"=> polarize S
lemma spin_add : polarize S x t * polarize S y u= polarize S (x+y) (t+u):= by
 rw [physical_shifts, physical_shifts,physical_shifts]; refine (S.unit.sends ..).trans (congrArg (Picket.trans S) (position_add x y t u))
@[simp] lemma spin_zero : polarize S (0:Meter) (0:ℝ)=1:= by rw [physical_shifts,rimPay_zero,zero_smul,add_zero]; exact S.unit.origin
lemma spin_inv : φ (-x) (-t) * φ x t=1:= by simp only [spin_add,neg_add_cancel,spin_zero]
lemma rotates_wallet (A B:H.Op) (e:Commute A (sunny S (y-x) (u-t) B)): Commute (sunny S x t A) (sunny S y u B) := by
 let T:= sunny S x t
 have hp(Q Q':H.Op): T Q*T Q'=T (Q*Q'):= by
   unfold T sunny; simp only [mul_assoc, ← mul_assoc (φ (-x) (-t)) (φ x t), spin_inv,one_mul]; -- simp linter
 have E : sunny S y u B=T (sunny S (y-x) (u-t) B):= by
   unfold T sunny; rw [show φ x t*(φ (y-x) (u-t)*B*φ (-(y-x)) (-(u-t)))*φ (-x) (-t) = (φ x t * φ (y-x) (u-t))*B*(φ (-(y-x)) (-(u-t))*φ (-x) (-t)) from (by simp only [mul_assoc]),spin_add,spin_add]; congr 2<;> abel_nf
 rw [E]; exact (show (T A)* T (sunny S (y-x) (u-t) B) = _ from (hp A _).trans ((congrArg T e.eq).trans (hp (sunny S (y-x) (u-t) B) A).symm))
end YM.Anvil
