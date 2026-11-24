import Velour.Organza.Gauze
/-!
# Smooth heat cutoff permitting high-order telescoping

A charge on both sides to de-pad from any positive dial. As crucial:
**the differences** are high order in the larger dial even *after*
cancellation of the smaller heat.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


local notation "R" => S.gauze
local notation "E" => S.E


private lemma pow_limit (T:H.Op)(r:ℝ)(p:‖T‖≤r)(m:ℕ):
  ‖T^m‖ ≤ r^m:=by
 induction m with
 | zero=>
   rw [pow_zero,pow_zero]
   exact ContinuousLinearMap.opNorm_le_bound _ (by simp) (by intro; rw [one_mul,one_apply_eq_self])
 | succ n h=>
    rw [pow_succ,pow_succ]
    exact (norm_mul_le ..).trans (mul_le_mul h p (norm_nonneg _) ((norm_nonneg _).trans h))

private noncomputable def multistrand (A B K:H.Op):ℕ→ H.Op
 | 0=>0
 | m+1=>multistrand A B K m * A + B^m*K

private lemma multistrand_prices (A B K Z:H.Op)(s:A-B=Z*K)(e:Commute Z B)(m:ℕ):
  A^m-B^m=Z*multistrand A B K m:=by
 induction m with
 | zero=>simp [multistrand]
 | succ m h=>
   rw [pow_succ,pow_succ,multistrand,mul_add,←mul_assoc,←h,←mul_assoc Z,
       (e.pow_right _).eq,mul_assoc (B^m), ←s, mul_sub, sub_mul]
   abel


private lemma multistrand_bound (A B K:H.Op)(r:ℝ)(a':‖A‖≤r)(b:‖B‖≤r)(k:‖K‖≤r)(m:ℕ):
  ‖multistrand A B K m‖ ≤ m * r^m:= by
 induction m with
 | zero=>simp [multistrand]
 | succ n h=>
    have hr:0≤r:=(norm_nonneg _).trans k
    rw [multistrand, Nat.cast_succ,add_mul,pow_succ,one_mul,←mul_assoc]
    exact (norm_add_le ..).trans (add_le_add
        ((norm_mul_le ..).trans (mul_le_mul h a' (norm_nonneg _) (by positivity)))
        ((norm_mul_le ..).trans (mul_le_mul (pow_limit B r b n) k (norm_nonneg _) (by positivity))))

private def loose (t:ℝ≥0):= R - E t * R
private lemma heat_dove(t u:ℝ≥0): Commute (E t) (E u):= by
 change _ = _
 change (E t).comp (E u)=(E u).comp (E t)
 rw [← S.time, add_comm,S.time]
private lemma heat_loose (t u:ℝ≥0):Commute (E t) (S.loose u):=
 (S.gauze_heated t).sub_right ((S.heat_dove t u).mul_right (S.gauze_heated t))
private lemma loose_bound (t:ℝ≥0): ‖S.loose t‖ ≤ 2:=by
  unfold loose
  rw [show (2:ℝ)=1+1 from (one_add_one_eq_two).symm]
  exact (norm_sub_le ..).trans
       (add_le_add S.gauze_norm ((norm_mul_le ..).trans
         (mul_le_one₀ (S.shrinks _) (norm_nonneg _) S.gauze_norm)))


def winding (m:ℕ)(t:ℝ≥0) := multistrand R (S.loose t) R m

lemma winding_bound (m:ℕ)(t:ℝ≥0): ‖S.winding m t‖ ≤ m * 2^m:=
  multistrand_bound R _ R _ (S.gauze_norm.trans (by norm_num)) (S.loose_bound t) (S.gauze_norm.trans (by norm_num)) m

private lemma winding_holds (m:ℕ)(t:ℝ≥0):
 E t * S.winding m t = R^m - S.loose t ^ m:=
 (multistrand_prices R _ R _ (by rw [loose]; abel) (S.heat_loose t t) m).symm

lemma winding_symm (m:ℕ)(t u:ℝ≥0): Commute (E u) (S.winding m t):=by
 unfold winding
 induction m with
 | zero=> exact Commute.zero_right ..
 | succ n h=>
    have x:=S.gauze_heated u
    exact (h.mul_right x).add_right (((S.heat_loose u t).pow_right n).mul_right x)

lemma heat_cancel {X Y:H.Op}{t:ℝ≥0}(p:E t*X=E t*Y):X=Y:=by
 ext1 x
 exact sub_eq_zero.mp (S.heat_faithful t _ (by rw [map_sub,←mul_apply_eq_comp,p,mul_apply_eq_comp,sub_self]))



lemma winding_diff (s t:ℝ≥0)(p:s≤t)(m:ℕ):
 ‖S.winding m s - E (t-s)*S.winding m t‖ ≤ m * (2 * (t:ℝ))^m:=by
 let A:=S.loose t
 let T:=S.loose s
 have e:E s * E (t-s)= E t:= ((S.time ..).symm.trans (congrArg E (add_tsub_cancel_of_le p)))
 have i:A-T= E s * S.loose (t-s):=by
    unfold A T loose; rw [mul_sub,←mul_assoc, e]; abel
 have x: S.winding m s - E (t-s)*S.winding m t=
      multistrand A T (S.loose (t-s)) m:= by
    apply S.heat_cancel (t:=s)
    rw [mul_sub,←mul_assoc (E s),e,winding_holds,winding_holds,
        ← multistrand_prices _ _ _ _ i (S.heat_loose s s) m]
    dsimp only [A,T]
    abel
 rw [x]
 have k {u:ℝ≥0}(h:u≤t): ‖S.loose u‖≤ 2*(t:ℝ):=
    (S.gauze_tug _).trans (mul_le_mul_of_nonneg_left (show (u:ℝ)≤_ from h) (by simp))
 exact multistrand_bound _ _ _ _ (k le_rfl) (k p) (k tsub_le_self) m


lemma winding_approaches {ι:Type} {l:Filter ι} {f:ι→ℝ≥0} (p:Tendsto f l (𝓝 0))
    {m:ℕ} (u:m≠0):
  Tendsto (fun i=> E (f i) * S.winding m (f i)) l (𝓝 (R^m)):=by
   simp_rw [winding_holds]
   have s:Tendsto (fun i=>S.loose (f i)) l (𝓝 0):= by
      refine squeeze_zero_norm (fun i=>S.gauze_tug (f i)) ?_
      simpa using (NNReal.tendsto_coe.mpr p).const_mul 2
   simpa only [zero_pow u,sub_zero] using (s.pow m).const_sub (R^m)
#print axioms winding_approaches
#print axioms winding_diff

