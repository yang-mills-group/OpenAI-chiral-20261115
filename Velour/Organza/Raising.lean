import Velour.Organza.Muslin
import YM.Distribution.Product
/-! Strong-operator Minkowski translation smearing **in the physical representation**.
T may already carry ordered Euclidean pads. Real-time sign is that of S.unit, i.e.
+ipx. Lebesgue. We get linear, tempered, translation covariant smears costing
only L¹. High-energy estimates from these smooth detectors follow later.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe
local notation "U" => S.unit.translation

/- **Bounded ops**. Conjugate by physical spacetime translations. -/
def dangle (b:E4)(T:H.Op):H.Op:= U b * T * U (-b)
local notation "α" => S.dangle

lemma unit_step (b c:E4): U b * U c=U (b+c):=S.unit.sends ..

lemma dangle_cont (T:H.Op)(x:H.space): Continuous (fun b=>α b T x):= by
  have t: Continuous (fun b:E4=>T (U (-b) x)):= T.continuous.comp ((S.unit.moves x).comp continuous_neg)
  change Continuous fun b:E4=>S.edge (b a) (S.U (SEP a b) (T (U (-b) x)))
  exact S.cont_edge _ _ (S.cont_cross _ _ t (SEP a).continuous) (by fun_prop)

lemma dangle_bill (b:E4)(T:H.Op)(x:H.space): ‖α b T x‖ ≤ ‖T‖ * ‖x‖:=by
  change ‖U b (T (U (-b) x))‖ ≤ _
  rw [S.unit.unitary]
  exact (T.le_opNorm _).trans_eq (congrArg (‖T‖ * ·) (S.unit.unitary ..))



lemma unit_star (b:E4): star (U b)= U (-b):= by
  ext1 v; apply ext_inner_left ℂ; intro x
  rw [← LinearIsometry.inner_map_map (show _ from
      { (U b).toLinearMap with norm_map' := S.unit.unitary b }) x (U (-b) v)]
  change inner ℂ x ((U b).adjoint v)= inner ℂ (U b x) (U b (U (-b) v))
  rw [← mul_apply_eq_comp,S.unit_step,add_neg_cancel,S.unit.origin, ContinuousLinearMap.adjoint_inner_right]; rfl

lemma dangle_star (b:E4)(T:H.Op) : star (α b T)=α b (star T):= by
 unfold dangle
 rw [star_mul,star_mul,S.unit_star,S.unit_star,neg_neg,mul_assoc]

/-! ## Vector integral -/

lemma unsoiled (T:H.Op)(f:Test4)(x:H.space): Integrable fun b=>f b • α b T x:= by
  have p: Integrable (fun b:E4=>‖f b‖ * (‖T‖*‖x‖)) volume:=
    f.integrable.norm.mul_const _
  exact p.mono' ((f.continuous.smul (S.dangle_cont ..)).aestronglyMeasurable)
    (ae_of_all _ fun b=>(norm_smul ..).trans_le
      (mul_le_mul_of_nonneg_left (S.dangle_bill ..) (norm_nonneg _)))

/-- our basic bill. -/
def L₁ (f:Test4) :ℝ:=‖f.toLp 1 volume‖
lemma real_L₁ (f:Test4): L₁ f=∫b,‖f b‖:=SchwartzMap.norm_toLp_one
lemma L₁_cont : Continuous L₁ := SchwartzMap.continuous_toLp.norm


private lemma wash_bound_aux (T:H.Op)(f:Test4)(x:H.space):
 ‖∫ b, f b • α b T x‖ ≤ (L₁ f * ‖T‖) * ‖x‖ := by
 rw [real_L₁,mul_assoc,←integral_mul_const]
 refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) ?_
 exact ae_of_all _ fun b=>(norm_smul ..).trans_le
      (mul_le_mul_of_nonneg_left (S.dangle_bill ..) (norm_nonneg _))

private noncomputable def wash (T:H.Op)(f: Test4): H.Op:= LinearMap.mkContinuous (σ:=RingHom.id ℂ)
 { toFun:= fun x=>∫ b, f b • α b T x
   map_add' x y:= by simp only [map_add,smul_add]; rw [integral_add (S.unsoiled ..) (S.unsoiled ..)]
   map_smul' c x:= by simp only [map_smul]; simp_rw [smul_comm _ c]; rw [integral_smul];rfl
 } _ (S.wash_bound_aux T f)

private noncomputable def washes (T:H.Op): Test4 →ₗ[ℂ] H.Op where
 toFun:=wash S T
 map_add' f g:= by
  ext1 x
  change (∫ b, (f+g) b • α b T x)= (∫ b, f b • α b T x)+∫ b, g b • α b T x
  simp_rw [_root_.add_apply,add_smul, integral_add (S.unsoiled ..) (S.unsoiled ..)]
 map_smul' c f:=by
  ext1 x
  change (∫ b, (c • f) b • α b T x)= c • ∫ b, f b • α b T x
  simp_rw [_root_.smul_apply,smul_eq_mul, mul_smul,integral_smul]


lemma zero_L₁ : L₁ 0=0:=by rw [real_L₁]; simp
lemma L₁_nonneg (f:Test4): 0≤L₁ f:=norm_nonneg _

private lemma washes_bound (T:H.Op)(f:Test4) : ‖S.washes T f‖≤ L₁ f * ‖T‖ :=
 ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (L₁_nonneg _) (norm_nonneg _))
     (S.wash_bound_aux T f)

/-- Minkowski translation smear. -/
def rasp (T:H.Op): Test4 →L[ℂ] H.Op where
 toLinearMap:=S.washes T
 cont:=by
  change Continuous (S.washes T)
  apply continuous_of_continuousAt_zero (S.washes T)
  have p:Tendsto (fun f:Test4=> L₁ f * ‖T‖) (𝓝 0) (𝓝 0):=by
    have k: L₁ 0 * ‖T‖ =0:=by rw [zero_L₁,zero_mul]
    exact k ▸ ((L₁_cont.mul (g:=fun _=>‖T‖) continuous_const).tendsto 0)
  change Tendsto _ _ _
  rw [map_zero]
  exact squeeze_zero_norm (S.washes_bound T) p

lemma rasp_apply (T:H.Op)(f:Test4)(x:H.space):
 S.rasp T f x=∫ b, f b • α b T x:=rfl
lemma rasp_bill (T:H.Op)(f:Test4) : ‖S.rasp T f‖ ≤ L₁ f * ‖T‖:=S.washes_bound ..


lemma rasp_star (T:H.Op)(f:Test4): star (S.rasp T f)= S.rasp (star T) (bar f):= by
  ext1 x; apply ext_inner_left ℂ; intro y
  change inner ℂ y ((S.rasp T f).adjoint x)=_
  rw [ContinuousLinearMap.adjoint_inner_right,← inner_conj_symm (S.rasp T f y),
      rasp_apply,rasp_apply,← integral_inner (S.unsoiled ..),← integral_inner (S.unsoiled ..),
      ← integral_conj]
  exact integral_congr_ae (ae_of_all _ fun b=> by
     dsimp only; rw [inner_smul_right, inner_smul_right,map_mul,bar_at,inner_conj_symm,
         ← S.dangle_star,show star (α b T) x=(α b T).adjoint x from rfl,ContinuousLinearMap.adjoint_inner_right]; rfl)

lemma rasp_ahead (T:H.Op)(f:Test4)(u:E4): S.rasp T (ahead u f)=α u (S.rasp T f):= by
  ext1 x
  change _=U u (S.rasp T f (U (-u) x))
  rw [rasp_apply,rasp_apply,←(U u).integral_comp_comm (S.unsoiled ..)]
  rw [← integral_add_left_eq_self (fun b=>ahead u f b • α b T x) u]
  refine integral_congr_ae (ae_of_all _ fun b=>?_ )
  dsimp only; rw [map_smul,ahead_at,add_sub_cancel_left]
  unfold dangle
  rw [neg_add_rev,← S.unit_step u b,← S.unit_step (-b) (-u)]; rfl -- inspect


lemma rasp_more_left (T K:H.Op)(p:∀b, Commute (U b) K) (f:Test4):
  S.rasp (K*T) f = K * S.rasp T f:= by
  ext1 x; rw [mul_apply_eq_comp, rasp_apply, rasp_apply, ←K.integral_comp_comm (S.unsoiled ..)]
  refine integral_congr_ae (ae_of_all _ fun b=>?_ )
  dsimp only; rw [map_smul]; unfold dangle
  rw [← mul_assoc, (p b).eq]; rfl
lemma rasp_more_right (T K:H.Op)(p:∀b, Commute (U b) K)(f:Test4):
  S.rasp (T*K) f= S.rasp T f * K:=by
  ext1 x; rw [mul_apply_eq_comp, rasp_apply,rasp_apply]
  refine integral_congr_ae (ae_of_all _ fun b=>?_ )
  dsimp only; unfold dangle
  simp only [mul_assoc]; rw [← (p (-b)).eq];rfl
#print axioms rasp
#print axioms rasp_ahead
#print axioms rasp_star

