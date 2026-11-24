import YM.CF.Buffered.Cone
import YM.CF.Buffered.Form

/-!
# Buffered FiniteGaugeData marked convergence

Period-local half-reflection inequality on the partner of *these very* paid
histories, and pointwise extensive estimates, combined with a local norm on
actual joint link (including reconstruction) arguments. We subsequently
iterate the inequality to remove the four-volume scale from the estimate on
local insertions; then transfer to `cap` on the cone by `cone_ratio`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

lemma theta_fee {I:Type*} [Fintype I] [LinearOrder I]
    (U : UNI I) (f : Fock.FC I) : ‖Fock.theta U f‖ = ‖f‖ := by
  rw [Fock.theta,twist_norm,Scroll.norm_cc]

variable {K: Calibration} (H:Histories K) {m n:Side}

abbrev hearth (m : Side) (t:ℕ) (f:Mark (K.c m)) :=
  atZero K.P (H.warm m t) (H.loom m) f

def cash (l:Loom n) (f:Mark n) := ∫ x, ‖f (drawn l x)‖ ∂city n

lemma cash_nonneg (l:Loom n) (f:Mark n) : 0 ≤ cash l f := integral_nonneg fun _=> norm_nonneg _
lemma cashable {l:Loom n} {f:Mark n} (w:Measurable l) (p:Envelope f) :
    Integrable (fun x=> ‖f (drawn l x)‖) (city n) :=
  (Env.integrableX (Env.along p (drawn_m l w)) _).norm

/-- Retain exactly the data used at one call. -/
structure Wick (H:Histories K) (m : Side) (t:ℕ) : Prop where
  allowed : K.Allowed m t
  step : 0 < t
  shot : Shots K.V K.T K.J K.η (K.monthSize m allowed.1)
    (H.loom m) t (H.sharp m t) (H.warm m t) (H.wave t) (H.wave' t)
    (H.B₀ t) (H.tilt t) (H.tilt' t) K.h K.R0 K.δ
  delta : Delta K.P (H.sharp m t 0) (H.warm m t 0) (H.loom m 0)
    (Burn.bill m.val t K.b₀ H.m')
  floor0 : Burn.presrec m.val H.c' ≤ ‖vac0 K.P (H.warm m t 0) (H.loom m 0)‖

lemma eventuallyWick : ∀ᶠ t in atTop, ∀ m:Side, K.Allowed m t → Wick H m t := by
  filter_upwards [H.paid,eventually_gt_atTop 0] with i hi ti m g
  obtain ⟨s,d,p⟩ := hi m g
  exact ⟨g,ti,s,d,p⟩

private def extensiveFee (H:Histories K) := |Burn.trial₀ K| + |H.m'|
def tariff (H:Histories K) := extensiveFee H + 1 + |H.c'|
lemma extensiveFee_nonneg : 0 ≤ extensiveFee H := add_nonneg (abs_nonneg _) (abs_nonneg _)
lemma tariff_nonneg : 0 ≤ tariff H := add_nonneg (by linarith only [extensiveFee_nonneg H] : 0 ≤ extensiveFee H + 1) (abs_nonneg _)

namespace Wick
variable {H} {t:ℕ} (p: Wick H m t)
include p

lemma warm_nonzero : partitionZ (H.warm m t 0) K.P (H.loom m 0) ≠ 0 :=
  part_ne_zero _ _ _ (norm_pos_iff.mp ((Real.exp_pos _).trans_le p.floor0))
lemma loom_m : Measurable (H.loom m 0) := (p.shot.warm_grant.paid 0 p.step).2
lemma warm_add {f g:Mark (K.c m)} (w:Envelope f) (v:Envelope g) :
    hearth H m t (f+g)=hearth H m t f + hearth H m t g := by
  unfold hearth atZero
  rw [mark_add p.loom_m w v (p.shot.warm_grant.paid 0 p.step).1,add_div]
lemma warm_one : hearth H m t 1 = 1 := by
  unfold hearth atZero; rw [markvac]; exact div_self p.warm_nonzero
omit p in
lemma warm_scale (a:ℂ) (f:Mark (K.c m)) : hearth H m t (a • f) = a*hearth H m t f := by
  unfold hearth atZero; rw [mark_smul,mul_div_assoc]

private lemma point (x:Orbit (K.c m)) :
    ‖Graph.recX K.P (H.warm m t 0) (H.loom m 0) x‖ ≤ Real.exp ((extensiveFee H + 1)*(m.val:ℝ)^4) := by
  let V : ℝ := (m.val:ℝ)^4
  have hm : 1 ≤ V := one_le_pow₀ (by exact_mod_cast m.property : (1:ℝ) ≤ m.val)
  have hb : Burn.bill m.val t K.b₀ H.m' ≤ Real.exp (extensiveFee H * V) := by
    unfold Burn.bill
    calc
      _ ≤ 1 * Real.exp (H.m'*(m.val:ℝ)^4) := mul_le_mul_of_nonneg_right
        (by simpa using (Real.rpow_le_rpow_of_exponent_le
           (by norm_num : 1 ≤ (2:ℝ)) (show -(Burn.depth K.b₀ t:ℝ)/2 ≤ 0 by exact div_nonpos_of_nonpos_of_nonneg (by simp) (by norm_num)))) (Real.exp_pos _).le
      _ ≤ _ := by rw [one_mul]; exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))) (by positivity))
  let y:=Graph.recX K.P (H.sharp m t 0) (H.loom m 0) x
  let z:=Graph.recX K.P (H.warm m t 0) (H.loom m 0) x
  have he : ‖z‖ ≤ Real.exp (extensiveFee H * V) + Real.exp (extensiveFee H * V) := by
    have hz:= norm_sub_norm_le z y
    have hv : ‖z-y‖ ≤ Real.exp (extensiveFee H * V) := by rw [norm_sub_rev]; exact (p.delta x).trans hb
    have hh : ‖y‖ ≤ Real.exp (extensiveFee H * V) := (Burn.sharp_extensive p.shot x).trans
      (Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))) (by positivity)))
    linarith
  change ‖z‖ ≤ Real.exp ((extensiveFee H + 1)*V); refine he.trans ?_
  rw [←mul_two,add_mul,Real.exp_add,one_mul]; exact mul_le_mul_of_nonneg_left
    ((by linarith : (2:ℝ) ≤ V+1).trans (Real.add_one_le_exp _)) (Real.exp_pos _).le

/-- Global pricing; the only part paying the four-volume. This uses the
pointwise delta (hence pays also if the tests are functions of the filled links). -/
lemma chimney (f:Mark (K.c m)) (w:Envelope f) : ‖hearth H m t f‖ ≤ Real.exp (tariff H * (m.val:ℝ)^4)*cash (H.loom m 0) f := by
  let V : ℝ := (m.val:ℝ)^4
  have hv : 0 ≤ V := by dsimp [V]; positivity
  let D : ℝ := (extensiveFee H + 1)*V
  let l:=H.loom m 0
  let A:=num0 K.P (H.warm m t 0) l f
  let μ:=city (K.c m)
  have he: ‖A‖ ≤ cash l f * Real.exp D := by
    unfold A num0 markedRead
    refine (norm_integral_le_integral_norm ..).trans ?_
    rw [cash,←integral_mul_const]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun _=>norm_nonneg _)) ((cashable p.loom_m w).mul_const _) (Eventually.of_forall fun i=> ?_)
    exact (mark_bound ..).trans (mul_le_mul_of_nonneg_left (p.point i) (norm_nonneg _))
  unfold hearth atZero; rw [←same_ratio,norm_div]
  change ‖A‖ / ‖vac0 K.P (H.warm m t 0) l‖ ≤ Real.exp (tariff H * V)*cash l f
  let X := Burn.presrec m.val H.c'
  have hx:0<X:=Real.exp_pos _
  refine (div_le_div₀ (mul_nonneg (cash_nonneg ..) (Real.exp_pos _).le) he hx p.floor0).trans ?_
  rw [mul_div_assoc,mul_comm (Real.exp (tariff H * V))]
  refine mul_le_mul_of_nonneg_left ?_ (cash_nonneg ..)
  unfold X Burn.presrec; rw [←Real.exp_sub]; unfold D tariff; apply Real.exp_le_exp_of_le
  change (extensiveFee H + 1) * V - -H.c' * V ≤ _
  rw [←_root_.sub_mul]; gcongr; linarith [le_abs_self H.c']

local notation "bandZ" i:max z:max => band (K.c m) i (Heat.gaugeShift K.B z) K.ℓ
lemma ember (i:Axis) (z:ℤ) {f:Mark (K.c m)} (w:AtSupport false (bandZ i z) f) :
    0 ≤ hearth H m t (reflMark i (Heat.gaugeShift K.B z) f*f) :=
  donor K.P _ _ _ _ _ _ _ i K.legal K.R.coarse p.shot.warm_grant (fun k _=> H.lawn m p.allowed.1 k) K.buffer z p.shot.heat.choose p.warm_nonzero w

/- Need PSD only on f and 1; prove without proof-dependent norms. -/
omit p in
private lemma two (x y v : ℂ) (h : 0 ≤ v)
    (e : ∀ a:ℂ, 0 ≤ v + a*y + star a*x + star a*a) : ‖x‖^2 ≤ ‖v‖ := by
  have h0:= Complex.le_def.mp h
  have h1:= (Complex.le_def.mp (e 1)).2
  have hI:= (Complex.le_def.mp (e Complex.I)).2
  simp [Complex.mul_im] at h0 h1 hI
  have hp:y.re=x.re:= by linarith
  have hx:y.im = -x.im:= by linarith
  have ht:= (Complex.le_def.mp (e (-x))).1
  simp only [Complex.add_re, Complex.mul_re,Complex.neg_im,Complex.neg_re, Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.zero_re,hp,hx] at ht
  have hk:= Complex.re_le_norm v
  rw [Complex.sq_norm,Complex.normSq_apply]; nlinarith

lemma cinder (i:Axis) (z:ℤ) {f:Mark (K.c m)} (w:AtSupport false (bandZ i z) f) :
    ‖hearth H m t f‖^2 ≤ ‖hearth H m t (reflMark i (Heat.gaugeShift K.B z) f*f)‖ := by
  let T:=reflMark (n:=K.c m) i (Heat.gaugeShift K.B z)
  let S:=bandZ i z
  have W:= (w.refl i (Heat.gaugeShift K.B z)).env
  apply two _ (hearth H m t (T f)) _ (p.ember i z w)
  intro a
  let u:Mark (K.c m):=1
  have he:=p.ember i z (w.addM ((AtSupport.oneM S).smulM a))
  have ht : T (f+a • u) = T f+star a • u := by
    funext x; unfold T reflMark; rw [Pi.add_apply, Fock.theta_add,Pi.smul_apply,Fock.theta_smul]; rw [show Fock.theta _ (u _) = 1 from Fock.theta_one _]; rfl
  let b:=star a
  change 0 ≤ hearth H m t (T (f+a • u)*(f+a • u)) at he
  rw [ht, add_mul,mul_add,mul_add,Algebra.mul_smul_comm,mul_one,Algebra.smul_mul_assoc,one_mul,Algebra.smul_mul_assoc,one_mul] at he
  have ha : Envelope (a • T f) := ((w.refl ..).smulM _).env
  have hb : Envelope (star a • f) := (w.smulM _).env
  have hc : Envelope (star a • a • u) := (((AtSupport.oneM S).smulM a).smulM (star a)).env
  have hd : Envelope (T f*f) := env_mult W w.env
  have hD : Envelope (T f*f+a • T f) := Girt.kitE _ _ (·+·) (by fun_prop) hd ha
  have hE : Envelope (star a • f+star a • a • u) := Girt.kitE _ _ (·+·) (by fun_prop) hb hc
  rw [p.warm_add hD hE,p.warm_add hd ha,p.warm_add hb hc] at he
  rw [warm_scale,warm_scale,warm_scale,warm_scale,p.warm_one,mul_one] at he
  convert he using 1; ring

end Wick
end YM.CF.Buffered.Afterglow
