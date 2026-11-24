import YM.SU5.ThinInteraction.Columns
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
noncomputable section
namespace YM.SatinThin
open MeasureTheory Filter Set Mink Spectral
open Six
open scoped InnerProductSpace Topology NNReal ENNReal BigOperators
section
variable {L:Hilbert} (Q:PVM L E4) (A:Set E4) (P:MeasurableSet A) (x:L)
include P
lemma squaring (A' : Set E4)(h : MeasurableSet A')(p : A ⊆ A'):
    Q.region A (Q.region A' x) = Q.region A x:= by rw [←ContinuousLinearMap.comp_apply,Q.joins P h, inter_eq_left.mpr p]
lemma fix_squaring (a:ℂ) : let y:= a • Q.region A x; Q.region A y=y:= by intro y; exact (map_smul (Q.region A) a (Q.region A x)).trans (congrArg (fun x:L=> a • x) (Q.idempotent P x))
lemma carries (p: Q.region A x=x) : ∀ᵐ w∂(Q.diagonal x), w∈A := by
  refine ae_iff.mpr ((Q.null_pair P.compl x).2 ?_)
  nth_rw 1 [←p]
  rw [←ContinuousLinearMap.comp_apply,Q.joins P.compl P,Set.compl_inter_self,Q.none]; rfl
lemma commutes_at {T:L.Op} {k:E4→ℂ} (e:Q.Represents k T) : Q.region A (T x)=T (Q.region A x):=DFunLike.congr_fun (e.comm_region P).symm x
lemma canon_inner (p:Q.region A x=x) (y:L): inner ℂ x y=inner ℂ x (Q.region A y):= by
  nth_rw 1 [←p]; rw [← Q.real P,ContinuousLinearMap.adjoint_inner_left,Q.real P] -- both replaced
lemma unit_ear (T:L.Op) {k:E4→ℂ} (e:Q.Represents k T) (p:Q.region A x=x) (y:L) (h : Q.region A y=x):
    inner ℂ x (T y)=∫ w,k w ∂Q.diagonal x:=
    (canon_inner Q A P x p (T y)).trans ((congrArg (fun y:L=>inner ℂ x y) ((commutes_at Q A P y e).trans (congrArg (fun x:L=> T x) h))).trans (e.on_diag x))
-- In a real estimate, integrate only on anchor.
lemma unit_floor {k:E4 → ℂ} (T:L.Op)(e:Q.Represents k T) {c:ℝ} (p:Q.region A x=x) (u:‖x‖=1)
    (hk:∀ w∈A,c≤(k w).re) (y:L) (h : Q.region A y=x): c≤(inner ℂ x (T y)).re:= by
  let μ:= Q.diagonal x
  rw [unit_ear Q A P x T e p y h]
  change c≤RCLike.re (K:=ℂ) (∫ w,k w ∂Q.diagonal x)
  rw [←integral_re (e.admissible.integrable _)]
  have hz: c=∫ _:E4,c ∂μ:= by
    rw [integral_const,Q.same MeasurableSet.univ x,Q.all]; simp [u]
  exact hz.trans_le (integral_mono_ae (integrable_const _) (e.admissible.integrable x).re ((carries Q A P x p).mono hk))

lemma norm_anchor (p:0<(Q.diagonal x).real A) : ‖(↑(Real.sqrt ((Q.diagonal x).real A))⁻¹:ℂ) • Q.region A x‖=1:= by
 let u := ‖Q.region A x‖; have he: Real.sqrt ((Q.diagonal x).real A)=u := by rw [Q.same P,Real.sqrt_sq (norm_nonneg _)]
 have hu:0<u:= he ▸ Real.sqrt_pos.mpr p
 rw [norm_smul,he, Complex.ofReal_inv, norm_inv]; simp [abs_of_pos hu,Complex.norm_real,show ‖Q.region A x‖=u from rfl,hu.ne']
end
section estimate
-- costs on a fixed cube
open scoped Real
lemma spatial_bill (x z:Space3) (h:∀ i,|x i| ≤ 1/16) (p:∀ i,|z i|≤1) : |inner ℝ z x| ≤ 3/16 := by
 have he (i:Fin 3): |inner ℝ (z i) (x i)| ≤ 1/16:= by
    rw [Real.inner_apply,abs_mul]; simpa [mul_comm] using mul_le_mul (h i) (p i) (abs_nonneg _) (show 0≤(1/16:ℝ) by norm_num)
 rw [PiLp.inner_apply]
 exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _=>he i)).trans_eq (by simp; ring))

def glow (m:ℝ)(k z:Space3)(τ:ℝ)(x:E4):ℂ:=
  Complex.exp ((↑(m * τ):ℂ) - (↑(inner ℝ k z):ℂ)*Complex.I) *
    phasor z x * ↑(Real.exp (-(τ* YM.time x)))
lemma glow_floor (m:ℕ) (k z:Space3) (x:E4) (τ:ℝ) (h:0≤τ) (p:τ≤2) (e: YM.time x ≤ (m:ℝ)+2)
    (hg: ∀ i,|z i|≤1/16) (v: ∀ i,|YM.spatial x i - k i| ≤ 1): Real.exp (-4)/2 ≤ (glow m k z τ x).re := by
 unfold glow; change _ ≤ (_ * Complex.exp ((↑(inner ℝ (YM.spatial x) z):ℂ) * Complex.I) * _).re
 rw [Complex.ofReal_exp, ←Complex.exp_add, ←Complex.exp_add, Complex.exp_re]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.mul_im,Complex.add_im,Complex.sub_im, mul_zero,mul_one,add_zero,sub_zero,zero_sub]
 have he: -4 ≤ (m:ℝ)*τ + -(τ* YM.time x):= by nlinarith only [mul_le_mul_of_nonneg_left e h,p]
 let y:= ⟪spatial x - k,z⟫_ℝ
 rw [show -⟪k,z⟫_ℝ+⟪spatial x,z⟫_ℝ=y by unfold y; rw [inner_sub_left]; abel]
 have hx: |y| ≤ Real.pi / 3 := le_trans (spatial_bill z (spatial x-k) hg v) (by linarith only [Real.pi_gt_d4])
 have hh : 1/2 ≤ Real.cos y := by rw [←Real.cos_abs,←Real.cos_pi_div_three]; exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith only [Real.pi_pos]) hx
 exact le_trans (le_of_eq (show Real.exp (-4) / 2= Real.exp (-4)*(1/2) by ring)) (mul_le_mul (Real.exp_le_exp.mpr he) hh (by positivity) (Real.exp_pos _).le)
end estimate
#print axioms glow_floor
#print axioms unit_floor
end YM.SatinThin
