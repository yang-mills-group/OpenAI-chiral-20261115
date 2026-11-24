import YM.CF.Lattice.Linearized
import YM.Next.FREE_KERNELS.Lines
import Mathlib.Analysis.Complex.SqrtDeriv
/-! Complex momentum, unnormalized spline splittings. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric
open scoped Topology Matrix BigOperators

def tmap (p : BZ.Mom) : Momentum := fun i => (p i:ℂ)
def pl (p : Momentum) (a : Axis) := 1-Complex.cos (p a)
def sine (p : Momentum) : Momentum := fun i => Complex.sin (p i)
def kin (p : Momentum) := -1 + ∑ a, pl p a
def mag (p : Momentum) := kin p^2+∑ a,sine p a^2
def rad (p : Momentum) := Complex.sqrt (mag p)
def gD (p : Momentum) := rad p+kin p
lemma wave_eq (p:BZ.Mom) : kin (tmap p) = (BZ.bare p:ℂ) := by simp [pl,tmap,kin,BZ.bare]
lemma mag_real (p:BZ.Mom) : mag (tmap p)=(BZ.wave p:ℂ)^2 := by
  unfold mag; rw [wave_eq]; rw [← Complex.ofReal_pow]; -- maybe hits wrong term
  simp_rw [sine,tmap, ← Complex.ofReal_sin]; norm_cast
  unfold BZ.wave; exact (Real.sq_sqrt (by positivity)).symm
lemma r_real (p:BZ.Mom) : rad (tmap p)=(BZ.wave p:ℂ) := by
  rw [rad,mag_real]; exact Complex.sq_cpow_two_inv (by simpa using BZ.wave_pos p)
lemma pq (p:Momentum) (h:physical p) : tmap (fun i : Fin 4 => (p i).re)=p := by
  rw [physical_iff] at h; funext i; apply Complex.ext <;> simp [tmap,h]
lemma pile (p:Momentum) : mag p = 1+ ∑ i, pl p i*(∑ j∈Finset.univ.erase i, pl p j) := by
  have he (i) : sine p i^2= 2*pl p i-(pl p i)^2 := by
    have hs := Complex.sin_sq_add_cos_sq (p i)
    rw [show sine p i=Complex.sin _ from rfl, pl,eq_sub_of_add_eq hs]; ring
  have hf (i : Axis) : ∑ j∈Finset.univ.erase i, pl p j = (∑ j,pl p j)-pl p i := eq_sub_of_add_eq (Finset.sum_erase_add _ _ (Finset.mem_univ _))
  unfold mag kin; simp_rw [he, hf, mul_sub]; simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,sq]; ring
lemma tmap_physical (p:BZ.Mom) : physical (tmap p) := by rw [physical_iff]; exact fun _ => rfl
lemma r_ge (p:BZ.Mom) : 1 ≤ BZ.wave p := by
  have he := congr_arg Complex.re ((mag_real p).symm.trans (pile (tmap p)))
  simp only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.add_re,Complex.one_re,Complex.re_sum] at he
  have hh : (1:ℝ) ≤ BZ.wave p ^ 2 := by
    rw [he]; refine le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ?_); unfold pl
    simp only [tmap, ← Complex.ofReal_cos]; push_cast; norm_cast
    exact mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (Real.cos_le_one _))
  nlinarith [BZ.wave_pos p]
lemma r_square (p:Momentum) : rad p ^2=mag p := Complex.cpow_ofNat_inv_pow _ 2
lemma sector (p:Momentum) : rad p+1≠0 := by
  suffices 0 ≤ (rad p).re by intro h; have he:=congr_arg Complex.re h; simp at he; linarith
  rw [rad,Complex.sqrt_eq_real_add_ite]; split <;> simp [Complex.mul_re] <;> positivity

lemma cube_inside : cube (α:=Axis) zone ⊆ closedBall (0: Momentum) domainRadius := by
  intro p hp; rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg domainRadius_pos.le]; exact zone_in_disk p hp
lemma mag_diff : Differentiable ℂ mag := by unfold mag kin pl sine; fun_prop
lemma rad_uniform : ∃ η C : ℝ, 0<η ∧ 0<C ∧ SafeCube η C rad := by
  let s := closedBall (0: Momentum) domainRadius; have hS : IsCompact s := isCompact_closedBall ..
  obtain ⟨δ,hp,hδ⟩ := Metric.uniformContinuousOn_iff.mp (hS.uniformContinuousOn_of_continuous mag_diff.continuous.continuousOn) 1 one_pos
  obtain ⟨a,ha,H⟩ := hS.exists_isMaxOn (show s.Nonempty from ⟨0,cube_inside (cube_zero zone zone_pos)⟩) mag_diff.continuous.norm.continuousOn
  let η := min zone (δ/2); have he : 0<η := lt_min zone_pos (by positivity)
  refine ⟨η,‖mag a‖+1,he,by positivity,⟨fun p hm => ?_,fun p hm => ?_⟩⟩
  · apply (Complex.differentiableAt_sqrt (Or.inl ?_)).comp p (mag_diff p)
    let q := rpart p
    have hh := hδ p (cube_inside (cube_mono (min_le_left ..) hm)) q (cube_inside (cube_mono (min_le_left ..) (mem_cube_real (rpart_mem_realCube hm) he))) (lt_of_le_of_lt (thin_dist he hm) ((min_le_right ..).trans_lt (by linarith)))
    let v : BZ.Mom := fun i => (p i).re; have hz : q=tmap v:= rfl
    have hx:= Complex.abs_re_le_norm (mag p-mag q)
    rw [dist_eq_norm] at hh; rw [Complex.sub_re,hz,mag_real,← Complex.ofReal_pow,Complex.ofReal_re] at hx
    rw [hz,mag_real,← Complex.ofReal_pow] at hh
    nlinarith [(abs_le.mp hx).1, r_ge v]
  have hx := H (cube_inside (cube_mono (min_le_left ..) hm)); have hh : ‖rad p‖ ^ 2=‖mag p‖ := by rw [← norm_pow,r_square]
  change ‖mag p‖≤‖mag a‖ at hx; nlinarith [norm_nonneg (mag p)]
end YM.CF.Fir
