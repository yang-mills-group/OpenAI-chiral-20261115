import YM.CF.Char.Parme
import YM.CF.Char.Velvet
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor
variable {t ε τ:ℝ}{n:ℕ}
def mount(b:G.Color× G.Color):G.Color := G.plog (G.mat (G.lieExp b.1 * G.lieExp b.2))
@[simp] lemma mount_zero : mount (0 : G.Color × G.Color)=0:=by simp [mount]
lemma pass_n (G: Gauge)(n:ℕ)(hn:1 ≤ n): ∃ ε D:ℝ,0<ε∧0<D∧∀{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (p:E→ G.Color)(x:E)(s), 0<s → s ≤ ε → Allows n p x s → ∀ a:G.Color, ‖a‖ ≤  s→
 Allows n (fun y=> mount (p y,a)) x (D*s) ∧ ∀ᶠ y in 𝓝 x, G.lieExp (mount (p y,a))=G.lieExp (p y)*G.lieExp a:=by
 let g(a:G.Color×G.Color):= G.lieExp a.1 * G.lieExp a.2
 have hg : Continuous g := (G.lieExp_cont.comp continuous_fst).mul (G.lieExp_cont.comp continuous_snd); have hG : g 0=1:=by simp [g]
 let U:= G.mat ∘ g; have hU:ContDiffAt ℝ ω U 0:=by
    unfold U Function.comp g; simp_rw [G.mat_mul]; exact (((G.exp_jet).comp contDiff_fst).mul ((G.exp_jet).comp contDiff_snd)).contDiffAt
 have h :ContDiffAt ℝ ω (mount (G:=G)) 0 := (show ContDiffAt ℝ ω G.plog (U 0) from (show U 0=1 from by simp only [U,Function.comp_apply,hG,G.mat_one]).symm ▸ G.plog_diff).comp _ hU
 have he : ∀ᶠ y in 𝓝 (0:G.Color × G.Color), G.lieExp (mount y)=g y := ((show Tendsto g (𝓝 0) (𝓝 1) by rw [← hG]; exact hg.tendsto _).eventually G.plog_right)
 obtain ⟨r,hr,hh⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp ((h.eventually (by simp)).and he)
 obtain ⟨C,hC,hP⟩:= Push.Uniform.exists_allows (isCompact_closedBall _ _) (fun i (hi:i∈closedBall (0:G.Color× G.Color) r)=> (hh hi).1) n
 let D:= composeCost n C 1; refine ⟨min (r/2) 1,max 1 D,lt_min (half_pos hr) zero_lt_one,lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
 intro E _ _ _ p x s hs hB hp a ha
 let P(y):=(p y,a); have hK:Allows n P x s:= hp.pair (allows_const x ha)
 have hz:‖P x‖ ≤ s:= hK.value; have ht:s<r:=(hB.trans (min_le_left ..)).trans_lt (half_lt_self hr)
 have hu: Allows n (fun y:G.Color × G.Color=> mount (s•y)) ((s⁻¹:ℝ)•P x) (C*s):=by
    have he := near_s (n:=n) (f:=mount (G:=G)) hs.le (hB.trans (min_le_right ..)) hn ht (fun i hi=> (show Allows n mount i C from let p:= hP i (mem_closedBall_zero_iff.mpr hi.le); ⟨p.1.of_le le_top,p.2⟩)) (x:=s⁻¹•P x) ?_
    · simpa only [mount_zero,sub_zero] using he
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]; exact (mul_le_mul_of_nonneg_left hz (inv_pos.mpr hs).le).trans_eq (inv_mul_cancel₀ hs.ne')
 have hv:= hK.smul s⁻¹; rw [abs_of_pos (inv_pos.mpr hs),inv_mul_cancel₀ hs.ne'] at hv
 refine ⟨((hu.comp (f:=(fun u=>s⁻¹ • P u)) hv).mono ((show composeCost n (C*s) 1 = D*s from by unfold D composeCost; ring).trans_le (mul_le_mul_of_nonneg_right (le_max_right ..) hs.le))).germ (Eventually.of_forall fun y=> by dsimp only; rw [smul_inv_smul₀ hs.ne']),?_⟩
 filter_upwards [hK.smooth.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hz.trans_lt ht)))] with y hy; exact (hh (ball_subset_closedBall hy)).2
end YM.CF.Char
