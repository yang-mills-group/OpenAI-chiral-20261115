import YM.SU5.Fineness.Inches
import SatinThinLaplace

set_option autoImplicit false
set_option maxHeartbeats 579000
noncomputable section
namespace YM.CF.Appel
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open Set Topology
open SectorNext.Vacuum
set_option linter.unusedSimpArgs false

lemma flurry_mass (G:Gauge) : ∃ L>(0:ℝ), ∀ t>(0:ℝ), 0 ≤ 1-point G t ∧ 1-point G t ≤ L*Real.exp (-t^2/4):=by
 let v:= Gaussian.dome G.ColorIndex
 have hv:0<v:=Gaussian.dome_pos
 let F(x:G.Color):= v⁻¹*Real.exp (-(1/4:ℝ)*‖x‖^2)
 have h x : 0≤F x:= mul_nonneg (inv_pos.mpr hv).le (Real.exp_pos _).le
 have hf:Integrable F:= (fire_integrable G (by norm_num:(0:ℝ)<1/4)).const_mul v⁻¹
 let C:= ∫ x,F x; have hx:0≤C:= integral_nonneg h
 refine ⟨C+1,by linarith,fun t ht=>?_⟩
 let Q:= closedBall (0:G.Color) t; let e:=Real.exp (-t^2/4); let s' := rice G
 have hQ:MeasurableSet Q:= isClosed_closedBall.measurableSet
 have he:0<e:=Real.exp_pos _
 have u: s'.real Qᶜ = 1-point G t:=by
    rw [measureReal_compl hQ,probReal_univ] -- tune
    rfl
 rw [←u]; refine ⟨ENNReal.toReal_nonneg,?_⟩
 calc _= ∫ x, Qᶜ.indicator (peakG G) x := by
        rw [integral_indicator hQ.compl]; -- either from integral_map_density or .real complement
        have hM :Measurable (fun x:G.Color=>ENNReal.ofReal (peakG G x)):=by unfold peakG; fun_prop
        unfold s'; rw [perk]
        -- tune
        rw [←setIntegral_one_eq_measureReal]
        rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hM _ _ hQ.compl] -- tune
        apply setIntegral_congr_fun hQ.compl; intro x hx
        dsimp only; rw [ENNReal.toReal_ofReal (by exact mul_nonneg (inv_nonneg.mpr hv.le) (Real.exp_pos _).le),smul_eq_mul,mul_one]
        filter_upwards with x; exact ENNReal.ofReal_lt_top
      _ ≤ ∫ x,e * F x:= by
        apply integral_mono_of_nonneg -- no need integrability of g? tune
        · filter_upwards with x; exact (indicator_nonneg (fun x _=> mul_nonneg (inv_nonneg.mpr hv.le) (Real.exp_pos _).le)) x
        · exact hf.const_mul e
        filter_upwards with x
        by_cases p : x∈Qᶜ
        · rw [indicator_of_mem p]; unfold F; rw [mul_left_comm]; unfold peakG v; apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hv.le); rw [show e= Real.exp _ from rfl,← Real.exp_add]; have hr: t < ‖x‖:= by simpa [Q] using p
          apply Real.exp_monotone; nlinarith only [pow_le_pow_left₀ ht.le hr.le 2]
        rw [indicator_of_notMem p]; exact mul_nonneg he.le (h _)
      _ ≤ _:= by rw [integral_const_mul]; change e*C ≤ (C+1)*e; linarith
end YM.CF.Appel

namespace YM.SectorNext.Remainder.Scales
open Filter Function Asymptotics Lattice RG Wilson Pressure MeasureTheory
open CF Skye -- shadow
open scoped Topology Matrix BigOperators ContDiff Classical
open Next.Scheduling.Clock
open CF.Fief

local notation "G5" => SU.group
/-- several polynomial (in g) rates. Merit is ~ X^(-1/4). -/
def merit (L:Side)(x:ℝ) := Real.sqrt (g SU.group L x)
theorem merit_pos (L:Side){x:ℝ}(h:y G5 L x>0): 0< merit L x:=Real.sqrt_pos.mpr (gauge _ _ h)
theorem earning (L:Side)(n:ℕ) : Tendsto (fun x=> p G5 L x^n * merit L x) atTop (𝓝 0):=by
 have h:= tally_price G5 L 0 n (a:=1/2) (by norm_num)
 simp_rw [pow_zero,one_mul,← Real.sqrt_eq_rpow] at h; exact h
theorem scant (L:Side): Tendsto (merit L) atTop (𝓝 0):= by simpa only [pow_zero,one_mul] using earning L 0

lemma merit_size (L:Side)(u:ℝ)(t:0<u)(f:ℝ→ℝ)(p:sizeK L 1 f) : ∀ᶠ x in atTop, |f x|≤u*merit L x := by
 obtain ⟨m,h⟩:=p; filter_upwards [(earning L m).eventually (ge_mem_nhds t),year G5 L|>.eventually_gt_atTop 0,h] with x hp hv v
 refine v.trans ?_; rw [pow_one]; let E:=merit L x; have ht:E^2=g G5 L x:=Real.sq_sqrt (gauge _ _ hv|>.le); rw [← ht]; change _ ≤ u*E; change _*E ≤ u at hp
 exact le_trans (le_of_eq (show E^2* Scales.p G5 L x^m = (Scales.p G5 L x^m * E)*E from by ring)) (mul_le_mul_of_nonneg_right hp (merit_pos L hv).le)

theorem shot_sight (L:Side)(b C:ℝ)(hb:0<b)(pL:0<C)(v:ℝ)(hv:0<v): ∀ᶠ x:ℝ in atTop,C * Real.exp (-b*p SU.group L x^2) ≤ v*merit L x := by
 have hr:= ((burnt (-1) b 2 2 hb one_lt_two zero_lt_two).comp (year G5 L)).const_mul C
 rw [mul_zero] at hr; filter_upwards [hr.eventually (ge_mem_nhds hv),year G5 L|>.eventually_gt_atTop 0,(minute G5 L).eventually (ge_mem_nhds zero_lt_one)] with x h hg e; let r:= p G5 L x; let A:= Real.exp (-b*r^2); let w:=g G5 L x
 have h': C*(w^ (-(1:ℝ))*Real.exp (-b*r^(2:ℝ))) ≤ v:= h; have hw:0<w:=gauge _ _ hg; rw [Real.rpow_two,Real.rpow_neg hw.le,Real.rpow_one,←div_eq_inv_mul] at h'; rw [←mul_div_assoc] at h'
 exact ((div_le_iff₀ hw).mp h').trans (mul_le_mul_of_nonneg_left (show w≤ merit L x by rw [show merit L x=Real.sqrt w from rfl,Real.le_sqrt hw.le hw.le]; nlinarith only [hw,show w ≤ 1 from e]) hv.le)
end YM.SectorNext.Remainder.Scales
