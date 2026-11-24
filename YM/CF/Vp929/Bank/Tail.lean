import YM.CF.Vp929.Bank.Jug
import YM.CF.Wray.Frost
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Appel.Rate
open Function Filter Set Lattice RG Precision Pressure MeasureTheory Metric ProbabilityTheory
 AnalyticBridge.LocalGaussianLaws AnalyticBridge.Annulus1AD Next.Fluctuations Next.SectorChange Reine
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal Classical
structure Patron (a C:ℝ): Prop where
 pos : 0<a
 earns : 1≤C
 limit : ∀ v:ℝ,1≤v→let F(x:SU.group.Color):=Real.exp (a*‖x‖^2); Integrable F (Appel.feast SU.group v) ∧ (∫ i,F i∂Appel.feast SU.group v)≤ C
lemma Patron.exists : ∃ a C,Patron a C:= by obtain ⟨a,C,h,p,w⟩:= Wray.sapI; exact ⟨a,C,h,p,w⟩
variable {G:Gauge} {a C u v h t d b:ℝ} {z:ℂ}
local notation "μ" => feast G
local notation "ρ" => point G
lemma feast_skirt (ha:0≤a) (hc:(∫ i:G.Color,Real.exp (a*‖i‖^2) ∂μ v) ≤ C) (hv:0<v) (hu:0 ≤ u) :
    (μ v).real (closedBall 0 u)ᶜ ≤ Real.exp (-a*u^2)*C:= by
 haveI:= feast_nn G hv; let S: Set G.Color:=(closedBall 0 u)ᶜ; have h:MeasurableSet S:= isClosed_closedBall.measurableSet.compl
 let F(x:G.Color):=Real.exp (a*‖x‖^2); have he:Integrable F (μ v):= ((show Continuous F by unfold F; fun_prop).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).smul_measure (ENNReal.inv_ne_top.mpr (grain_pos G hv).ne')
 let D:= Real.exp (-a*u^2); let A(x:G.Color):= D*F x; have hx:0<D:=Real.exp_pos _; have fp:= he.const_mul D
 rw [show (μ v).real (closedBall 0 u)ᶜ=(∫ x,S.indicator (fun _=> (1:ℝ)) x∂μ v) from by rw [integral_indicator h,setIntegral_const,smul_eq_mul,mul_one]]; exact (integral_mono ((integrable_const _).indicator h) fp (fun x=>by
   by_cases e:x∈S
   · rw [indicator_of_mem e]; unfold D F; rw [←Real.exp_add]; apply Real.one_le_exp; have U:u<‖x‖:=lt_of_not_ge (mt mem_closedBall_zero_iff.mpr e); nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu U.le 2) ha]
   rw [indicator_of_notMem e]; exact mul_nonneg hx.le (Real.exp_pos _).le)).trans (le_trans (le_of_eq (integral_const_mul D F)) (mul_le_mul_of_nonneg_left hc hx.le))
lemma point_skirt (hv:0<v) (p:u≤v) : (μ v).real (closedBall 0 u)=ρ u/ρ v:= by unfold feast; rw [Measure.real,Measure.smul_apply,Measure.restrict_apply' isClosed_closedBall.measurableSet]; change (_⁻¹*rice G _).toReal =_; rw [inter_eq_left.mpr (closedBall_subset_closedBall p), ENNReal.toReal_mul, ENNReal.toReal_inv,mul_comm]; rfl
lemma point_mono (p:u≤v):ρ u ≤ ρ v:= measureReal_mono (closedBall_subset_closedBall p)
lemma feast_insideD (hv: u ≤ v) (p : 0<u): μ u = ENNReal.ofReal (ρ v/ρ u) • ((μ v).restrict (closedBall (0:G.Color) u)):= by
 have t:=grain_pos G p; have f:=grain_pos G (p.trans_le hv); unfold feast; rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset (closedBall_subset_closedBall hv), smul_smul]; congr 1; let y:=point G u; let x:=point G v; rw [show grainS G u=ENNReal.ofReal y from (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,show grainS G v=ENNReal.ofReal x from (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,ENNReal.ofReal_div_of_pos (point_p (G:=G) p)]; change _=ENNReal.ofReal x/ ENNReal.ofReal y* (ENNReal.ofReal x)⁻¹; have e:0<x:=point_p (p.trans_le hv); rw [div_eq_mul_inv,mul_comm (ENNReal.ofReal x),mul_assoc,ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,mul_one]
lemma rent_s (h:1-b ≤ u/v)(ha:0<v)(p:0<u)(hq:0≤b)(hp:b ≤ 1/2) : v/u ≤ Real.exp (2*b) := by
 have e:0<1-b:=by linarith
 have ht:(1-b)*(1+2*b)≥1:=by
    nlinarith
 rw [le_div_iff₀ ha] at h; apply (div_le_iff₀ p).mpr; exact (by
   rw [mul_comm (Real.exp _)]; have := Real.add_one_le_exp (2*b); nlinarith)
namespace Patron
local notation "S"=> SU.group
variable (H: Patron a C)
include H
lemma tail (u:ℝ)(hp:0≤u)(h:1≤v) : (feast S v).real (closedBall 0 u)ᶜ ≤ Real.exp (-a*u^2)*C:= feast_skirt H.pos.le (H.limit v h).2 (zero_lt_one.trans_le h) hp
lemma toll (hp:0<u)(hv:1≤v)(hu:u≤v)(hm:Real.exp (-a*u^2)*C ≤ b)(h:b≤1/2): point S v/point S u ≤ Real.exp (2*b):= by
 have p:= H.tail u hp.le hv; have e:=zero_lt_one.trans_le hv; haveI:= feast_nn S e; rw [measureReal_compl (isClosed_closedBall.measurableSet),probReal_univ,point_skirt e hu] at p
 exact rent_s (by linarith only [p,hm]) (point_p e) (point_p hp) (le_trans (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans H.earns)) hm) h
local notation "W"=> ‖z-((t^2:ℝ):ℂ)‖
local notation "J"=> jug S h
lemma tilt (hb:0≤b)(hm:b≤1/2)(e:1/2 ≤ t^2)(ha:0<t)(hp:0<h)(hh:1≤ t*h)(p: W ≤ a/2)(g:W*(2/a)*C ≤ b) : J z ≠ 0 ∧ ‖J z‖/‖J (t^2:ℝ)‖ ≤ Real.exp b ∧ ‖J (t^2:ℝ)‖/ ‖J z‖ ≤ Real.exp (2*b) := by
 have Q:= (relative_norm ha hp H.pos e p (H.limit (t*h) hh).2).trans g
 let u:= J z/J (t^2:ℝ); have U:1-b≤ ‖u‖∧‖u‖ ≤ 1+b:=by
   have := norm_sub_norm_le (1:ℂ) (u);
   have p := norm_add_le (1:ℂ) (u-1); change ‖u-1‖ ≤ b at Q; rw [norm_one,norm_sub_rev] at this; rw [show (1:ℂ)+(u-1)=u from by ring,norm_one] at p; constructor<;> linarith
 have hp':0<‖u‖:=by linarith [U.1]
 have hv:J z≠0:= fun h=> (norm_pos_iff.mp hp') (by unfold u; rw [h,zero_div])
 have I:J (t^2:ℝ)≠0:=fun h=>(norm_pos_iff.mp hp') (by unfold u; rw [h,div_zero])
 unfold u at *
 rw [norm_div] at U; exact ⟨hv,U.2.trans (by linarith [Real.add_one_le_exp b]), rent_s U.1 (norm_pos_iff.mpr I) (norm_pos_iff.mpr hv) hb hm⟩
end Patron
end YM.CF.Appel.Rate
