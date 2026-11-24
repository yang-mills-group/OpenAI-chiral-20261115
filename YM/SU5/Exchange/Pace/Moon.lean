import YM.SU5.Exchange.Reg.RateMargin
import YM.CF.Roots.Cane
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open YM.CF.BPress (PL NPL)
variable {F G:ℝ→ℝ}
lemma PL_par(F:ℝ→ℝ)(p:Tendsto F atTop (𝓝 0)):PL F:= (PL.const 1).mono (p.abs.eventually (ge_mem_nhds (by simpa: |(0:ℝ)|< |(1:ℝ)|)))
lemma PL_radiusX : PL (fun x:ℝ=>(radiusB x:ℝ)):=by refine PL.scale.mono (Eventually.of_forall fun i=>?_); rw [abs_of_nonneg (zero_le_one.trans (BPress.lscale_one _)),abs_of_nonneg (Nat.cast_nonneg (radiusB i))]; exact le_add_of_nonneg_left zero_le_one
lemma PL_spanV: PL (fun x:ℝ=>Sour.spanV (radiusB x)):=by
 let a(x:ℝ):ℝ:= radiusB x; have hx:=((PL_radiusX.add PL_radiusX).add (PL.const 1)).pow 4; exact hx.mono (Eventually.of_forall fun i=> by unfold Sour.spanV; simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_one]; rfl)
-- toll= Q clock with maybe Y delta. compare.Manual sticks exact
local notation "P♣"=> SU.group
abbrev pinpr (R : Side)(x:ℝ) :=Scales.g SU.group R x^2
variable (R:Side)
local notation "ω"=> BPress.drift
local notation "∆"=> Scales.g SU.group R
lemma draft_π :∀ᶠ x:ℝ in atTop, 0<x ∧ 0<∆ x ∧ ∆ x ≤ (BPress.g x) ∧ BPress.g x ≤ 2*∆ x ∧ (pinpr R x=∆ x^2):=by
 let A:= P♣.slopeConstant*Real.log R.val; have hg: 0≤A:=mul_nonneg (Work.E07.slope_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr R.property))
 filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop A] with x hx e
 have hp:x+A>0:=by linarith
 let u:= x+A; have ht:∆ x=BPress.g u:=rfl
 rw [ht]; refine ⟨hx,BPress.g_pos hp,inv_anti₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt (le_add_of_nonneg_right hg)),?_,congrArg (fun g:ℝ=>g^2) ht⟩
 have h1:= BPress.gscale hp.le; have h2:= BPress.gscale hx.le
 have h3:x⁻¹ ≤ 2*(x+A)⁻¹:=by rw [←one_div,←div_eq_mul_inv]; rw [div_le_div_iff₀ hx hp]; nlinarith
 unfold u; nlinarith only [h1,h2,h3,BPress.g_pos hx,BPress.g_pos hp]
lemma nq : NPL (pinpr R):=by
 refine (BPress.npl_g.mul BPress.npl_g.pl).mono ?_
 filter_upwards [draft_π R] with x hx; obtain ⟨_,u,z,H,k⟩:=hx; rw [k,sq]; simp only [abs_mul,abs_of_pos u,abs_of_pos (u.trans_le z)]
 exact mul_le_mul z z u.le (u.trans_le z|>.le)
lemma dirP: NPL (dleaf R):=by
 refine (BPress.npl_g.mul BPress.npl_temp.pl).mono ?_
 filter_upwards [draft_π R] with x hx; obtain ⟨_,u,z,H,k⟩:=hx; simp only [dleaf,abs_mul,abs_of_pos u,abs_of_pos (u.trans_le z)]
 exact mul_le_mul_of_nonneg_right z (abs_nonneg _)
local notation "w"=> BPress.drift
abbrev stemS (x:ℝ):= (w x)^((1:ℝ)/4)
abbrev hueW (x:ℝ):ℝ:= pinpr R x/(temp x)^2 * stemS x
lemma coolQ : NPL (hueW R):=by
 let f(x):=(w x)^((1:ℝ)/4)
 refine (BPress.npl_drift (1:ℝ) zero_lt_one).mono ?_
 filter_upwards [draft_π R] with x hx; obtain ⟨hz,u,p,l,k⟩:=hx; let y:= pinpr R x ; let r:= w x; have hr:1≤r:=BPress.drift_one _
 have hh:0<BPress.g x:=u.trans_le p; have hs:0<r:=zero_lt_one.trans_le hr
 have ht: y ≤ BPress.g x^2:=pow_le_pow_left₀ u.le p _; rw [hueW,BPress.temp_eq, Real.rpow_one]; have h(f:ℝ)(h:f ≤ r)(hl:0 ≤ f): |y/(BPress.g x*r)^2*f| ≤ |r⁻¹|:=by
    rw [abs_of_pos (inv_pos.mpr hs),abs_of_nonneg (show 0 ≤ y/(BPress.g x*r)^2*f from mul_nonneg (div_nonneg (by rw [show y= _ from k]; positivity) (by positivity)) hl)]
    refine (mul_le_mul (div_le_div_of_nonneg_right ht (by positivity)) h hl (by positivity)).trans_eq ?_; field_simp -- ring
 exact h (stemS x) (show r^((1:ℝ)/4)≤r from (Real.rpow_le_rpow_of_exponent_le hr (show (1:ℝ)/4 ≤ 1 by norm_num)).trans_eq (Real.rpow_one _)) (Real.rpow_nonneg hs.le _)
lemma coolDivPiece:NPL (fun x=> hueW R x*dleaf R x/ pinpr R x):=by
 refine (BPress.npl_drift ((1:ℝ)/2) (by norm_num)).mono ?_
 filter_upwards [draft_π R] with x hx; obtain ⟨hx,v,p,l,k⟩:= hx; have hp: (w x)≥1:=BPress.drift_one _; let b:=w x; have hs:b≥1:=hp; have hu:0<b:=zero_lt_one.trans_le hs; let D:= BPress.g x; let Y:= ∆ x; have hv :0 < Y:= v; have hz :0<D := v.trans_le p; let W:= hueW R x; have hk: W*(Y*temp x)/pinpr R x= Y / (D*b) * b^((1:ℝ)/4):=by unfold W hueW; rw [k,BPress.temp_eq]; unfold D Y b stemS; field_simp
 rw [dleaf,hk]; rw [abs_of_pos (show 0<Y/(D*b)*_ from mul_pos (div_pos hv (mul_pos hz hu)) (Real.rpow_pos_of_pos hu _)),abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos hu _))]; apply le_trans (b:=D/(D*b)*b^((1:ℝ)/4)); gcongr
 change D / (D*b)* _ ≤ (b^((1:ℝ)/2))⁻¹
 rw [div_mul_eq_div_div,div_self hz.ne',one_div]; apply (le_inv_comm₀ (by positivity) (by positivity)).mpr -- order?
 rw [mul_inv_rev, inv_inv]; apply (le_inv_mul_iff₀ (by positivity)).mpr; rw [←Real.rpow_add hu]; exact (Real.rpow_le_rpow_of_exponent_le hs (show (1:ℝ)/4+1/2 ≤1 by norm_num)).trans_eq (Real.rpow_one _)

-- C e^{-a floor(b/10)} exposes superpython in x.Couple.B threshold.h
lemma tailω (a:ℝ)(m:ℕ)(hp:0<a)(u:1 ≤ m) : NPL (fun x=> hueW R x* Real.exp (-a*((radiusB x /m:ℕ):ℝ)) / pinpr R x):=by
 let f(x:ℝ):= Real.exp (-a*((radiusB x /m:ℕ):ℝ)); have hZ: ∀ᶠ x:ℝ in atTop,f x ≤ x⁻¹^2:=by
    let z:ℝ:=m; have hk:1 ≤ z:= Nat.one_le_cast.mpr u
    let L(x:ℝ):ℝ:= radiusB x / m -- careful division Nat? annotate
    filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2*z/a+z+a*z+1)] with x hx h
    let A:= (Real.log x)^2; have hv:A ≤ (radiusB x:ℝ):= Nat.le_ceil _; let M:=radiusB x; let k:= M/m
    have hu:(M:ℝ)≤ z*((k:ℝ)+1):=by unfold z; norm_cast; exact Nat.le_of_lt (Nat.lt_mul_div_succ M (show 0 < m from u)) -- lemma check
    have he: x⁻¹=Real.exp (-Real.log x):=by rw [Real.exp_neg, Real.exp_log hx]
    rw [he,sq,←Real.exp_add]; apply Real.exp_monotone; let l:=Real.log x; have h':2*z/a+z+a*z+1 ≤ l:=h
    have hT: 0 ≤ 2*z/a:=by positivity
    have hU:0<z:=zero_lt_one.trans_le hk
    have hf: l ≥ a*z:=by linarith
    have ho: l≥ 2*z/a+1:=by nlinarith
    have H: l≥z:=by nlinarith
    have hg: (2*z/a)*a=2*z:=by field_simp; -- tune
    change -a* (k:ℝ) ≤ -l+-l
    apply le_of_mul_le_mul_right _ (show 0<z by linarith); have ha:=mul_le_mul_of_nonneg_left (hv.trans hu) hp.le; unfold A at ha; change a*l^2 ≤ _ at ha; have hy:=mul_le_mul_of_nonneg_left (show 2*z/a+1 ≤ l from ho) hp.le; nlinarith -- tune
 refine (coolQ R).mono ?_; filter_upwards [hZ,draft_π R,eventually_ge_atTop (5:ℝ)] with x h u t; obtain ⟨hx,v,g,p,k⟩:=u
 let q:= pinpr R x; have hp:0<q:=by unfold q; rw [k]; positivity
 change |_* f x / q|≤ _
 rw [abs_div, abs_mul,abs_of_pos hp, abs_of_pos (show 0<f x from Real.exp_pos _), div_le_iff₀ hp]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply h.trans
 let V:=BPress.g x; have he:V^2=x⁻¹:= BPress.gscale hx.le; let U:=∆ x; have ht: V ≤ 2*U:=p
 have hH: x⁻¹ ≤ (5:ℝ)⁻¹:= inv_anti₀ (by norm_num) t; have hq: x⁻¹ ≤ 4*q:=by unfold q; rw [k,←he]; exact le_trans (pow_le_pow_left₀ (show 0 ≤ V from (BPress.g_pos hx).le) ht 2) (le_of_eq (by unfold U; ring))
 rw [sq]; nlinarith only [mul_le_mul hq hH (inv_nonneg.mpr hx.le) (show 0≤4*q by positivity),hp]
end YM.CF.Py
