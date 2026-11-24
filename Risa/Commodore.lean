import Risa.Verdant
import Risa.Snag
import Risa.Variance
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
open Almanac CF.BProof
variable (Qh:Hike) (y:ℝ)(Rs:Rules G)(Lc:Side)
local notation "φ" => scaleY
noncomputable abbrev heightH(A:ℕ):ℕ:= 2*A+100
noncomputable abbrev hatch(A:ℕ)(x:ℝ):Hike:= ⟨scaleY x^heightH A, pow_pos (coin_pos ..) _⟩
noncomputable def capacityS(A:ℕ)(x:ℝ):ℕ:= ⌈(φ x)^(24*heightH A)⌉₊
lemma reaches(d:ℕ)(x:ℝ):0< capacityS d x:= Nat.ceil_pos.mpr (pow_pos (coin_pos ..) _)
noncomputable def sock(A:ℕ)(x:ℝ):ℝ:= (φ x)^A/(capacityS A x:ℝ)
-- public profile.AERC. reserve errors per Tile
lemma summitT(x:ℝ):1≤ scaleY x:=by rw [coin_scale]; exact Real.one_le_exp (sq_nonneg _)
lemma summitG:Tendsto scaleY atTop atTop:= by
 simp_rw [funext coin_scale] -- coin_scale states x
 have h:= (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop); exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (α:=ℝ) (by norm_num:(2:ℕ)≠0)).comp h)
noncomputable abbrev coronaS(R:Rules G)(u:ℝ)(k:ℕ):= (G.colorScale*16+R.C*4 +8*G.colorScale*(k:ℝ))*u^2
private lemma slot_equal {u:ℝ}(R:Rules G){k:ℕ}: slotError R k u = coronaS R u k:=by unfold slotError faceCutError coronaS; ring
lemma sqrt_grade0:Almanac.Grade (1/2) (fun x:ℝ=> Real.sqrt x):=by simpa only [Real.sqrt_eq_rpow] using Grade.pitch (1/2)
lemma clockτ{x:ℝ}(h:0<x):|Real.sqrt x| * temp x=φ x:=by unfold temp; rw [abs_of_pos (Real.sqrt_pos.mpr h),←mul_assoc,mul_inv_cancel₀ (Real.sqrt_pos.mpr h).ne',one_mul,coin_scale]
-- numerator eventual .η debt λ. theorem sunFee with D. 
lemma foliage (A:ℕ): ∀ᶠ x:ℝ in atTop, ∀ p:BudgetPoint,p.threshold=temp x→
 sunFee (hatch A x) Rs (Real.sqrt x) p (v:=tuition Lc x) * (φ x)^heightH A ≤1:=by
 let h:=heightH A; let w(x:ℝ):=hatch A x
 let g:ℕ:= ridges; let b:ℕ:=(posess G (hatch A 0)).payroll
 let M(x:ℝ):= Real.sqrt x
 let W(x:ℝ):= φ x^h; let E(x:ℝ):= coronaS Rs (tuition Lc x) b
 let Q(x:ℝ):= (((g:ℝ)*2*W x)*(M x)*E x)*W x
 have hW:Grade (0:ℝ) W:=by apply Grade.grow ((Grade.stock 0 1).pwr h); linarith
 have hE: Grade ((-2/5:ℝ)*2) E:= Grade.scaleB _ (tuition_b Lc|>.pwr 2) |>.grow (by norm_num) -- syntax
 have hp:= (Grade.mul (Grade.mul (Grade.mul (hW.scaleB ((g:ℝ)*2)) sqrt_grade0) hE) hW).roots (by norm_num)
 filter_upwards [hp.eventually (le_mem (b:=1/2)),eventually_gt_atTop (0:ℝ),summitG.eventually_ge_atTop (max 2 (2*ridges):ℝ)] with x he t u p e -- le_mem?
 have h₀:0< W x:= pow_pos (coin_pos ..) _; have hg:2≤φ x:=le_trans (le_max_left ..) u
 have hv := clockτ t
 have hσ: Etch.priceS (posess G (w x)) Rs (M x) (tuition Lc x)=((g:ℝ)*2*W x*(M x)*E x):=by unfold Etch.priceS; rw [slot_equal,abs_of_nonneg (Real.sqrt_nonneg _)]; rfl
 unfold sunFee; rw [e,hv,show Etch.priceS _ _ _ _ =_ from hσ]
 change (g *2*W x*M x*E x +(W x)⁻¹ ^2 *(↑g*(φ x)^4))*W x≤1 -- g Nat cast
 change Q x ≤ 1/2 at he
 have hb:5 ≤ h:= by unfold h heightH; omega
 have hs:φ x* (φ x)^4 ≤W x:=by unfold W; rw [mul_comm, ←pow_succ]; exact pow_le_pow_right₀ (by linarith) hb
 have hz:2*(g:ℝ) ≤ φ x:=le_trans (le_max_right ..) u
 have ht: 2*((g:ℝ)* (φ x)^4) ≤ W x:=(show _≤ φ x*(φ x)^4 from (by nlinarith only [mul_le_mul_of_nonneg_right hz (show 0≤(φ x)^4 by positivity)]))|>.trans hs
 have hu:(W x)⁻¹ ^2*((g:ℝ)* (φ x)^4)*W x≤1/2:=by field_simp; linarith only [ht] -- field_simp cancels W.
 unfold Q at he; linarith only [hu,he]
where le_mem{b:ℝ}(u:0 < b := by norm_num) : ∀ᶠ x in 𝓝 (0:ℝ), x ≤ b := ge_mem_nhds u
#check Real.tendsto_log_atTop
end Risa
end YM.Gleam.Luster
