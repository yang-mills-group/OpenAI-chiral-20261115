import Refrain.Shrift
import YM.SU5.Fineness.Frank
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Matrix Finset CF CF.Newt Pressure
open scoped Matrix Matrix.Norms.Frobenius BigOperators
open Filter Lattice RG Precision Tree Forge FreeResolvent PhysicalNext.JointLoad.Heir
open Next Next.Fluctuations Next.SectorChange
open AnalyticBridge.LocalGaussianLaws
open scoped Classical Topology Kronecker
local notation "G"=>SU.group
variable {K:Teller SU.group}{R:Patch}{m n:Side}(S:StepData m n)(M:Monk SU.group S){x η δ:ℝ}
local notation "g'"=> Affine.headGap G R K.bind K.top.clip
local notation "β'" => Fintype.card (Site n)
local notation "Zm"=> Fintype.card SU.group.ColorIndex
variable (ε:ℝ) (U: Tube SU.group S)(H:Bed)
local notation "H'"=> Neige.baseX U x (Corne.kist M).key (Corne.kist M).park (Corne.kist M).k 1
local notation "G₀"=> treeMatrix G S M.park H.metric
local notation "C0"=> K.top.paths
local notation "W0"=> K.top.width
open CF.Refrain CF.Fief SectorNext.Remainder
lemma porch_shrift (K:Teller SU.group)(R:Patch)(p:0<ε) : ∀ᶠ x in atTop,∀ {m n:Side}(S:StepData m n)(M:Monk SU.group S)(U:Tube SU.group S)(H:Bed){η δ:ℝ},Floor H K.top.clip n η δ→Attached H U.up→ Bid.Sworn H n SU.group→ Newt.Cert R K S U x→ |Corne.arcD U x M+(1/2:ℝ)*Real.log (treeMatrix G S M.park H.metric).det| ≤ (ε* shrift R.L x)* Fintype.card (Site n):=by
 let k:= Affine.headGap SU.group R K.bind K.top.clip; have he:0<k:= Affine.headGap_pos ..
 let c:ℝ:=2*(Fintype.card SU.group.ColorIndex:ℝ); have hc:0≤c:=by unfold c; positivity
 let w:= K.top.width/4
 have hw:0<w:=div_pos K.top.width_pos (by norm_num)
 let a:=ozPay R K.bind K.top.width K.top.paths SU.group
 have hf:sizeK R.L 1 temp:=by
    have h:∀ᶠ x:ℝ in atTop,|temp x| ≤|2*(Scales.g SU.group R.L x*Scales.p SU.group R.L x)|:=by
       filter_upwards [YM.Work.E07.temp_coarse_le SU.group R.L,eventually_gt_atTop (0:ℝ)] with x v e
       rw [abs_of_pos (YM.Work.E09.temp_pos e),←Scales.fi]; exact v.trans (le_abs_self _)
    exact (((sizeK.main R.L).tint (sizeK.height R.L)).scale 2).cost_d h
 filter_upwards [Newt.smallF (n:=1) hw a, cleared R.L ε (c/k) hf (by norm_num) p] with x hp ht m n S M U H η δ p q e t; rw [pow_one] at hp; rw [mul_comm (ε* shrift ..)]; refine (porch S M U H p q e t).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
 change c*((Real.exp (-w*Stores.till x)*a)/k)≤ _
 exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hp.trans (le_abs_self _)) he.le) hc).trans ((by rw [←show c/k*|temp x| = c*(|temp x|/k) from by ring]; exact ht) : c*(|temp x|/k) ≤ ε*shrift R.L x)
end YM.Fineness
