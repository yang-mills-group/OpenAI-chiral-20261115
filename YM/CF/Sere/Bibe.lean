import YM.CF.Sere.Gilt
import YM.CF.Beau.Clack
import YM.Extra.WILSON_STARTUP.Clock
import YM.CF.Hype.Flash
import YM.CF.Hype.Mora
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Prism Haro Tap Oath
open Larch
-- decays compared with all plow^•
-- Canon pre & later B. clip.S separate than change.PB only B/temp. use earned β law.
open Taxi Beau AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Geo AnalyticBridge.VerifiedReset.Collection UVNext.PricedKernels Work.F03 WilsonStartup Vow
abbrev pond_X(k p:ℕ)(a:ℝ)(h0:6≤k)(h1:2≤p)(ha:0<a):BudgetPoint:=⟨p,k,a,1,1,h1,h0,ha,Nat.zero_lt_one,zero_lt_one,le_rfl⟩
variable(P_: BudgetPoint)
def upl(Y:BudgetPoint)(B:ℕ)(t:ℝ)(p:0<B)(v:0<t)(h:t ≤1):BudgetPoint:={Y with B:=B,B_pos:=p, threshold:=t, threshold_pos:=v, threshold_le:=h}
def hall_P (Z: BudgetPoint)(x:ℝ):= if h:0< radiusB x ∧ 0<temp x ∧ temp x≤1 then upl Z (radiusB x) (temp x) h.1 h.2.1 h.2.2 else Z
local notation "Θ"=> hall_P P_
variable(Ve:ℝ)
private lemma scaleW(h:0<x): temp x= WilsonStartup.Timing.temp (Real.log x):=by
 have hp : (Real.sqrt x)⁻¹=Real.exp (-(Real.log x/2)) := by
    rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos h]; congr 2; ring
 unfold WilsonStartup.Timing.temp Pressure.temp; rw [hp,Real.exp_add]
lemma purse_K (S:RG.Stage)(t:S.clip.direct≤1) :∀ᶠ x in atTop, let P:=Θ x
          P.threshold=temp x ∧ P.B=radiusB x ∧Decent S.clip P ∧ Geo.Width P S.clip S.width ∧ (P.supportExponent+1+1) / (P.B:ℝ) ≤ S.width/8 :=by
 have hp: Tendsto (fun x:ℝ=>(P_.supportExponent+1+1)/(radiusB x:ℝ)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
 have he:=S.width_pos
 filter_upwards [Real.tendsto_log_atTop.eventually (WilsonStartup.Timing.cut S.clip),hp.eventually (ge_mem_nhds (show 0<S.width/8 from by positivity)),Work.E01.radiusB_tendsto.eventually_ge_atTop 2,(sizeK.tempo (1:Side)).spine.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ)] with x p u r H y P
 unfold P hall_P; rw [dif_pos (show 0<radiusB x∧_ from ⟨(by omega),Work.E09.temp_pos y,H⟩)]
 refine ⟨rfl,rfl,⟨t,r,?_⟩,⟨S.width_pos,S.slow_selector,?_ ⟩,u⟩
 · change 2 ≤ temp x * Real.exp (((radiusB x-2:ℕ):ℝ) / S.clip.relaxation); rw [scaleW y]; exact p
 exact (le_trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)) (le_trans u (by linarith)))
lemma let_X(x:ℝ): let P:=Θ x; P.order=P_.order∧ P.power=P_.power∧P.supportExponent=P_.supportExponent:=by intro P; unfold P hall_P; split<;>exact ⟨rfl,rfl,rfl⟩
lemma hall_l :∀ᶠ x:ℝ in atTop,(hall_P P_ x).B=radiusB x:=by
 filter_upwards [Work.E01.radiusB_tendsto.eventually_gt_atTop 0,(sizeK.tempo (1:Side)).spine.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ)] with x i v t; unfold hall_P; rw [dif_pos (show 0<radiusB x∧_ from ⟨i,Work.E09.temp_pos t,v⟩)]; rfl
variable (Aχ Γχ:ℝ)(q:Clip)(σ C:ℝ)
lemma spend_T(P : BudgetPoint)(h: P.order=P_.order)(he:P.power=P_.power)(hm:P.supportExponent=P_.supportExponent): tax_E P q σ C Aχ Γχ = tax_E P_ q σ C Aχ Γχ:=by
 unfold tax_E fee_l Quotes.lowBase Quotes.highBase Quotes.anchoredFee lowFee Geo.both lowCost rowCost faceCost highFee turnFee rowDegree inS uprank priceV tollV pairBill
 rw [h,he,hm] -- tune
lemma blaze_t(P:BudgetPoint)(h:P.order=P_.order)(p:P.power=P_.power)(x:ℝ): blazeP P Γχ x=blazeP P_ Γχ x:=by unfold blazeP liteV tollV pairBill; rw [h,p]
lemma belt_p(k:ℕ) :BoreP fun x => belt_K (hall_P P_ x) k Γχ:=by
 let Y(n):= (((hinge_P n k+hinge_P n k+1)^4:ℕ):ℝ)* horn_v P_ k Γχ
 have he:BoreP fun x=>Y (radiusB x):=by
    unfold Y hinge_P; push_cast; have I_:=BoreP.radius_c
    let M:= (((BoreP.still ((k:ℝ)+81)).grip (((BoreP.still 4).grip I_).join (BoreP.still 2))).join ((BoreP.still 2).grip I_))
    exact ((((M.join M).join (BoreP.still _)).self 4).grip (BoreP.still _))
 apply he.tune; filter_upwards [hall_l P_] with x p; unfold belt_K; rw [p,show horn_v (hall_P P_ x) k Γχ= horn_v P_ k Γχ from ?_]
 obtain ⟨p,h,hv⟩:=let_X P_ x; unfold horn_v; rw [blaze_t P_ Γχ _ p h, hv]
end YM.CF.Py
