import ForceSatin.FormPrice
import ForceSatin.Normalize
set_option autoImplicit false
set_option maxHeartbeats 520000
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x

-- Choose unscaled prices once. Q-dose X^(-50u), u=.000001;
-- temptations in PA budgets always post. assumptions grade-zero use
-- slack u*1/2 in **total** coefficients.
abbrev micr : ℝ := 1/(1000000:ℝ)
abbrev truncExp : ℝ := 20*micr
def forceDose (x:ℝ):=x^(-(50*micr))
def pencilPrice (x:ℝ):= x^(-(49.5*micr))
def formTill (x:ℝ):= x^(-(54*micr))
def integralTill (x:ℝ):= x^(-(53.5*micr))
def poseTill (x:ℝ):= x^(20*micr)
def truncateStep (x:ℝ):ℕ:= Nat.ceil (x^truncExp)
def curveOp (x:ℝ):= tiltCost*(1+ (truncateStep x:ℝ))
def curveDiscard (c x:ℝ):= tiltCost*Real.sqrt (c*(x^(-truncExp/2)))

theorem trunc_pay (c:ℝ)(p:0≤c)(x:ℝ)(u:1≤x):
    tiltCost*Real.sqrt (c*(Real.sqrt (truncateStep x:ℝ))⁻¹) ≤ curveDiscard c x := by
  have h:x>0:=zero_lt_one.trans_le u
  let k:=truncateStep x
  have hk: x^truncExp ≤ (k:ℝ):=Nat.le_ceil _
  have hz:(0:ℝ)<k := (Real.rpow_pos_of_pos h _).trans_le hk
  apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ p)) (Real.exp_pos _).le)
  have he:x^(-truncExp/2)= (Real.sqrt (x^truncExp))⁻¹:=by
    rw [neg_div, Real.rpow_neg h.le]; congr 1; rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h.le]; ring_nf
  rw [he]; exact inv_anti₀ (by positivity) (Real.sqrt_le_sqrt hk)

lemma form_margin {m:ℕ}(c B:ℝ)(p:0≤c) : ∀ᶠ x:ℝ in atTop,
    pencilPrice x * B^m ≤ 1/2 ∧ stack m (curveDiscard c x) (pencilPrice x) (curveOp x) B +
     2*(pencilPrice x*B^m)^2 ≤ formTill x:=by
  have hc:Grade (-(49.5*micr)) pencilPrice:= Grade.pitch _
  have hv: Grade truncExp curveOp:= Grade.scaleB tiltCost (((Grade.block _).grow (by norm_num [truncExp,micr])).plus (Grade.ceil_float (Grade.pitch _) ((eventually_ge_atTop (1:ℝ)).mono fun x (h : (1:ℝ) ≤ x)=> Real.rpow_nonneg (zero_le_one.trans h) _) (by norm_num [truncExp,micr])))
  have hx:Grade (-(5*micr)) (curveDiscard c):=by
    apply Grade.cash (Grade.scaleB (tiltCost*Real.sqrt c) (Grade.pitch (-(5*micr))))
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x h; apply le_of_eq; congr 1
    unfold curveDiscard; rw [Real.sqrt_mul p, ←mul_assoc, Real.sqrt_eq_rpow (x:= (x^(-(truncExp)/2):ℝ)),←Real.rpow_mul h.le]; norm_num [truncExp,micr,div_eq_mul_inv]
  let Y(x):= pencilPrice x*B^m; have hy: Grade (-(49.5*micr)) Y:=by simpa only [add_zero] using hc.mul (Grade.block _)
  let θ:ℝ:= -(54.5*micr); let t:= fun x=> stack m (curveDiscard c x) (pencilPrice x) (curveOp x) B + 2*(Y x)^2
  have he:Grade θ t:= by
    have h₁:= ((hv.mul hc).mul (Grade.block (normalCost B m))).pwr 2
    have h₂:= hc.mul ((Grade.scaleB ((2:ℝ)*m) hx).mul (Grade.block (B^m)))
    have h₃:= Grade.scaleB (2:ℝ) (hy.pwr 2)
    exact ((h₁.grow (by norm_num [micr,truncExp,θ])).plus (h₂.grow (by norm_num [micr,θ]))).plus (h₃.grow (by norm_num [micr,θ]))
  filter_upwards [he.cost_p (b:=-(54*micr)) (by norm_num [θ,micr]),(hy.roots (by norm_num [micr])).eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2))] with x H hx; exact ⟨hx,(le_abs_self _).trans H⟩

lemma distance_margin : ∀ᶠ x:ℝ in atTop, formTill x + 5*parcelF x * poseTill x ≤ integralTill x:=by
  let q:ℝ:= -(54*micr); have hp:= (Grade.pitch q).plus ((Grade.scaleB 5 (Grade.pitch (-claimV)) |>.mul (Grade.pitch (20*micr))).grow (b:=q) (by norm_num [q,claimV,ratioV,tauA,micr]))
  exact (hp.cost_p (b:=-(53.5*micr)) (by norm_num [micr,q])).mono (fun i h=> (le_abs_self _).trans h)

end Papal
end LocalLimit
end Rate
end YM.CF.Py
