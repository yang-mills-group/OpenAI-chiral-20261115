import YM.SU5.Velvet.Hemline
import Refrain.Seismic
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
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
open BProof Refrain
-- reformulation in unshifted convention (first line of 06af Press exactly, with 1/8)
abbrev closeDen (j i k:ℕ):Prop:=
 let B':=gram Y j i k
 let g:=room Y j i
 let T:=count Y j i
 let v:=changeM P.U (1:Pane T) B'.J.M
 let d:=‖inner ℂ (mateK T) v‖
 let b:=Fineness.gaugedBase P.L B'.beta (More T) (P.V.L.H (Y.uv k-j))
 d>0 ∧ partitionZ B' P.U g ≠ 0 ∧
    Real.exp (b + Real.log d - ℶ j ^ (-(8:ℝ)⁻¹) * sites T) ≤ ‖vac0 P.U B' g‖
lemma close_denominator (q:GeometrySharp P):∀ᶠ s in atTop,∀ i k,(Y.voyage i).kick≤k→s≤Y.uv k→ closeDen Y s i k:=by
 obtain ⟨C,hC,H⟩:=benchmarksSharp Y q
 let v:=P.R.L
 have hp:∀ᶠ x:ℝ in atTop,C*shrift v x≤ x^ (-(8:ℝ)⁻¹):=by
    filter_upwards [(year G5 v).eventually (coin_budget (a:=-1/4) (b:=0) (c:=0) (d:=-(8:ℝ)⁻¹) (e:=0) (f:=0) (by norm_num) C 1 zero_lt_one),eventually_gt_atTop (0:ℝ), (year G5 v).eventually_gt_atTop 0] with x h hx hg
    let y':=y G5 v x
    have hy: x≤ y':=by
       have he: (1:ℝ) ≤ (v.val:ℝ):=by exact_mod_cast v.property
       unfold y' y betaF; exact le_add_of_nonneg_right (mul_nonneg ((Gauge.slopeConstant_pos Thera.yet_one).le) (Real.log_nonneg he))
    rw [one_mul] at h
    refine h.le.trans ?_; unfold BProof.coin; rw [mul_zero,mul_zero,add_zero,add_zero,Real.rpow_def_of_pos hx]; exact Real.exp_monotone (mul_le_mul_of_nonpos_right (Real.log_le_log hx hy) (by norm_num))
 filter_upwards [H,(stage_slope P.V P.x).eventually hp] with s hs hP i k hx h
 unfold closeDen; dsimp only
 let A:=gram Y s i k; let T:=count Y s i; let L:=changeM P.U (1:Pane T) A.J.M; let d:=inner ℂ (mateK T) L
 have hu:=P.J.gran.trans ((Y.voyage i).ownership s).size
 obtain ⟨ha,hg,h₀⟩:=angle_pay (gram Y s i k).J.M P.K.j P.U _ (by rw [P.kJ]; omega) hu P.W.health
 have hv:0<‖d‖:=norm_pos_iff.mpr ha
 have hr: Real.exp (sod Y k s i-C*shrift v (ℶ s)*sites T) ≤ ‖vac0 P.U A (room Y s i)‖:= hs i k hx h
 have hZ:‖vac0 P.U A (room Y s i)‖>0:= (Real.exp_pos _).trans_le hr
 refine ⟨hv,?_,?_⟩
 · intro H; unfold vac0 at hZ; change partitionZ A P.U (room Y s i)=0 at H; rw [H,mul_zero,norm_zero] at hZ; exact lt_irrefl _ hZ
 exact hr.trans' (Real.exp_monotone (by unfold sod entryFin; change Fineness.gaugedBase _ _ _ _+Real.log ‖d‖-_≤ Fineness.gaugedBase _ _ _ _+angleFin A.J.M T P.K.j - _; rw [(show angleFin A.J.M T P.K.j=Real.log ‖d‖ from hg)]; exact sub_le_sub_left (mul_le_mul_of_nonneg_right hP (zero_le_one.trans (sites_pos T))) _))
end Papal
end LocalLimit
end Rate
end YM.CF.Py
