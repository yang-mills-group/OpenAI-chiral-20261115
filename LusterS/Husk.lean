import YM.SU5.Velvet.Hemline
import LusterS.Meteor
import LusterS.Anchored
import Refrain.Foundation
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
open YM.Gleam YM.Gleam.Luster YM.Gleam.Luster.Almanac
-- Use stabilization version with ξ_D def sites
abbrev greyFee (μ:ℝ)(s:ℕ)(i k:ℕ)(x:Pane (count Y s i)):=
 let g:=gram Y s i k; let L:=P.R.L; let z:= ℶ s;
 flagCup g.p P.K.top.clip g.beta*(misdemean g.p.threshold x).card+ μ*((walls L z:ℕ):ℝ)^4*(misdemean (sax z) x).card
abbrev gFoundation (μ:ℝ)(s i k:ℕ):ℝ:=
 let A:=gram Y s i k; (∫ x:Pane (count Y s i), Real.exp (-A.path.inChannels A.funds A.p A.beta x+greyFee Y μ s i k x) ∂prior G5 (More (count Y s i)))
abbrev pressureLean (μ:ℝ)(s i k:ℕ):Prop:=
 let A:=gram Y s i k; let t:=P.V.L.H (Y.uv k-s); gFoundation Y μ s i k≤ Real.exp (Fineness.gaugedBase P.L A.beta (More (count Y s i)) t+(ℶ s)^(-yieldA)*sites (count Y s i))
theorem prong_first (μ:ℝ):∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k→ pressureLean Y μ s i k:=by
 let T:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a:=|K|
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le
 filter_upwards [(stage_slope P.V P.x).eventually (obtained P.K.top.clip R' P.L P.chart a P.R.L (V.L.mood 0).width hv V.W.bar (abs_nonneg K) μ),block_widths P] with s q H i k ht
 let N:= count Y s i; let G:=More N; let F:=Y.uv k - s; let A:= gram Y s i k
 obtain ⟨W,g,t,hW,c,r,u,hX⟩:= H (Y.ir i)
 obtain ⟨he,hT,e,f,_⟩:= prices_plot Y s i k ht
 have hV: A.p.threshold=temp (hat P.R.L P.x s):= he ▸ (Y.meter.boot s).1
 let Z:= P.V.L.H F; let Q:=V.L.path F; let Hm:=V.L.roof F
 have Hs:=q W g t hW A.p A.beta f hV G c r u hX (V.L.tied F) (V.L.mood F) (Hm.2.1 G) V.W.reserve (fun i=> (YM.Fineness.stairEstimate Z P.K.width.le Hm.1.2.1 i).trans (le_abs_self K))
 unfold pressureLean gFoundation; dsimp only; change A.path=Q at hT; change A.funds=T.top.clip at e
 unfold greyFee; dsimp only
 change (∫ x:Pane N, Real.exp (-(A.path.inChannels A.funds A.p A.beta x)+_) ∂prior G5 G) ≤ Real.exp _
 rw [e,hT]
 exact Hs.trans_eq (congrArg Real.exp (show _=_ from (by unfold Gleam.Roof Fineness.gaugedBase; rw [Pannier.shadowLie,sites_as_price])))
end Papal
end LocalLimit
end Rate
end YM.CF.Py
