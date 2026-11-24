import SatinThinAtlas
import SatinThinSkyward
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open Gleam.Tempest Worth 
namespace Papal
abbrev xhood (s:ℕ):ℝ:=hat P.R.L P.x s
local notation "Bq" t:max y:max=> P.K.top.clip.linear*t*y/4 -- delete

def frost_bill (s i k:ℕ)(x:ℝ)(κ k':ℝ) (V:Pane (count Y s i)):= let G:= gram Y s i k; Real.exp (-(G.path.inChannels G.funds G.p G.beta V)+κ*Pannier.flakes G.p.threshold V+k'*Pannier.flakes (shieldC x) V)
abbrev freeR (s i k:ℕ)(κ:ℝ): Prop:= κ ≤ (gram Y s i k).beta*unitDueS P.K.top.clip (gram Y s i k).p/2
abbrev coolR (s i k:ℕ)(k':ℝ) : Prop:= k' ≤ Gleam.Tempest.empress P.K.top.clip (gram Y s i k).beta (xhood (P:=P) s)
abbrev gBaseR (s i k:ℕ):= Fineness.gaugedBase P.L (gram Y s i k).beta (More (count Y s i)) (P.V.L.H (Y.uv k-s)) -- ambiguity
abbrev normBill (s i k:ℕ)(κ k':ℝ)(M:ℝ) := let f:=frost_bill Y s i k (xhood (P:=P) s) κ k'; (∫ x:Pane (count Y s i),f x ∂prior SU.group (More _)) ≤ Real.exp M
open YM.Gleam.Tempest
lemma far_bill : ∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k→ ∀ κ k':ℝ,freeR Y s i k κ→ coolR Y s i k k' → normBill Y s i k κ k' (gBaseR Y s i k +7*meterC (xhood (P:=P) s)*sites (count Y s i)):=by
 let T:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a:=|K|; let h:= P.chart; let J:= P.L; -- P.L chart?
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le -- tune
 filter_upwards [(stage_slope P.V P.x).eventually (shelfUnmarked P.K.top.clip R' P.chart (V.L.mood 0).width hv V.W.bar P.R.L a (abs_nonneg K)),ciViGeometry P] with s q H i k ht κ k' kK Kk
 let N:= count Y s i; let G:=More N; let F:=Y.uv k - s; let A:= gram Y s i k
 obtain ⟨W,g,t,c,r,u,hX⟩:= H (Y.ir i)
 obtain ⟨he,hT,e,f,_⟩:= prices_plot Y s i k ht
 have hV: A.p.threshold=temp (hat P.R.L P.x s):= he ▸ (Y.meter.boot s).1
 let Z:= P.V.L.H F; have hm:=P.V.L.roof F; let Q:=V.L.path F; have hx:T.top.clip=P.K.top.clip:=rfl
 have Hs := q W g t A.p A.beta f hV G c r u hX (V.L.tied F) (V.L.mood F) (hm.2.1 G) V.W.reserve (fun i=>?_) κ k' kK Kk; -- gauge align
 · unfold normBill; have hg : ∀ V:Pane N,Gleam.twice_angled Q P.K.top.clip A.p A.beta κ k' (shieldC (hat P.R.L P.x s)) V= frost_bill Y s i k (hat P.R.L P.x s) κ k' V:=fun U=> by unfold Gleam.twice_angled; change A.path=Q at hT; change A.funds= _ at e; unfold frost_bill; rw [← hT]; rw [←e]; rfl
   change (∫ V:Pane N,Gleam.twice_angled Q P.K.top.clip A.p A.beta κ k' (shieldC (hat P.R.L P.x s)) V ∂prior SU.group (More N))≤ _ at Hs; simp_rw [hg] at Hs; exact Hs.trans_eq (congrArg Real.exp (show _=_ from (by unfold Gleam.Roof gBaseR Fineness.gaugedBase G; rw [Pannier.shadowLie,sites_as_price])))
 exact (YM.Fineness.stairEstimate Z P.K.width.le hm.1.2.1 i).trans (le_abs_self K)
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.far_bill
