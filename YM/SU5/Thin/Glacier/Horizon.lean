import YM.SU5.Thin.Glacier.Throat
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
open clocks
variable {L':Side}
namespace Papal
open clocks CF.Pannier.Damask
variable (s i k:ℕ)
local notation "M"=> count Y s i
local notation "uX"=> hat P.R.L P.x s
local notation "Xg"=> gram Y s i k
local notation "Bt"=> (Y.uv k-s)
abbrev winterBill (u:Pane (count Y s i)) := polarBill (P.V.L.path Bt) P.K.top.clip ((Xg).p) ((Xg).beta) (grain uX) (ledge uX) (outerMark uX) u
abbrev scenic (r: Ratio N (More (count Y s i)))(B t Q:ℝ)(φ:Pane (count Y s i)→ℝ)(U:Altar SU.group (More (count Y s i))→ℝ):Prop:= ∀ (A:Support N)(W:Finset (Pressure.Cell (More M))), RimScene (P.V.L.mood Bt) (P.V.L.tied Bt) (Xg).p r (height uX) (Xg).beta (scant uX) (Q+B*fritTrap r (height uX) A W) (outerMark uX) A W t φ U
abbrev panorama (t:ℝ)(U:Altar SU.group (More (count Y s i))→ℝ):ℝ:= plumeCost (P.V.L.mood Bt) (P.V.L.tied Bt) U t
abbrev winterRent := Fineness.gaugedBase P.L (gram Y s i k).beta (More M) (P.V.L.H Bt) + oar uX * sites M
def VisiblePolar (E t sB:ℝ) (r:Ratio N (More (count Y s i))) (φ:Pane (count Y s i)→ℝ): Prop :=Envelope φ ∧ ∀ a:Signed, let φ'(V:Config SU.group (More M)):= φ (pull a 0 V); GaugeInvariant φ' ∧ ∃ (W:Altar SU.group (More M)→ℝ)(R₁ R₂ Q:ℝ),ContDiff ℝ 1 W ∧(∀ i,|W i|≤ R₁)∧ (∀ i, ‖fderiv ℝ W i‖ ≤ R₂) ∧ panorama Y s i k t W + Q + Regis.trend* R₂^2*t^2 ≤ sB ∧ scenic Y s i k r E t Q φ' W
lemma flintBill {n:Side}(r:Ratio n (More (count Y s i)))(E:ℝ) (p:0≤E): VisiblePolar Y s i k E 0 0 r (fun _=>0):=by
 refine ⟨Envelope.const _,fun a=>?_⟩; intro V'; refine ⟨(fun _ _=>rfl),fun _=>0,0,0,0,contDiff_const,(by simp),(fun x=>by simp),?_ ,?_⟩
 · simp [panorama, plumeCost]
 intro A W U V Y hr ht hs hz; simp only [mul_zero,zero_mul,zero_add,ge_iff_le]; unfold fritTrap; positivity
lemma financed (E:ℝ)(eh:0≤E): ∀ᶠ s in atTop, ∀ i k:ℕ,s≤Y.uv k→ ∀ {n:Side} (r:Ratio n (More (count Y s i))), Portal r (hat P.R.L P.x s) P.R.L→ ∀ (F:Pane (count Y s i)→ℝ) (t b:ℝ), VisiblePolar Y s i k E t b r F → (∫ x:Pane (count Y s i), winterBill Y s i k x*Real.exp (t* F x) ∂prior SU.group (More (count Y s i))) ≤ Real.exp (winterRent Y s i k+b):=by
 let T:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a₁:=|K|; let h:= P.chart; let J:= P.L
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le
 filter_upwards [(stage_slope P.V P.x).eventually (clocks.canyonRide P.K.top.clip R' P.chart a₁ P.R.L (V.L.mood 0).width hv V.W.bar (abs_nonneg K) E eh)] with s p i k hk; intro n r h F t b w
 refine everyPolar (P.V.L.mood (Y.uv k-s)) w.1 _ t (fun a=> ?_); obtain ⟨x,W,R₁,R₂,Q,H,hp,hf,w',z⟩:= w.2 a
 let Gx:=gram Y s i k; let B₁:= Y.uv k-s; let Z:= P.V.L.H B₁; let d:=(count Y s i); let N:=More d; obtain ⟨he,hT,e,f,_⟩:= prices_plot Y s i k hk; have hV: Gx.p.threshold=temp (hat P.R.L P.x s):= he ▸ (Y.meter.boot s).1; let hm:=P.V.L.roof B₁; let F'(x: Config SU.group N):= F (pull a 0 x); have hv':Envelope F':=⟨w.1.meas.comp (by apply (prior_pull _ _).measurable),w.1.cost.choose,fun _=> w.1.cost.choose_spec _⟩
 apply le_trans (p r.count h.odd h.span Gx.p Gx.beta f hV N n r h.ample rfl (V.L.tied B₁) (V.L.mood B₁) (hm.2.1 N) V.W.reserve (fun i=> (YM.Fineness.stairEstimate Z P.K.width.le hm.1.2.1 i).trans (le_abs_self K)) t Q R₁ R₂ hv' x W H hp hf z) (Real.exp_monotone ?_) -- F' implicit use `(φ...)` at p filter_leans explicit?
 dsimp only [N] -- drop?
 unfold winterRent Fineness.gaugedBase Gleam.Roof; rw [Pannier.shadowLie]; try rw [sites_as_price]; unfold panorama at w'; linarith only [w']
lemma fleeced (E:ℝ)(p:0≤E): ∀ᶠ s in atTop, ∀ i k:ℕ, s ≤ Y.uv k→ (∫ x:Pane (count Y s i), winterBill Y s i k x ∂prior SU.group (More (count Y s i))) ≤ Real.exp (winterRent Y s i k):=by
 filter_upwards [financed Y E p, winters_port P] with s g w i k h; obtain ⟨c,r,f⟩:= w (Y.ir i); simpa [Real.exp_zero] using (g i k h r f _ _ _ (flintBill Y s i k r E p))
end Papal
end LocalLimit
end Rate
end YM.CF.Py
