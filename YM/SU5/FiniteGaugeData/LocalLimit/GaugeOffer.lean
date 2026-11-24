import YM.SU5.FiniteGaugeData.LocalLimit.GaugeLimit
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Image
/-!
# Limits of auxiliary PSD offer in the true gauge volume subsequences

*Only* positive with the buffered positive link support here: at the cover origin,
after spending `reach`, use `Sees` (both endpoints each link). The `mirror` definitions
use cover native reflection coordinates along that axis, undo the positive link convention,
and multiply at the same resolution on the same configuration.

Not all marks, not an assertion of full CapP positivity at the finite steps. For
finite volume UV limits of that theory on the Query, we also require room to
reflect on the same tile period. The stated estimate is norm PSD for that
cover matrix.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit
open Window SquareScalar
namespace Preparation
open Marks Donor
variable {P: Preparation}{F : (s:Side)→ Scree.Loom s→Prop} (Y:Course P F)
namespace Course
local notation "Ξ" i:max => Y.voyage i
local notation "Gₛ" i:max k:max h:max => (Ξ i).Q k h
local notation "Xj" i:max j:max => cell (Y.ir i) P.block P.R.L j
local notation "γF" i:max j:max => Pane (Xj i j)
local notation "G₀" i:max k:max => (Ξ i).X (Y.uv k)
local notation "Xm" i:max j:max => (Ξ i).CapeT j
open FullBill Push.GridApprox
open BoxGauge
variable (r j i k:ℕ)
local notation "σ" => SU.group
local notation "Λ…" => More (P.Ctor (Y.ir i) j)
local notation "Γ…" => P.Ctor (Y.ir i) j
local notation "Xg" h:max => (Ξ i).Q k h
abbrev melter (p:(Y.voyage i).kick ≤ k)(X: Pane (Γ…)→ℂ):= Donor.probe (Ξ i).funds (Xg p) j (bosonic Γ… X) -- order? theorem verses
abbrev hintM (A :Box r) (k:ℕ):= if h:(Y.voyage i).kick ≤ k then Y.melter j i k h (BoxGauge.paint r _ A) else 0

variable (A : Box r)
lemma melted_price {X:ℂ}{u:ℕ→ℕ}(v:StrictMono u)(p:Tendsto (fun k=>Y.glimpsed j r i (u k) A) atTop (𝓝 X)): Tendsto (fun k=>Y.hintM r j i A (u k)) atTop (𝓝 X):= by
 let Xf:= BoxGauge.paint r (Λ…) A
 let Z:=bosonic Γ… Xf; let f(x:Orbit Γ…):= Z x.1
 have hv:= (BoxGauge.paid r A).1.comp_env (BoxGauge.tab_cont r (Λ…)).measurable; have hm:Measurable f:= Marks.lift_meas Z ( ((show Continuous (fun v:ℂ=>v • (1: FC (Single Γ…))) from continuous_id.smul continuous_const).measurable.comp hv.meas))
 let w:=max 1 hv.cost.choose; have h₀:=le_max_right 1 hv.cost.choose; have hw:0 < w:= zero_lt_one.trans_le (le_max_left ..); have hW:∀ i,‖f i‖ ≤ w:= Donor.tag_width Xf w fun i=>(hv.cost.choose_spec i).trans h₀
 refine p.congr_dist (Metric.tendsto_nhds.mpr fun ε t=>?_)
 let d:=ε/(2*w); have he:0<d:=by unfold d; positivity
 filter_upwards [v.tendsto_atTop.eventually (Y.thaw j d he),v.tendsto_atTop.eventually (eventually_ge_atTop (Y.voyage i).kick)] with k T q
 rw [hintM,dif_pos q] -- rewrite issues
 rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm]; apply lt_of_le_of_lt _ (show d*w < ε from by unfold d; field_simp; nlinarith)
 change ‖finiteForm P.V.U P.U _ _ Z - finiteForm P.V.U P.U _ _ Z‖ ≤ _; rw [← Marks.identify,← Marks.identify]; exact T i q f w hm hW

variable {u π:ℕ→ℕ}
namespace Query
open BoxGauge Reflect
open scoped ComplexOrder
variable (Q:Y.Query u π) {I:Type*} [Fintype I] (D:I→Box r) (s:Axis) (h:∀ i,BoxGauge.Sees r P.R s (D i))
include h Q
def smoke (q: ℕ) (I:Type*) (D:I→Box q)(s:Axis)(b: BoxGauge.Record SU.group q) :Matrix I I ℂ := Matrix.of fun x y=> BoxGauge.share q (BoxGauge.reflected q (Signed.mirror s) (D x)* D y) b -- include h Q?
local notation "Λ" => BoxGauge.weight
lemma survives (e:Y.availableSpace j r i)(f:r+Push.GridApprox.reach P.R<(Γ…).val): (smoke r I D s (Q.L (j,r) i)).PosSemidef:=by
 let A(i x:I): Box r:= (reflected r (Signed.mirror s) (D i))* D x
 let X(x:I):= BoxGauge.paint r (More (cell (Y.ir i) P.block P.R.L j)) (D x)
 let pz(k):Matrix I I ℂ:= Matrix.of fun i' x=>Y.hintM r j i (A i' x) (π k)
 refine Window.proveLimit pz _ ?_ fun a b=> melted_price Y r j i (A a b) Q.grant.dep (priority Y r j i Q (A a b) e)
 filter_upwards [Q.grant.dep.tendsto_atTop.eventually (Y.heatGap j),Q.grant.dep.tendsto_atTop.eventually (eventually_ge_atTop (Y.voyage i).kick)] with k t u
 let B:= (Ξ i).Q (π k) u
 have hD: (pz k)= reflectionForm (m:=Vale.mesh (Y.ir i) P.R.L j) (B:=P.block) s (Donor.probe _ B j) (fun i=>bosonic Γ… (X i)):= by
    ext x y; change hintM _ _ _ _ _ _ =(Donor.probe _ B j) (flipTime _ _ _ _* _); unfold hintM; rw [dif_pos u]; rw [θ_bosonic,boseP]; dsimp only [melter]; apply congrArg; apply congrArg; exact (congrArg (· * X y) (BoxGauge.mirror r s (D x))) -- tune def
 rw [hD]; exact B.PSD_buffered _ P.scale P.budget _ j (t.1.trans (deeper ..)).le (t.2 i u).priceH.valid X fun i'=> BoxGauge.m_gate r P.R s (D i') f (h i')
theorem candles : (smoke r I D s (Q.Z (j,r))).PosSemidef := by
 apply Window.proveLimit (fun s'=> smoke r I D s (Q.L (j,r) (u s')))
 · have hm:∀ᶠ i in atTop,r+Push.GridApprox.reach P.R < (cell (Y.ir i) P.block P.R.L j).val:= (Y.ir_grows.tendsto_atTop.eventually_gt_atTop _).mono fun i h=> lt_of_lt_of_le h (amplit (Y.ir i) P.block P.R.L j)
   exact Q.grant.per.tendsto_atTop.eventually (((Y.fit_more j r).and hm).mono fun i a=> survives Y r j i Q D s h a.1 a.2)
 exact fun a b=> infinite Y r j Q (BoxGauge.reflected r (Signed.mirror s) (D a)* D b)
end Query
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
