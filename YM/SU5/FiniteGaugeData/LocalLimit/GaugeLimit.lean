import YM.SU5.FiniteGaugeData.LocalLimit.Sequence.Ring
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Model
import YM.SU5.FiniteGaugeData.LocalLimit.Sequence.Share
/-!
# Joint subsequential result. Part I: Local gauge probes

Axiom audits in `checks/HorizontalArrival` and `checks/GaugeLimit`.
**Not claiming** matter local estimate here. The progression and upper cutoff
thresholds are the *actual-first* variant of the bridge, and the input
periods need not use one and the same wave, bare Month pilots etc. (see
Course). Domain in `BoxGauge` contains all gauge-invariant scalar functions
of local support links on given level and box, at least bounded and measurable
(may wrap support, projection priced). This includes gauge Wilson plaquette
density and loops without prescribing any limit value. Their ratio observations
use the full shared regulator with no modifications. Cutoff-first limits at
each period with availability, and one joint square-price estimate.
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
abbrev Box (j:ℕ) := BoxGauge.paper SU.group j
variable (r j i k:ℕ)
abbrev bankLook (p:ℕ × ℕ)(i k:ℕ) := Y.slice p.1 p.2 i k
abbrev spacesFor (i:ℕ)(p:ℕ×ℕ):= Y.availableSpace p.1 p.2 i
abbrev placeable (i k:ℕ):Prop:= (Y.ir i).val^5 ≤ Y.uv k
abbrev grade (i k:ℕ)(p:ℕ×ℕ):= Y.Good p.1 p.2 i k
abbrev load (s:ℕ):Finset (ℕ×ℕ):= Finset.Iic s ×ˢ Finset.Iic s
def coins (s:ℕ):ℝ:= (1/2:ℝ)^s
open YM.SU5.FiniteGaugeData.LocalLimit
structure Query (i k:ℕ→ℕ) where
 L : (p:ℕ × ℕ) → ℕ → BoxGauge.Record SU.group p.2
 Z : (p:ℕ × ℕ)→ BoxGauge.Record SU.group p.2
 grant : Rings.Tent Y.bankLook Y.spacesFor Y.grade Y.placeable Course.load coins i k L Z

lemma corners (A B:ℕ→ℕ)(a:StrictMono A)(b:StrictMono B) : ∃ i k:ℕ→ℕ, StrictMono i ∧ StrictMono k ∧ Nonempty (Y.Query (A ∘ i) (B ∘ k)) := by
 have hm(i): ∀ᶠ k in atTop, Y.placeable i k:= Y.uv_grows.tendsto_atTop.eventually_ge_atTop _
 have ht(k): ∀ᶠ i in atTop, ¬ Y.placeable i k:= ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp Y.ir_grows.tendsto_atTop |>.eventually_gt_atTop (Y.uv k)).mono fun _ h=> not_le.mpr h
 obtain ⟨i,k,L,H,a,b,v⟩:= Rings.two_steps Y.bankLook Y.spacesFor Y.grade Y.placeable Course.load coins
    (fun j=> by obtain ⟨H,_,e,f⟩:= Y.ceil_compact j.1 j.2; exact ⟨H,e,f⟩) (fun j=>Y.fit_more j.1 j.2) (fun i j=> Y.fixed_support j.1 j.2 i) hm ht (fun i=> by unfold coins; positivity) A B a b
 exact ⟨i,k,a,b,⟨⟨L,H,v⟩⟩⟩
namespace Query
variable {u π:ℕ→ℕ}(Q:Y.Query u π)
include Q
open BoxGauge
local notation "μ" => coins
variable (X: Box r)
abbrev step_limit (Q:Y.Query u π):= share r X (Q.L (j,r) i) -- order variables?
abbrev ultimate (Q:Y.Query u π):= share r X (Q.Z (j,r))
lemma priority (h:Y.availableSpace j r i) : Tendsto (fun k=> Y.glimpsed j r i (π k) X) atTop (𝓝 (share r X (Q.L (j,r) i))) := by
 let H(k:ℕ):= Y.slice j r i (π k); have hp : Tendsto H atTop (𝓝 (Q.L (j,r) i)):= Q.grant.cut (j,r) i; refine ((share_cont r X).continuousAt.tendsto.comp hp).congr' ?_
 filter_upwards [Q.grant.dep.tendsto_atTop.eventually (Y.fixed_support j r i h)] with k hk; change share r X (H k)=_; unfold H; rw [Y.ready_slice j r i _ hk]; exact share_one (dummy P) r (ceiling P j) X _ _ hk.rooted (Y.quiz_pos ..).le
lemma infinite : Tendsto (fun v=> share r X (Q.L (j,r) (u v))) atTop (𝓝 (share r X (Q.Z (j,r)))) := (share_cont r X).continuousAt.tendsto.comp (Q.grant.ir (j,r))
lemma eligible(s t:ℕ)(p: Y.placeable (u s) (π t)) (h: j ≤ s)(w: r ≤ s): Y.Good j r (u s) (π t) := (Q.grant.line s t ((Q.grant.card s t).mp p) (j,r) (by simp [Course.load,h,w])).1
lemma pore(s k t l:ℕ) (p: Y.placeable (u s) (π k))(e: Y.placeable (u t) (π l))(h₁:j≤ min s t)(h₂:r≤ min s t):
    ‖Y.glimpsed j r (u s) (π k) X - Y.glimpsed j r (u t) (π l) X‖ ≤ (μ s+ μ t)*BoxGauge.weight r X := by
 obtain ⟨p₁,h⟩:=le_min_iff.mp h₁; obtain ⟨p₂,w⟩:=le_min_iff.mp h₂; have g(s k:ℕ)(p: Y.placeable (u s) (π k))(h:j≤ s)(w:r≤ s) := Q.grant.line s k ((Q.grant.card s k).mp p) (j,r) (by simp [Course.load,h,w]); obtain ⟨u,hg⟩:=g s k p p₁ p₂; obtain ⟨v,z⟩:=g t l e h w
 apply Y.peek _ _ _ _ u v _ X; exact (dist_triangle_right _ _ (Q.Z (j,r))).trans (add_le_add hg z)
end Query
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
