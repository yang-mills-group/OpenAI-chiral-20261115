import YM.SU5.FiniteGaugeData.LocalLimit.Local.Sing
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Linear
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Card

/-!
# L¹ functional bound and compact approximations.

All arguments drawn exactly under the `city` probability with operators from
`ratioField`. In this section, support on tags empty since scalar.
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
variable (j r i k:ℕ)
local notation "Ξs" => BoxGauge.paper SU.group r
abbrev glimpsed (A: ↥(BoxGauge.paper SU.group r)) := Y.texture i k j (bosonic (Xj i j) (BoxGauge.paint r _ A))
abbrev quiz:= Y.radiusPrice (j+1) (ready P r)
lemma quiz_pos : 0 < quiz Y j r:=by unfold quiz radiusPrice mural; positivity

def availableSpace:= SquareScalar.tile P.block P.R (ready P r) ≤ (cell (Y.ir i) P.block P.R.L (j+1)).val ∧ 2*r < (More (cell (Y.ir i) P.block P.R.L j)).val
lemma fit_more : ∀ᶠ i in atTop, Y.availableSpace j r i := by
 have h(s): ∀ q:ℕ, ∀ᶠ i in atTop, q ≤ (Xj i s).val:= fun q=> ((Y.ir_grows).tendsto_atTop.eventually_ge_atTop q).mono fun i h=>h.trans (amplit (Y.ir i) P.block P.R.L s)
 filter_upwards [h (j+1) (SquareScalar.tile P.block P.R (ready P r)),h j (2*r+1)] with i p l using ⟨p, (show 2*r < (Xj i j).val *2 from (by omega))⟩
local notation "C" => Y.quiz j r
local notation "Lf" i:max k:max => Y.glimpsed j r i k
local notation "Ss" => dummy P
local notation "Ft" => ceiling P j
local notation "Q" => Y.radiusPrice
local notation "k₀" => (Ξ i).kick

-- `Good` is true throughout permit, not requiring an arbitrary additional selection
-- around the price of this mark. (UV thresholds still depend on period.)
structure Good (i k:ℕ) : Prop where
 eligible : Y.availableSpace j r i
 val : j < buoy (Y.ivory k)
 own : (Y.voyage i).kick ≤ k
 rooted : BoxGauge.Used r (dummy P) (ceiling P j) (Y.glimpsed j r i k) (Y.quiz j r)

lemma legitimate : ∀ᶠ k in atTop, ∀ i, (Y.voyage i).kick ≤ k → Y.availableSpace j r i → Y.Good j r i k := by
 filter_upwards [Y.at_home (j+1)] with k u i p h
 have hz := u.1.trans (deeper (Y.ivory k) P.b)
 have ht:j < Y.uv k:= Nat.lt_of_succ_lt hz; let X:= (Ξ i).X (Y.uv k)
 have h₀:= Y.each_level i k j p ht.le
 refine ⟨h,Nat.lt_of_succ_lt u.1,p,?_⟩; let S:= Y.stepData i k j; let x:= Y.beta i k j; have he:= Y.pilot_steps j i k
 have hv:S.kernel=(dummy P).kernel:= he.2.1
 constructor
 · intro A B; exact Window.chips _ (can_evaluate _ _ (X.gram j) _ h₀) r A B
 · intro A c; exact Window.chips_scale _ r A c
 intro A; let Ak:= BoxGauge.paint r (More (Xj i j)) A; let V:= Y.lyric i k j Ak; let w:= ‖BoxGauge.digest r (dummy P) (ceiling P j) A‖
 have hA:Cells.Interior (Push.GridApprox.window 0 r) Ak:= BoxGauge.within r A
 have hz:∀ i':Pane (Xj i (j+1)), ‖V i'‖ ≤ w:= fun i'=> BoxGauge.tariff r S x A he.2.2 h.2 (fun B=> by
    rw [BoxGauge.news_agrees r Ss S hv.symm A x]; exact (BoxGauge.digest r Ss (ceiling P j) A).norm_coe_le_norm (⟨x,Y.seated j i k ht⟩,B)) i'
 change ‖Y.texture i k j (bosonic _ Ak)‖ ≤ _; rw [Y.singer j i k ht Ak ⟨hA.borel,hA.cost⟩]; exact u.2 i p (ready P r) h.1 w V (Y.closer j i k r Ak hA) hz

lemma fixed_support (h:Y.availableSpace j r i) : ∀ᶠ k in atTop, Y.Good j r i k := ((Y.legitimate j r).and (eventually_ge_atTop (Y.voyage i).kick)).mono fun _k u=> u.1 i u.2 h

open scoped BoundedContinuousFunction
abbrev slice : BoxGauge.Record SU.group r:= if h: Y.Good j r i k then BoxGauge.Used.bank r Ss (ceiling P j) (Y.glimpsed j r i k) h.rooted (Y.quiz_pos ..).le else 0
lemma ready_slice (h:Y.Good j r i k): slice Y j r i k=BoxGauge.Used.bank r (dummy P) (ceiling P j) (Y.glimpsed j r i k) h.rooted (Y.quiz_pos ..).le := by unfold slice; rw [dif_pos h]
lemma ceil_compact : ∃ A:Set (BoxGauge.Record SU.group r), 0 ∈ A ∧ IsCompact A ∧∀ i k, Y.slice j r i k∈ A := by
 obtain ⟨A,h,p,q⟩:= BoxGauge.packed r Ss (ceiling P j) SU.group C (Y.quiz_pos j r); refine ⟨A,h,p,fun i k=>?_⟩; unfold slice; split; exact q _ _ _; exact h
lemma peek {i' k':ℕ}(p:Y.Good j r i k)(q:Y.Good j r i' k'){ε:ℝ}(e:dist (Y.slice j r i k) (Y.slice j r i' k') ≤ ε)(A:Ξs):
    ‖Y.glimpsed j r i k A-Y.glimpsed j r i' k' A‖ ≤ ε*BoxGauge.weight r A := by
 rw [Y.ready_slice j r i k p,Y.ready_slice j r i' k' q] at e; rw [←dist_eq_norm]; exact BoxGauge.Used.see _ _ _ p.rooted (Y.quiz_pos ..).le q.rooted e A
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
