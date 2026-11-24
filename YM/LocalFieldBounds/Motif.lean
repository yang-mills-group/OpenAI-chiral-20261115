import YM.SU5.SatinWard.Resolution.Peralta
import YM.SU5.SatinWard.Resolution.Moonglow
import YM.SU5.Reconstruction.Seams.Bills
import YM.SU5.Macro.Across
import YM.LocalFieldBounds.Motif.Pivot

/-!
# Direct pair on a Ward calendar

Last import, incorporating a short receipt and a named axiom audit.
Use `finale`. In particular this standalone purchase theorem has no parameters
or hypotheses.
This buys the CP scope only, NOT the full relativistic claim.
See also the construction notes (hand-off).
-/

set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.LocalFieldBounds.Motif
open Filter Function Set Metric MeasureTheory 
open scoped Topology ComplexOrder InnerProductSpace NNReal Classical
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
open CF.QuadClock.ShapeLab SoulField SatinWard.Installment
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open Polaris.Rampart _root_.GarnetAct.Cut
open Set MeasureTheory
open _root_.YM.SatinWFixed Andesite Carton _root_.YM.Boundary Probe
open CF.Py.Rate.LocalLimit Preparation
open CF.Buffered.Afterglow.Tower
open Preparation.Tabletop CasaF.Signboard
open CF.Py.Rate.LocalLimit.Preparation.Yoke
open CF.Ione.Clock CF.Moto CF.LitCurrent AuroraX Verdance Lattice
open CF.QuadClock.SignSlot
open Chili
open YM.WakeFields CF
open Papal.Moon
open SatinWard
universe u

open Resolving ResolutionFrame

attribute [local irreducible] Spine.Register

open Metric
variable {X Z:TintDemand}{Q:Supplier}{m:ℕ}{η:Type}[Fintype η][Nonempty η]
  {ε' target:ℝ}{y : Programme.{u} X Z Q m η ε' target} (g : Stage y)


local notation "h@" => y.ht.tendsto_atTop
local notation "o@" => y.Costs.ledger.rocky.night
local notation "W@" => g.a.Wj
local notation "e@" => g.a.ed

namespace Stage

abbrev chron := windowχ y.P g.v
abbrev activation := brow y.P h@ e@ o@ g.w true 0
abbrev carton := galaxy y.P rayPost rayP y.M h@ W@ e@ o@ g.guest.atx
abbrev matter_tag := (g.guest.sig:ℂ) • choral g.guest.i g.activation

abbrev Ω := g.carton.vacuum
abbrev matter_op := g.carton.operator g.matter_tag (Easel.film g.guest.first)
abbrev gauge_op := g.carton.operator omegaCorner (Easel.film g.guest.last)

end Stage

local notation "ΓJ" => g.matter_tag
local notation "ΓK" => omegaCorner
local notation "left♣" => g.guest.first
local notation "right♣" => g.guest.last
local notation "joint" => inner ℂ g.Ω (g.matter_op (g.gauge_op g.Ω))

/-- A few selected consequences at exactly this Stage (see the gift for
further claims including tolerance, calibration, estimator & Ward records). -/
structure PairReceipt : Prop where
  paid : Pivot y.P y.f target
  latched : y.P.lodestar 3 g.guest.atx
  thermal : InkPort g.carton g.guest.eu g.guest.mink
  pos : 0 < g.chron
  apo : ∀ x ∈ tsupport (Easel.film left♣), ∀ z ∈ tsupport (Easel.film right♣),
      2*g.chron < time z - time x ∧
      |time z - time x| + g.chron < z.ofLp 0 - x.ofLp 0 ∧
      x-z ∈ Mink.spacelike
  symmetric : LinearMap.IsSymmetric g.matter_op ∧ LinearMap.IsSymmetric g.gauge_op
  direct : joint ≠ (inner ℂ g.Ω (g.matter_op g.Ω)) * inner ℂ g.Ω (g.gauge_op g.Ω)
  wick :
    vesper g.guest.eu ΓJ ΓK left♣ right♣ ≠
      sighting g.guest.eu ΓJ left♣ * sighting g.guest.eu ΓK right♣

lemma receipt : PairReceipt g :=
  let p := g.guest.gift
  ⟨tied y,p.moors,p.song.ticket,p.song.wrap.tempo,
   (fun _ h _ k => out_of_reach y.P y.M g.activation g.guest.i h@ W@ e@ o@
     g.guest.atx g.chron g.guest.sig _ _ g.guest.r p.song.wrap _ _ h k),
   p.credit.grip,price_not_product y.P y.M g.activation g.guest.i h@ W@ e@ o@
     g.guest.atx g.chron g.guest.sig _ _ g.guest.r _ _ p,
   wick_not_product y.P y.M g.activation g.guest.i h@ W@ e@ o@
     g.guest.atx g.chron g.guest.sig _ _ g.guest.r _ _ p⟩

/-- Standalone election theorem, using the direct-pair CP scope.
`g.guest.gift.world` in this conclusion carries the tolerance claims even
on the approximating stencil estimator and the real-time regulator. -/
theorem finale : ∃ l:Lone, PairReceipt l.date :=
  id (specimen.elim (fun l => ⟨l,receipt _⟩))
#print finale
#print axioms finale
#print axioms programme
#print axioms late_at
#print axioms dressed
#print axioms specimen
#print axioms january_debut
#print axioms rerun
#print axioms opening
#print axioms tied
#print axioms pivot
#print axioms receipt
#print axioms gift_of
#print axioms signal
#print axioms charge_real
#print axioms double_billing
#print axioms Easel.tone
#print axioms Easel.Stamp.interpolate
#print axioms appointment
#print axioms halls
#print axioms cashed
#print axioms blaze
#print axioms credit_test
#print axioms given_fee
#print axioms paid_stage
#print axioms stageK
#print axioms stageJ
#print axioms use_valise
#print axioms initial
#print axioms cargoJ
#print axioms cargoK
#print axioms price_not_product
#print axioms no_clock
#print axioms pay_solo
#print axioms pay_cross
#print axioms blood_tax
#print axioms blood_scale
#print axioms drewW
#print axioms InkPort.tensor
#print axioms InkPort.real_value
#print axioms InkPort.real_pair
#print axioms InkPort.true_pos
#print axioms InkPort.reference_eq
#print axioms Carton.black_con
#print axioms tales
#print axioms lightingW
#print axioms approachW
#print axioms Orchid.spanMeter
#print axioms Spine.bare_chiral
#print axioms Spine.six_families
#print axioms Spine.bare_density
#print axioms Spine.input_formula
#print axioms Spine.input_order
#print axioms Spine.common_reading
#print axioms Spine.usual_footprint
#print axioms Spine.heavenRank
#print axioms signatureK
#print axioms signatureJ
end YM.LocalFieldBounds.Motif
