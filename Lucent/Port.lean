import SU5SatinWakePhysicalGramNovember8
import Lucent.Drill
/-! # Begin with Spine.wakeElectionWithPhysicalGram
KEEP all the appointments and credentials. Our registration,
quote, Wick and reading lemmas are applications at that election.
In this door we also budget the every-s kinetic coupling normalization
on the same coherent path (can incorporate any antecedent path thinning).
Neither these measurements nor these estimates require changing the
irreversible cutoff/period elections before any future x.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter MeasureTheory
open scoped Topology
open Py Py.Rate LocalLimit Preparation Preparation.Yoke Lucent Jewel
universe u
variable (P:Spine)
local notation "iA"=> P.period ∘ P.projection.rows
local notation "kA"=> P.cutoff ∘ P.projection.columns

/-- Ticket. No assuming a-law openness when later turning to this family. -/
structure Port (K:P.Register)(M:ℝ)(Mc:ℕ)(f:ℕ→ℕ)(β:ℕ→ℝ):Prop where
  investment: PreparedInvestment P K M Mc
  signedPose:PureForce.CakeL.SignedPoseBudget P
  readout:QualifiedWakeReadout.{u} P K
  Gram:PhysicalWakeGram P
  pooled: Pooling P.run iA kA f β
  wavetable :(∀ (I:Type)[Fintype I] (C A:ℝ)(m d:ℕ),0≤C → 0<A →
    ∀ᶠ s in atTop,∀ᶠ j in atTop, MixedBox P.run s (iA j) (kA j) M C A I m d)
#check @wakeElectionWithPhysicalGram

/-- A may be chosen *after* making all these purchases. Candied bounds
(and physical degree/order) are preassigned to use each uniform late-s cost.
-/
theorem wakeWithAnArmy (X:TintDemand)(Mc:ℕ):
 ∃ (P: Spine) (K:P.Register) (M:ℝ), ∀ (u:ℕ→ℕ),StrictMono u → ∃ (q:ℕ→ℕ) (β:ℕ→ℝ), StrictMono q ∧ Port.{u} P K M Mc (u ∘ q) β := by
 obtain ⟨P,K,E,b,c,d,e⟩:= wakeElectionWithPhysicalGram.{u} X Mc
 refine ⟨P,K,E,?_⟩; intro u h; obtain ⟨q,w,hq,hw⟩:= Pooling.fettle P.run P.history h
 refine ⟨q,w,hq,b,c,d,e,hw,?_⟩
 intro I _ C A m g p t
 obtain ⟨v,k⟩:=b.investment
 exact charEncounter P.run P.law P.history I m g k b.dispatch b.rocky.merit p t
#check wakeWithAnArmy
#print axioms wakeWithAnArmy
