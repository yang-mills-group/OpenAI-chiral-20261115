import YM.SU5.FiniteGaugeData.Dally.Archon
import ZecaGilt
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin.Gem Poin Poin.Galleon Poin.Galleon.Dai Leal Leal.Breve
  Celeritas Land
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (N : Canopy (K timeAxis) ι) (A : Tribe N)
    (ω : ∀ i, (K i).space) (j : Axis)
namespace Gilt

variable (u : N.Chip)

def Diad : Prop:=
  ∀(n:ℕ)(p:Points n)(u:Fin n→N.Chip)(a b:Axis)(L L':List (Fin n)),L.Perm L'→
   ProofOrder p a L→ProofOrder p b L'→
 quoteG W N A ω a p u L=quoteG W N A ω b p u L'

local notation "StampF"=>stamped W N A
variable (y:∀j,saucer (W j) (ω j)=ω j)(D:Diad W N A ω)
include y D

lemma monarch (n:ℕ)(a b:Axis):
   Philos (σ:=Fin n) W ω a b (Set.range (StampF)):=by
 intro F h p L L' e _ d r
 choose v g using h
 rw [show F=StampF ∘ v from (funext g).symm] at d r ⊢
 let z:=WithLp.toLp 2 p
 rw [stamped_paid (x:=z) _ _ _ _ a v L (y a) d,
     stamped_paid (x:=z) _ _ _ _ b v L' (y b) r]
 have f (j:Axis){i k:Fin n}(g:Seers (StampF ∘ v) p j i k):
       p i j < p k j:=
    (le_add_of_nonneg_right (v i).2.val.coe_nonneg).trans_lt
      (g.trans_le (sub_le_self _ (v k).2.val.coe_nonneg))
 exact D _ z _ a b L L' e (d.imp fun h=>f _ h) (r.imp fun h=>f _ h)
#print axioms monarch

structure Regime where
 delta:ℝ
 eta:ℝ
 steps:ℕ→ℝ
 sites:∀n,Set (Points n)
 tiny:0<eta
 shuffling:∀ᶠ i in atTop, 0<steps i
 easy:Tendsto steps atTop (𝓝 0)
 covers:∀n, Dense (sites n)

variable (B:Regime)
abbrev initial:=Rookie W N ω A B.delta B.eta B.steps B.sites
abbrev actual:=Quarter W N ω A (StampF) (fleet W N A)
                   B.delta B.eta B.steps B.sites
omit D in lemma initial_actual:initial W N A ω B↔actual W N A ω B:=
 Sensor W N ω A _ _ (y _) _ _ _ _ B.shuffling

lemma rookie_real:initial W N A ω B↔RotReal W N ω A:=
 altar W N ω A y (sealC W N A)
    (fun n a b _=>monarch W N A ω y D n a b)
     _ _ B.tiny _ _ B.shuffling B.easy B.covers
lemma chamber: actual W N A ω B↔ RotReal W N ω A:=
  (initial_actual W N A ω y B).symm.trans (rookie_real W N A ω y D B)

#print axioms chamber
#check altar
