import Anomaly.Framing.Carry
import Anomaly.Framing.Purse
import Anomaly.Rack.Singleton
import YM.CF.Salt.Rider
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax Rill Ione Clock Salt Mew PowerSeries Sour
attribute [local instance] opCStarAlgebra
open scoped Mew
variable {n:Side}
variable {p:BudgetPoint}{X Y Z:Aura n}{D:Support (More n)}
variable {q:ℕ}{h:ℝ} {F: ForceBudget n}
variable (s:Sweep n)
local notation "Vn"=> Aura n
open QuadClock
lemma settleAcross (v:passingF n s F F)(V:Orbit n)(p:Injective (priorP V.2))(X:Vn)(D:Support (More n)):
    settleK F (moldA s X) (actY s D) (yellA s V)=suit_Y s (settleK F X D V) := by
  unfold settleK; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; refine sum_equiv (Salt.fanZ s) (fun i=> ?_) (fun i _=> (v i V p).symm)
  unfold motV; rw [mem_filter,mem_filter,and_iff_right (mem_univ _),and_iff_right (mem_univ _)]
  change _↔ moldA s (lordD i)=moldA s X ∧ actY s (extraD i)=actY s D; exact and_congr (moldA s).injective.eq_iff.symm (Finset.map_injective _).eq_iff.symm

variable {I J:Type} [LinearOrder I][LinearOrder J][Fintype I][Fintype J] {K: I→ Bag n}{G: J→ Bag n}
variable {t e: I→Aura n→ℝ}{v u : J→ Aura n→ℝ}
variable (Q:∀ (i:I)(X:Aura n),YM.CF.Sour.Flight p q X h (K i X) (t i X) (e i X)) (Ψ:∀ (j:J)(X:Aura n),YM.CF.Sour.Flight p q X h (G j X) (v j X) (u j X))
local notation "A" => zealPitch K t e Q
local notation "L" => zealPitch G v u Ψ
local notation "τ" z:max => pinSeries G z
local notation "Θ" z:max => pinSeries K z

#check Q
include Q Ψ
lemma habit_P (g:passingF n s F F) (x:Key I)(y:Key J)(m:ℕ)(f:∀ W:Orbit n,Injective (priorP W.2)→∀ S:Aura n, (τ y) (moldA s S) (yellA s W)=sauce s.charge (detX s.s) (Sour.γS s) ((Θ x) S W)) :
    passingU n s (lensCells F A m x) (lensCells F L m y) := by
  intro X V vp D w
  unfold lensCells layerN; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; exact sum_congr rfl fun i _=> rise_two (settleK F) _ s V (Title.powerQ _ _ (industry K t e Q x)) (Title.powerQ _ _ (industry G v u Ψ y)) vp f (fun X D _=> settleAcross s g V vp X D) X D i w
variable {x:Seat n}
variable (t₀: Ids n)(i:I)(j:J)

lemma peers (f:∀ V:Orbit n,Injective (priorP V.2)→∀ X:Aura n,G j (moldA s X) (yellA s V)=sauce s.charge (detX s.s) (Sour.γS s) (K i X V)) : passingR n s (singleReceipt K t e Q t₀ i x) (singleReceipt G v u Ψ t₀ j ((boxA s).symm x)) := by
  intro X V
  unfold singleReceipt
  have ht(Y:Seat n): (moveHub s X).val.1=(boxA s).symm X.val.1:=rfl; rw [ht x]; by_cases y:X.val.1=x
  · rw [if_pos y, if_pos (congrArg _ y)]; obtain ⟨T,k⟩:=(sepT (n:=n)).exists
    let W:Orbit n:=(V,T); let S:=Bake.lagE X; have hu:Bake.lagE (moveHub s X)=moldA s S:=Subtype.ext rfl
    rw [dedicate_fixed K t e Q i _ t₀ T V,dedicate_fixed G v u Ψ j _ t₀ (bun s T) (flashA s V),hu]; exact leap_two _ s ∅ W 1 1 (Title.powerQ _ _ fun X=>(Q i X).tube.title) (Title.powerQ _ _ fun X=>(Ψ j X).tube.title) k f S S (map_one _).symm -- flags ∅ act same defeq?
  rw [if_neg y, if_neg (fun z=>y ((boxA s).symm.injective z)),Pi.zero_apply,Pi.zero_apply,map_zero]

omit Q Ψ
lemma inkRelease (z:ℂ)(K:I→Bag n)(i:I): pinSeries K (update 0 i z)=z • K i:=by
  funext X; unfold pinSeries; rw [sum_eq_single i,update_self]; rfl; intro j _ v; rw [update_of_ne v]; exact zero_smul ..; simp -- include remove
#print axioms peers
#check peers
end YM.CF.Vow.TreasuryFog
