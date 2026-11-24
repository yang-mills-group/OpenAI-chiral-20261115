import Organdy.Perch
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

/-- Timer budget and old K on one finite book. Does not mention launches;
applies to any with compatible Barrage per anchor, with costs full a birth b. -/
structure Polar (p:BudgetPoint)(h:ℝ)(q:ℕ)(F:ForceBudget n)
    (M L:ℕ)(a b γ:ℝ):Prop where
 large:2*(massif L*p.B) ≤ (More n).val
 width:10≤p.B
 rate: p.supportExponent=1
 tall: 1≤h
 stalls:Stalls p M (outfit L a) (outfit L b) γ
 before :∃ d:ℝ,d < γ ∧ Ledger p h q d F

variable {M L:ℕ}{γ:ℝ}{F:ForceBudget n}
variable (K:Polar p h q F M L a b γ)
variable {Y:I→Support (More n)} {σ:I→Seat n}
variable (V:I→Bag n)
local notation "v'"=>incline σ L p V

/-- Single realization data, in the normalization used by the launches
of the gas. Parametric in post-crag costs a b. -/
structure Tumble (p:BudgetPoint)(h:ℝ)(q:ℕ)
    (F:ForceBudget n)(M:ℕ)(a b γ:ℝ)
    (σ:I→Seat n)(V:I→Bag n)
    (A B:I→Aura n→ℝ)(r:Aura n→Support (More n)→ℝ) :Prop where
    width:10≤p.B
    rate:p.supportExponent=1
    tall: 1≤h
    tine:Tine p q h σ V A B a b
    pow:Stalls p M a b γ
    density:breeze σ M
    paid: OrbitRack pow.sleigh σ q F h tine.toPollen.soar
      (∑ i:I,A i) (∑ i:I,B i) r (trawling V)

include K
lemma Polar.realize
    (e:breeze σ M) (o:∀ i,σ i∈Y i)
    (bills:∀ i:I,Barrage p q (Y i) h (V i) (highLaunch p) a b):
    (∀ i:I,Pavilion L p (v' i)) ∧
    ∃ A B r,Tumble p h q F M (outfit L a) (outfit L b) γ σ v' A B r:= by
  obtain ⟨A,B,v⟩:=blossom L ((safetyK K.width).2 K.rate) o bills
  obtain ⟨d,hd,g⟩:=K.before
  obtain ⟨r,s⟩:= rerack K.stalls K.width (zero_le_one.trans K.tall) g hd v e
  exact ⟨fun _=>backed K.large _ _,A,B,r,K.width,K.rate,K.tall,v,K.stalls,e,s⟩
end YM.CF.Organdy
