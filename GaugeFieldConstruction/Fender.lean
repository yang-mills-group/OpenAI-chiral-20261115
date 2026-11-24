import GaugeFieldConstruction.Cyclone
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Rio
open Grotto
variable {n:Side}{I:Type}[Fintype I][LinearOrder I]
section
variable {α β J:Type}[Fintype α][Fintype β][Fintype J]
variable (σ:I→Seat n){S:α→Support (More n)}{z:β→Force n} (Γ:J→ Grotto I S z)(u:J→ℝ)(P:BudgetPoint)(h r:ℝ)(K:ℕ)(y:Seat n)
def payment : Rio I n :=⟨white σ Γ, Grotto.gray σ Γ,Grotto.fullY σ Γ⟩
def payStamp (C:α→ℝ)(U:β→ℝ):CashI I n:=⟨blerr σ Γ u C,verr σ Γ u C,Grotto.flair σ Γ u C U⟩
variable (o:Seat n)(e:∀ i,(Γ i).anchor.val.1=o)
variable (A:Rio I n) (X:Origin n) (a η ℓ Ω:ℝ)(b:ℕ)(hΩ:0≤Ω)(pΩ: Cube_M b*Ω ≤1) (s:0<r) (hs:0<η)
-- adapter. Cost transforms.Rotation require Garner proof still.Recurse.Att.
include e hΩ hs s pΩ
lemma vintage (p: ∀ (V:CashI I n), Weighted P σ r h K A V→ ∃ (u:J→ℝ)(C:α→ℝ)(U:β→ℝ),0≤C ∧ 0≤U ∧ (∀ j:J,Grotto.Pits σ (Γ j) (u j) C U P r h K) ∧ (∑ j:J,u j*Summit b a (Γ j).anchor.val.2)≤ℓ ∧ ∀ L:List (Site (More n)),∀ i:Site (More n),SumAll b a η X V L i = postG S C (RedB b a η L) i+postG (plateI z) U (ColdB b a η L) i) : Adv_L P σ r h K b a η ℓ Ω X o A (payment σ Γ):=by
 intro V g L l t
 obtain ⟨u,C₀,U,v,h,H,sz,Q⟩:=p V g
 let Y:= RedB b a η L; let Y' := ColdB b a η L; let R:=o::L; let T:= RedB b a η R; let T':= ColdB b a η R
 have eU:= Grotto.hour σ Γ u C₀ U v h P _ _ _ s H -- order
 have he(i): postG S C₀ Y i ≤ Ω∧postG (plateI z) U Y' i ≤ Ω:=by
    have hx(i):Y i≤ T i:=Temp_mono b _ η L i hs.le o
    have hz(i): Y' i ≤ T' i:= Temp_mono b _ η L i hs.le o
    apply And.intro ?_ ?_
    · refine le_trans ((Finset.sum_le_sum (s:=univ.filter (fun j=> i∈ S j)) (fun i _=> mul_le_mul_of_nonneg_left (hx (S i)) (show 0≤C₀ i from v i)))) ?_ -- tune underscores
      have eK:=t i; rw [Q] at eK; apply le_trans (le_add_of_nonneg_right ?_) eK; exact sum_nonneg (fun i _=>mul_nonneg (h _) (Temp_p ..|>.le))
    refine le_trans (sum_le_sum (s:=univ.filter (fun j=> i∈ plateI z j)) (fun j _=> mul_le_mul_of_nonneg_left (hz (plateI z j)) (show 0≤U j from h _))) ?_; have eK:=t i; rw[Q] at eK; apply le_trans (le_add_of_nonneg_left ?_) eK; exact sum_nonneg (fun i _=>mul_nonneg (v _) (Temp_p ..|>.le))
 refine ⟨payStamp σ Γ u C₀ U,⟨eU.1,eU.2.1,eU.2.2⟩,⟨fun i=> whitePay σ Γ u C₀ o i e v l ℓ sz (fun j=>(H j).clarity),fun i=>?_⟩⟩
 have p:=grayPay σ Γ u C₀ U o i e v h l (fun i=>(he i).1) (fun i=>(he i).2) pΩ hΩ ℓ sz (fun j=>(H j).clarity)
 apply le_trans p (le_of_eq ?_); congr 3
 rw[Q,Q,respite_1,respite_1]; unfold RedB ColdB; ring
end
end Rio
end YM.CF.Scree.Ing
end
