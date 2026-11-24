import GaugeFieldConstruction.PesoL
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
open Pastry
section
variable {n:Side}{α β I E:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β]
variable (σ:I→ Seat n) {S:α→ Support (More n)} {z:β→Force n}
variable {X J K:Type}[Fintype X][DecidableEq X][Fintype J][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
omit [Fintype α] [Fintype β] in
lemma κClipSum (q:J→List I)(F:J→K→E)(g:J→X)(x:K)(L:X):Kin σ (fun z=>(∑ i:J,Canz σ _ (clipK σ (g i) (q i) (F i)) z) L x) (fun z=>∑ j∈univ.filter (fun i=>g i=L), carR z (q j) • F j x):=by
 simp_rw [Finset.sum_apply,sum_filter]
 apply loft_bank; intro j _
 have ht:= KinClip σ (g j) L (F j) x (q j); by_cases d:g j=L
 · simp_rw [if_pos d]; simpa only [if_pos d.symm] using ht -- simpa needs only Bool.S.
 simp_rw [if_neg d]; simpa only [if_neg (Ne.symm d)] using ht
namespace Grotto
variable (A:Grotto I S z)(p:BudgetPoint)
local notation "K"=> Key I
local notation "Ψ"=>Heart A.anchor S A.needs
local notation "T"=> Legist A.anchor S A.needs
local notation "B" i:max=> Base z (T i) A.flag
local notation "X" i:max=> roost z (T i) A.flag
variable (U:Orbit n)(x:Key I→ β→ Cipher n)(hv:∀ i:β,River (fun z=>x z i))
local notation "Ω"=> flags p.threshold U.1
omit hv
private lemma jet_transfer(x:Force n→ Cipher n){I:Type}[Fintype I]{A:I→ForceBudget n}:
 sparkJet Ω x (fun i=>(∑ j:I,A j) i U)=∑ j:I,sparkJet Ω x (fun i=>A j i U):=by
 rw[←map_sum]; congr 1; funext i; simp [Finset.sum_apply]
include hv
private def upsilon (i:Heart A.anchor S A.needs) :=∑ j:B i, clipK σ ((X i) j) (A.fromB i j.val) (A.termB i j.val)
set_option maxHeartbeats 100000 in
lemma queenSpec (j:Ψ):Kin σ (fun y=>sparkJet Ω (PourUp z (x y)) (fun i=>Canz σ _ (upsilon σ A j) y i U)) (fun y=> A.goBoat p y (x y) U j):=by
 let X':=X j; let G(y)(i:B j):=carR y (A.fromB j i.val)• A.termB j i.val U
 have he(i):River (fun y=>PourUp z (x y) i):=(tip_bank _ _ (fun j _=>hv j)).1
 let f(y)(i:Force n):=(∑ r:B j,Canz σ _ (clipK σ (X' r) (A.fromB j r.val) (A.termB j r.val)) y) i U
 have hp:∀ i,Kin σ (fun y=>f y i) (fun y=>PourUp X' (G y) i):=fun i=> κClipSum σ (fun p:B j=>A.fromB j p.val) (fun p:B j=> A.termB j p.val) X' U i
 -- lhs after simp issue rewrote SECOND can_pour & jet_transfer all way -> sum sparkJet x f_j. rewrite grouped via ₹.
 have ht:=sparkKin σ Ω (fun y=>PourUp z (x y)) f (fun y=>PourUp X' (G y)) he hp
 have hh(y:Mew.Key I): sparkJet Ω (PourUp z (x y)) (PourUp X' (G y))=A.goBoat p y (x y) U j:= mural z (T j) A.flag (x y) (G y) Ω (fun i:Finset β=>carR y (A.fromB j i)• A.termB j i U) (fun _=>rfl)
 have e(y i): Canz σ _ (upsilon σ A j) y i U=f y i:=by unfold upsilon; rw [can_pour]
 simp_rw[e,← hh]; exact ht
lemma queenK : Kin σ (fun y=>sparkJet Ω (PourUp z (x y)) (fun i=> Canz σ _ (Kinc σ A) y i U)) (fun y=>∑ j:Ψ,A.goBoat p y (x y) U j):=by
 have V(y):sparkJet Ω (PourUp z (x y)) (fun i=> Canz σ _ (Kinc σ A) y i U)=∑ j:Ψ, sparkJet Ω (PourUp z (x y)) (fun i=>Canz σ _ (upsilon σ A j) y i U):=by
    rw [show Kinc σ A=∑ j:Ψ,upsilon σ A j from rfl,can_pour]; exact jet_transfer p U _
 simp_rw[V]; exact loft_bank _ _ (fun j _=> A.queenSpec σ p U x hv j)
lemma turnoverPack (v:Rue.FleetS p.threshold U.1): Kin σ
 (fun y=> exponentL p (Canz σ _ (A.Rinc σ) y) U.1 * hum Ω id (PourUp z (x y)) +sparkJet Ω (PourUp z (x y)) (fun i=>Canz σ _ (A.Kinc σ) y i U))
 (fun y=> A.cashVector p y (x y) U):=by
 simp_rw [Hum_split]
 apply loft_add _ (queenK σ A p U x hv)
 apply Kin.mulT (BringR _ _ _ _ v) (Kin.refl _ _)
 unfold hum; apply (tip_bank _ _ _).1 -- tune
 intro i bill; clear bill; induction i using Finset.induction with
 | empty=> simp only [prod_empty]; exact zeroR _
 | insert i s t ih=> simp_rw [prod_insert t]; exact (hv i).mul_T ih
#print axioms turnoverPack
end Grotto
end
end YM.CF.Scree.Ing
end
