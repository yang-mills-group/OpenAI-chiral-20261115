import YM.CF.Eire.Rule
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open scoped Classical
variable {L m:Side} (S:StepData L (More m))(x:ℝ)(R:GramM m)(V:Monk SU.group S)(k A:ℝ)(J:ChartRatio SU.group)(U:Ids m)(P:Tube SU.group S)(q:Chi)(d:ℝ)(l:ℕ)
open Pastry
attribute [local instance] opCStarAlgebra
-- old flags use full equality at intact, lifted clamp by smooth masks; guard only defaults
section
variable{t:Type*}[Fintype t][LinearOrder t]
lemma flourish {H:Finset t}{A: Dough t}(p: Flour H A.val): Flour H (exp A).val:=by
 let D:= stretch H; have ht:A∈ D:=p
 rw [exp_eq_tsum ℝ]; apply tsum_mem (D.toSubmodule.closed_of_finiteDimensional); -- tune
 exact fun i=> D.toSubmodule.smul_mem _ (D.pow_mem ht _)
lemma breed {c v M:Type*}[Fintype c][Fintype v][AddCommMonoid M](F:Finset (c⊕v)→M): ∑ i,F i=∑ p:Finset c,∑ q:Finset v,F (p.disjSum q):=by
 rw [← Fintype.sum_prod_type (f:=fun r:Finset c×Finset v=> F (r.1.disjSum r.2))]; symm; exact Equiv.sum_comp (Finset.sumEquiv.toEquiv.symm) F -- tune
end
local notation "θ"=> R.p.threshold
local notation "H"=> V.sent x P q d l R.beta
local notation "I"=> brushK V.key (chillB V) θ
abbrev inspectD(Y:Support (More m)) : Finset (Cell (More m)):= univ.filter fun i=> ¬ Disjoint Y (touched i)
def guardB (Y:Support (More m)):ℝ:= ∏ i∈(inspectD Y)\V.key.costs, q.read ((toll H i / (θ/2))^4)
section
variable {I':Force m}
def warmY (W:Support (More m)): Prop:=∀ i∈ V.key.costs, i∈ inspectD W → toll (chillB V) i < θ
def shineK (Z:Force m): Cipher m:= let E:=Z.val.1.val.2 \ Z.val.2; if warmY S R V E then guardB S x R V P q d l E • R.K Z (H,U) else 0
def juice (Z: Roc m):= numbE θ Z.1.val.2 (if Z.2 then R.F Z.1 else R.slip Z.1) H
def sheer (Z:Roc m): Cipher m:=let E:=Z.1.val.2; if warmY S R V E then guardB S x R V P q d l E • (exp (if Z.2 then R.F Z.1 H else R.slip Z.1 H)-1) else 0
def CostsB(t:Set (Finset (Rust m))):= t -- tune
end
abbrev SubmitB:=∀ i,i∉ V.key.costs → toll H i ≤ θ/2
variable (h:SubmitB S x R V P q d l)
include h
lemma shin_g(Y:Support (More m)) : guardB S x R V P q d l Y=1:= by
 apply prod_eq_one; intro i g; have ht:= h i (mem_sdiff.mp g).2; exact q.to_one _ (pow_le_one₀ (div_nonneg (SU.group.chord_nonneg _) (half_pos R.p.threshold_pos).le) ((div_le_one (half_pos R.p.threshold_pos)).mpr ht))
lemma shin_h: Healthy θ (∅:Support (More m)) H:=by simp [Healthy] -- tune
lemma shin_u(Y:Support (More m)) : warmY S R V Y↔ pingS θ Y H:=by
 constructor
 · intro p i g; by_cases v:i∈V.key.costs
   · change toll H i<_; rw [pageB V P x q d l R.beta i v]; exact p i v (mem_filter.mpr ⟨mem_univ _,g⟩)
   exact (h i v).trans_lt (half_lt_self R.p.threshold_pos)
 intro p i v g; rw [←pageB V P x q d l R.beta i v]; exact p i (mem_filter.mp g).2
lemma shine_a (Z:Force m): shineK S x R V U P q d l Z=Scree.clamp R.p Z (R.K Z) (H,U):=by
 unfold shineK Scree.clamp boundF; dsimp only; simp only [shin_u S _ _ _ _ _ _ _ h,shin_g S _ _ _ _ _ _ _ h,one_smul]
lemma shine_b (Z:Roc m): sheer S x R V P q d l Z= exp (juice S x R V P q d l Z)-1:=by
 unfold sheer juice; dsimp only; letI : NormedAlgebra ℚ (Cipher m):= NormedAlgebra.restrictScalars ℚ ℝ (Cipher m); simp only [shin_g S _ _ _ _ _ _ _ h,shin_u S _ _ _ _ _ _ _ h]; split
 next hx=> rw [numbE, Set.indicator_of_mem (show H∈ _ from hx),one_smul]; split<;>rfl
 next hx=> rw [numbE, Set.indicator_of_notMem (show H∉ _ from hx),NormedSpace.exp_zero,sub_self]
lemma sheer_sum: ∑ i:Finset (Roc m), (∏ j∈i, sheer S x R V P q d l j)= exp (exponentL R.p R.F H+exponentL R.p R.slip H):=by
 let Q:=sheer S x R V P q d l; let Q':=juice S x R V P q d l; rw [← powerset_univ (α:= Roc m),←prod_one_add]; have ht(j):1+Q j=exp (Q' j):=by rw [show Q j=exp (Q' j)-1 from shine_b S x R V P q d l h _]; ring
 -- tune Prod.E.X Normed
 change ∏ i:Roc m, (1+Q i)=_; simp_rw [ht]; letI : NormedAlgebra ℚ (Cipher m):= NormedAlgebra.restrictScalars ℚ ℝ (Cipher m); rw [←NormedSpace.exp_sum]; congr 1; rw [Fintype.sum_prod_type]; unfold exponentL; rw [←sum_add_distrib]; apply sum_congr rfl; intro i g; unfold Q' juice; simp
lemma shine_sum: ∑ i∈(Finset.univ:Finset (Finset (Force m))).filter (fun i:Finset (Force m)=> (i.biUnion (fun x=> x.val.2)=I ∧ Set.PairwiseDisjoint (i:Set (Force m)) fun x=>x.val.1.val.2)), (∏ j∈ i,shineK S x R V U P q d l j)= fueled R.p R.K (H,U):=by -- rendL only mid A B! must generalize
 rw [Scree.fueled,sum_filter]; apply sum_congr rfl; intro i _; have hF:I=flags θ H:=by rw [←stampedB,←flags_K V H θ (p:=fun i v=>(h i v).trans (half_le_self R.p.threshold_pos.le))] -- tune
 simp only [shine_a _ _ _ _ _ _ _ _ _ h,hF, coverF]
end YM.CF.Eire
