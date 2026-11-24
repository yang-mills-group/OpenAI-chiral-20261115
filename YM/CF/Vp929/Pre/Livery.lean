import YM.CF.Vp929.Pre.Minus
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
variable {m: Side}{Z:Set ℂ}
open Salt Vow Bake Larch Nor
open Mew Fief
abbrev writP : RegBudget m→ₗ[ℝ] RegBudget m := {
 toFun := writ_E
 map_add' := fun x y=> writ_k x y
 map_smul' := fun c X=>by
    unfold writ_E; have p(i:Sweep m) : base_Q i (c• X)=c • base_Q i X:= funext fun v=> funext fun U=> map_smul (suit_Y i⁻¹) c _; simp_rw [p,←smul_sum]; rw [smul_comm]; rfl }
abbrev writY : Cusp m→ₗ[ℝ] Cusp m := {
 toFun := writ_K
 map_add' := fun H G=>by
    unfold writ_K; have p(i:Sweep m): force_V i (H+G)= force_V i H + force_V i G:= funext fun v=>funext fun z=> funext fun U=> map_add ..; simp_rw [p,sum_add_distrib,smul_add]
 map_smul' := fun c X=>by
    unfold writ_K; have p(i:Sweep m): force_V i (c•X)= c • force_V i X:= funext fun v=>funext fun z=>funext fun U=>map_smul (suit_Y i⁻¹) c _; simp_rw [p,←smul_sum]; rw [smul_comm]; rfl }
-- Holo census and lift helpers. Also reusable for testing & future reading.
variable {B i j k:Type*}{E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E][FiniteDimensional ℂ E]
section
variable {G H:ℂ→ Pair (i→ j→ E)}(h:IsOpen Z)
include h
lemma Census.plus (A:Census Z G)(B:Census Z H):Census Z fun z=> G z+ H z:=by
 intro i j; exact (((A i j).form h).add ((B i j).form h)).holo h
lemma Census.minus (A:Census Z G)(B:Census Z H): Census Z fun z=> G z-H z:=by
 intro i j; exact (((A i j).form h).sub ((B i j).form h)).holo h
omit h
lemma Census.plus_curve (A:Census Z G)(i j):DifferentiableOn ℂ (fun z=> Pair.plus (G z) i j) Z:= (A i j).1
lemma Census.minus_curve (A:Census Z G)(i j):DifferentiableOn ℂ (fun z=> Pair.minus (G (star z)) i j) ((starRingEnd ℂ) ⁻¹' Z):= (A i j).2
lemma Census.recombine {F G:ℂ→i→j→E}(A:∀ i j,DifferentiableOn ℂ (fun z=>F z i j) Z)(B:∀ i j,DifferentiableOn ℂ (fun z=>G (star z) i j) ((starRingEnd ℂ) ⁻¹' Z)): Census Z fun z=> Pair.cat (F z) (G z):= by
 intro i j; exact holo_cat (A i j) (f:=fun z=> F z i j) (g:=fun z=> G z i j) (B i j)
include h
lemma Form.pointSum'' (I:Finset k)(F G:k→ℂ→E)(p:∀ i∈I,Holo Z (fun z=>(F i z,G i z))): Holo Z (fun z=>(∑ i∈I,F i z,∑ i∈I,G i z)):= ((form_ballot I Z _ (fun i hi=> (p i hi).form h))).holo h
end
lemma census_writ {G:ℂ→ Pair (RegBudget m)}(h:IsOpen Z)(p:Census Z G): Census Z fun z=>(writP (G z).1,writP (G z).2):=by
 intro i V
 let F(j:Sweep m)(z:ℂ): Pair (Cipher m):= (base_Q j (G z).1 i V,base_Q j (G z).2 i V)
 have hF(j:Sweep m): Form Z (F j):= ((p (moveHub j i) (flashA j V)).form h).probe ((suit_Y j⁻¹).toLinearMap.toContinuousLinearMap)
 change Holo Z (fun z=>(writ_E (G z).1 i V,writ_E (G z).2 i V)); unfold writ_E; simp_rw [Pi.smul_apply,Finset.sum_apply]; exact ((form_ballot univ Z F (fun i _=> hF i)).probe (plight_C m • ContinuousLinearMap.id ℝ (Cipher m))).holo h

lemma writ_bound_census {G:ℂ→ Pair (Cusp m)}(h:IsOpen Z)(p:Query (fun _=> Set.univ) Z G): Query (fun _=> Set.univ) Z fun z=>(writY (G z).1,writY (G z).2):=by
 intro i D _ V
 let F(j:Sweep m)(z:ℂ):Pair (Cipher m):= (force_V j (G z).1 i D V,force_V j (G z).2 i D V)
 have hF(j:Sweep m):Form Z (F j):= ((p (moldA j i) (actY j D) (Set.mem_univ _) (yellA j V)).form h).probe ((suit_Y j⁻¹).toLinearMap.toContinuousLinearMap)
 change Holo Z (fun z=>(writ_K (G z).1 i D V,writ_K (G z).2 i D V)); unfold writ_K; simp_rw [Pi.smul_apply,Finset.sum_apply]; exact ((form_ballot univ Z F (fun i _=> hF i)).probe (plight_C m • ContinuousLinearMap.id ℝ (Cipher m))).holo h
end YM.CF.Py.Rate
