import YM.CF.Scion.Emp
import YM.CF.Corne.Pink
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
variable {c f:Side}(S:StepData c f){s v r:ℕ}{t:ℝ}
-- finite coarse incidence explicit order prior-based later, occupancy before inverse, post-flag gate afterwards
variable {C F:Type*}[DecidableEq C][DecidableEq F]
lemma gem{X X' Y Y':Finset C}{A B:Finset C}(g:Disjoint A B)(p:X⊆ A)(q:Y⊆ A)(u:X'⊆ B)(v:Y'⊆ B):X∪ X'=Y∪ Y'↔ X=Y∧X'=Y':=by
 have hu{X X' Y Y' A B:Finset C}(g:Disjoint A B)(p:X⊆A)(q:Y'⊆ B)(w:X∪X'=Y∪Y') : X⊆ Y:=fun x h=> (mem_union.mp (w ▸ mem_union_left X' h)).resolve_right fun t=> disjoint_left.mp g (p h) (q t)
 refine ⟨fun w=> ⟨(hu g p v w).antisymm (hu g q u w.symm),?_⟩, fun ⟨l,t⟩=>congrArg₂ _ l t⟩; rw [union_comm X,union_comm Y] at w; exact (hu g.symm u q w).antisymm (hu g.symm v p w.symm)
lemma gloss{f:C→ Finset F}{A B:Finset C}(p:∀ i∈A,∀ j∈B, i≠j → Disjoint (f i) (f j)): Set.PairwiseDisjoint (↑(A∪B)) f ↔ Set.PairwiseDisjoint (↑A) f∧Set.PairwiseDisjoint (↑B) f:=by
 constructor; intro v; refine ⟨v.subset (coe_subset.mpr (subset_union_left)),v.subset (coe_subset.mpr subset_union_right)⟩ -- tune
 rintro ⟨u,v⟩ i g j t q; rcases (mem_union.mp g) with l|l<;> rcases mem_union.mp t with h|h; exact u l h q; exact p i l j h q; exact (p _ h _ l q.symm).symm; exact v l h q
variable {H:Gauge}
abbrev Kite(S:StepData c f)(v:ℕ):= Hos S v × Support f × Support f
abbrev liftK (X:Finset (Kite S r)):=X.image Prod.fst
def pureK(X:Finset (Kite S r)):Prop:= Set.PairwiseDisjoint (X:Set (Kite S r)) (fun i=>stem S i.1)
lemma proud_p (X: Finset (Kite S r))(p:pureK S X): Set.InjOn Prod.fst (X:Set (Kite S r)):=by
 rintro i v j t h; by_contra k; obtain ⟨l,u⟩:=stem_p S i.1; exact disjoint_left.mp (p v t k) u (show l∈stem S j.1 from (congrArg (stem S) h) ▸ u)
lemma proud (X:Finset (Kite S r))(p:pureK S X): Set.PairwiseDisjoint ((liftK S X):Set (Hos S r)) (stem S):=by
 intro i v j t g; obtain ⟨l,h,rfl⟩:=mem_image.mp v; obtain ⟨r,q,rfl⟩:=mem_image.mp t; exact p h q (fun e=> g (congrArg Prod.fst e))
def cook (X:Finset (Kite S r)):=Esti.Pear S (liftK S X)
lemma cooked(X: Finset (Kite S r))(p:pureK S X): blip S (cook S X) r= liftK S X:=stem_u S _ (proud S X p)
lemma wears(X:Finset (Kite S r)) : plots (cook S X)=X.biUnion (fun i=>plots i.1.val):=by rw [cook,Pear, vase_c,liftK]; ext; simp -- tune
lemma flags_g (X:Finset (Kite S r)): (cook S X).flags=X.biUnion (fun i=>i.1.val.flags):=by ext i; simp [cook,Pear, liftK,vase, vase_a S] -- tune
lemma costs_g (X:Finset (Kite S r)): (cook S X).costs=X.biUnion (fun i=>i.1.val.costs):=by ext i; simp [cook,Pear, liftK,vase,vase_a S]
abbrev hatY(Y:Support f):Support c:=Y.image S.ratio.parent
def frameP (X:Kite S r):Support c:= stem S X.1 ∪ hatY S (danceL S X.1.val r∪ X.2.1∪ X.2.2) -- Atala
lemma frame_s(X:Kite S r):stem S X.1⊆ frameP S X:=subset_union_left
end YM.CF.Eire
