import YM.CF.Rill.Ice
import YM.CF.Atala.Bingo
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
variable {s a p:ℝ}{j n:ℕ}
open Atala
-- default group used only where capacity intersect; for differentiability need this even on topological support of entire recipe
abbrev looseV(x:ℝ)(M:Monk G S)(r:ℕ)(j:ℕ)(U:Config G f): Prop:= ∀ O∈ blip S M.key r,∀ i∈nearFace S (obv x j 110 O.val),i∉ M.key.costs → toll U i≤ fiery G x S.patch.L/2
lemma shave(M:Monk G S)(J:ChartRatio G)(h:0<fiery G x S.patch.L)(p: (∏ i∈blip S M.key r,M.pep x T t i.val q d l β w J j)≠0): looseV x M r j (M.sent x T q d l β):=by -- drop unnecessary U later
 intro O u i g v; let L:=M.sent x T q d l β; have hu: total M.key x q L (obv x j 110 O.val)≠0:=left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ((Finset.prod_ne_zero_iff.mp p) O u)))) -- tune
 let a:=fiery G x S.patch.L; have hp:0<a:=h; have ht:= (profile_charged _ _ _ (by positivity :0<a/4) i ((Finset.prod_ne_zero_iff.mp hu) i g) (SU.group.chord_nonneg (faceValue L i))).2 v; exact le_trans ht.le (le_of_eq (by ring))
-- in fact any flag mark local is EXACT only planted costs. Concretely on closure of positives firing.
lemma join_l (M:Monk G S){U:Config G f}(h:looseV x M r j U)(p:PaneL M E x e b U)(hδ:fiery G x S.patch.L<e)(hy:0<fiery G x S.patch.L): SeeW U e (Passage S E) (Passage S M.key.place):=by
 intro i u a v
 by_cases p':i∈ Passage S (M.key.dome (12*radiusB x)); swap; · exact Or.inl ((p.mindF _ u a v).resolve_right p')
 have hu:= (mem_filter.mp p').2; obtain ⟨z,t,l⟩:=halo_spec.mp hu; rw [← bloomE S M.key r] at t; obtain ⟨O,t,q⟩:=mem_biUnion.mp t; have he:S.ratio.parent i ∈ startPos S a:= mem_image_of_mem S.ratio.parent v
 by_cases hv: a∈M.key.costs
 · exact Or.inr (mem_filter.mpr ⟨mem_univ _, mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨a,hv,he⟩))⟩)
 apply Or.inl; apply lt_of_le_of_lt (h O t a ?_ hv) (lt_of_le_of_lt (half_le_self hy.le) hδ); refine mem_filter.mpr ⟨mem_univ _, fun v=> disjoint_left.mp v he (halo_spec.mpr ⟨z,q,?_ ⟩)⟩; simp_rw [Nat.add_mul]; omega
variable {α:Type}[TopologicalSpace α]
lemma loose_veil(M:Monk G S){f': α→ Config G f}{P':α→ℝ}{y:α}(s:∀ v∈ Function.support P', looseV x M r j (f' v))(h:y∈ tsupport P')(g:∀ O∈blip S M.key r,∀ i ∈nearFace S (obv x j 110 O.val), ContinuousAt (fun p=> toll (f' p) i) y): looseV x M r j (f' y):=by
 intro O k i u z; by_contra! t; have hp:= (g _ k _ u).eventually (lt_mem_nhds t); obtain ⟨v,w,h⟩:= mem_closure_iff_nhds.mp h _ hp; exact (s v h _ k i u z).not_gt w -- tune closure
end YM.CF.Rill
