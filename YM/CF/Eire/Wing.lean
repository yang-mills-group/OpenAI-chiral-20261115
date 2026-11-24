import YM.CF.Eire.Wilt
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
open Pastry Peaks
attribute [local instance] opCStarAlgebra
variable {m c:Side} (S:StepData c (More m))(x:ℝ)(R:GramM m)(V N:Monk SU.group S)(J:ChartRatio SU.group)(U W:Ids m)(P:Tube SU.group S)(q:Chi)(d:ℝ)(l:ℕ)
local notation "θ"=> R.p.threshold
local notation "H"=> V.sent x P q d l R.beta
local notation "K"=> N.sent x P q d l R.beta
local notation "I"=> brushK V.key (chillB V) θ
abbrev OpK : Rust m → Cipher m:= Sum.elim (sheer S x R V P q d l) (shineK S x R V U P q d l)
def lure (F:Finset (Rust m)): Cipher m:= ∏ i∈F,OpK S x R V U P q d l i
lemma fleet_p(h:SubmitB S x R V P q d l): R.board (H,U)=∑ F∈(Finset.univ:Finset (Finset (Rust m))).filter (fun F:Finset (Rust m)=> F.toRight.biUnion (fun i=> i.val.2)=I ∧ Set.PairwiseDisjoint (F.toRight:Set (Force m)) fun i=> i.val.1.val.2), lure S x R V U P q d l F:=by
 rw [GramM.board,← sheer_sum S _ _ _ _ _ _ _ h,← shine_sum _ _ _ _ _ _ _ _ _ h,sum_mul]; conv_rhs=> rw [sum_filter,breed]
 apply sum_congr rfl; intro i _; rw [mul_sum]; simp only [toRight_disjSum]; rw [sum_filter]; apply sum_congr rfl; intro j _; split_ifs with g; rw [lure, Finset.prod_disjSum]; rfl; rfl -- tune
structure Copies (R:GramM m):Prop where
 capital:∀ i: Hub m,∃ a b, PressB R.p i (R.F i) a b
 heritage:∀ i:Hub m,∃ a b, PressB R.p i (R.slip i) a b
 forced:∀ i:Force m, ∃ a b, ForceB R.p i (R.K i) a b
lemma witnessH (v: Copies R)(F:Rust m): Flour (camp (rustL _ F).val.2) (OpK S x R V U P q d l F).val:=by
 rcases F with i|i
 · change Flour (camp i.1.val.2) (sheer S x R V P q d l i).val; unfold sheer; dsimp only; split; swap; · exact Flour.trivial
   apply Flour.rsmul; apply (stretch_ok _).mp; apply Subalgebra.sub_mem; swap; · exact Subalgebra.one_mem _
   apply (stretch_ok _).mpr; apply flourish; split
   next _=> obtain ⟨a,b,p⟩:= v.capital i.1; exact p.fitted _
   next _=> obtain ⟨a,b,p⟩:= v.heritage i.1; exact p.fitted _
 change Flour (camp i.val.1.val.2) (shineK S x R V U P q d l i).val; unfold shineK; dsimp only; split
 · obtain ⟨a,b,p⟩:= v.forced i; apply Flour.rsmul; exact p.fitted _
 exact Flour.trivial
variable {X:Support c}{Y Z:Support (More m)}(h:Duo SU.group S V N X)(p:Ready P x)(he:1000 ≤ radiusB x)(hf: halo ((l+75)*radiusB x) (hatY S (inspected Y))⊆X)
include h p he hf
lemma grass_a (i:Cell (More m))(hq:i ∈ inspectD Y): toll H i=toll K i ∧ (i∈ V.key.costs↔ i∈N.key.costs):=by
 let y:=S.ratio.parent i.1; have hh:y∈ hatY S (inspected Y):= by apply mem_image_of_mem; refine mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩); rw [if_neg ((mem_filter.mp hq).2)]; exact Work.E01.base_touched i -- tune
 have ht:i.1∈touched i:=Work.E01.base_touched i; refine ⟨congrArg SU.group.chord (h.foot_t p he i (Subset.trans ?_ hf)), h.cost i (fun q=> disjoint_left.mp q (mem_image_of_mem _ ht) (hf (halo_subset _ _ hh)))⟩
 exact Corona.halo_mono (Nat.mul_le_mul_right _ (by omega)) (singleton_subset_iff.mpr hh)
lemma guard_equal(u:Z⊆Y): guardB S x R V P q d l Z=guardB S x R N P q d l Z ∧ (warmY S R V Z ↔ warmY S R N Z):=by
 have ht(i)(v:i∈inspectD Z):= grass_a S x R V N P q d l h p he hf i (mem_filter.mpr ⟨mem_univ _,fun k=> (mem_filter.mp v).2 (k.mono_left u)⟩); have ho: inspectD Z \ V.key.costs =inspectD Z \ N.key.costs:= Finset.ext fun i=>mem_sdiff.trans ((and_congr_right fun v=>not_congr (ht i v).2).trans mem_sdiff.symm)
 refine ⟨prod_congr ho fun i g=> ?_,?_⟩ -- tune orientation
 · rw [(ht _ (mem_sdiff.mp g).1).1]
 constructor
 · intro f i k t; let v:= (ht i t).2.mpr k; rw [←pageB N P x q d l R.beta i k,←(ht _ t).1,pageB V P x q d l R.beta i v]; exact f i v t
 intro f i k t; let v:=(ht i t).2.mp k; rw [←pageB V P x q d l R.beta i k,(ht _ t).1,pageB N P x q d l R.beta i v]; exact f i v t
lemma heard  : Agrees Y H K:=by
 intro i v t; have hp:S.ratio.parent i.1∈hatY S (inspected Y):= mem_image_of_mem _ (mem_union_left _ (show i.1∈ Y from v)); exact h.toBeat.backF p he i (Subset.trans (Corona.halo_mono (Nat.mul_le_mul_right _ (by omega)) (singleton_subset_iff.mpr hp)) hf)
omit hf
lemma earnR (v:Copies R)(F:Rust m)(u:halo ((l+75)*radiusB x) (hatY S (inspected (rustL m F).val.2))⊆ X)(k:Set.EqOn U W ((rustL m F).val.2)): OpK S x R V U P q d l F=OpK S x R N W P q d l F:=by
 let hh:=heard S x R V N P q d l h p he u
 rcases F with i|i
 · obtain ⟨a,b,r⟩:=v.capital i.1; obtain ⟨c,d',z⟩:=v.heritage i.1; obtain ⟨g,t⟩:= guard_equal S x R V N P q d l h p he u (Subset.refl _); change sheer S x R V P q d l i= sheer S x R N P q d l i; let Y:=i.1.val.2; simp only [rustL,Sum.elim_inl] at g t; unfold sheer; dsimp only; have he0:= r.term _ _ hh; have hz:= z.term _ _ hh; simp only [g,t, he0, hz] -- tune Y
 let Y:=i.val.1.val.2; obtain ⟨a,b,r⟩:= v.forced i; obtain ⟨g,t⟩:=guard_equal S x R V N P q d l h p he u (sdiff_subset (t:=i.val.2)); change shineK S x R V U P q d l i=shineK S x R N W P q d l i; unfold shineK; dsimp only; have he0:=r.values _ _ _ _ hh k; simp only [rustL,Sum.elim_inr] at t g; simp only [g,t,he0]
end YM.CF.Eire
