import YM.CF.Rill.Latch
import YM.CF.Eire.Rig
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
variable {H:Gauge}
-- eligibility attached to non-default tests _only_; this data sees no active pay nor V. crucial for CAR forcing, analytic derivatives
variable {S}(M:Monk H S)(R:Stores S)(U:Config H f)
def chillB : Config H f:=fun i=> if i∈M.park.trunks then 1 else M.U i
def brushK (A:Stores S)(V:Config H f)(t:ℝ): Support f:= (A.costs.filter fun i=>t < toll V i).biUnion touched
protected lemma sketch(T:Tube H S)(x:ℝ)(q:Chi)(w:ℝ)(l:ℕ)(β:ℝ)(i:Bond f)(p:S.ratio.parent i.1∈M.key.dome (10*radiusB x)) : M.sent x T q w l β i=chillB M i:=by
 unfold chillB; split
 next h=> exact M.park.on_tree _ ⟨_,h⟩
 next h=> let j:Frozen M.key x M.park:=⟨⟨i,h⟩,Or.inl p⟩; exact held_physical x M.key M.park M.V (M.bush x) (M.fuel x T q w l β) j
lemma pageB (T:Tube H S)(x:ℝ)(q:Chi)(w:ℝ)(l:ℕ)(β:ℝ)(i:Cell f)(p:i∈M.key.costs):toll (M.sent x T q w l β) i= toll (chillB M) i:=by
 apply congrArg H.chord; exact travel_local i.1 _ _ _ (fun j v _=> Eire.sketch M T x q w l β j (halo_subset _ _ (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨i,p,mem_image_of_mem _ (List.mem_toFinset.mpr v)⟩)))))
lemma stampedB (T:Tube H S)(x:ℝ)(q:Chi)(w:ℝ)(l:ℕ)(β:ℝ)(t:ℝ):brushK M.key (M.sent x T q w l β) t= brushK M.key (chillB M) t:=by
 unfold brushK; refine congrArg (Finset.biUnion · touched) (Finset.filter_congr fun i p=> by rw [pageB M T x q w l β i p]) -- test
lemma wornG(k:Finset (Kite S r)): brushK (cook S k) U t=k.biUnion fun i=> brushK i.1.val U t:=by
 ext i; simp only [brushK,costs_g,mem_biUnion,mem_filter]; aesop -- tune
lemma wornB (k:Finset (Kite S r)): brushK (cook S k) U t ⊆ Passage S (k.biUnion fun i=> stem S i.1):=by
 rw [wornG]; apply biUnion_subset.mpr; intro i g y p; obtain ⟨c,u,v⟩:= mem_biUnion.mp p; exact mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr ⟨i,g,halo_subset _ _ (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨c,(mem_filter.mp u).1, mem_image_of_mem _ v⟩)))⟩⟩ -- tune
variable {q:Chi}{d β w x t s a B:ℝ}{J:ChartRatio SU.group}{T:Tube SU.group S}{k:ℕ}{l r:ℕ}
open Oriented
-- keep multiplication Qen * receipt: statements valid irrespective of A match
variable {J:ChartRatio SU.group}
lemma receipt (Z: Monk SU.group S)(u: (∏ i∈blip S Z.key r,Reine.treat T x Z q d l β J w s B r k i)≠0)(ht: Corne.Qen T x q d l Z β w s k ≠ 0)(hp:0<fiery SU.group x S.patch.L): let F:=Z.sent x T q d l β; ∀ i:Cell f,i∉ Z.key.costs →toll F i ≤ fiery SU.group x S.patch.L/2:=by
 intro F i g; let t:=fiery SU.group x S.patch.L; let L:=(k+110)* radiusB x
 by_cases hh:i∈nearFace S (Z.key.dome L)
 · obtain ⟨y,v,h⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp hh).2); obtain ⟨z,f,b⟩:= halo_spec.mp h; rw [←bloomE S Z.key r] at f; obtain ⟨O,u',f⟩:= mem_biUnion.mp f
   apply Rill.shave Z J hp (r:=r) (Finset.prod_ne_zero_iff.mpr fun _ t=> left_ne_zero_of_mul (left_ne_zero_of_mul ((Finset.prod_ne_zero_iff.mp u) _ t))) O u' i ?_ g -- tune hidden
   exact mem_filter.mpr ⟨mem_univ _,fun w=> disjoint_left.mp w v (halo_spec.mpr ⟨z,f,b⟩)⟩
 have he: (∏ i∈(nearFace S (Z.key.dome L))ᶜ, tokenF Z.key q x F i)≠0:=left_ne_zero_of_mul (right_ne_zero_of_mul ht); exact ((profile_charged q _ _ (by change 0<t/4; positivity) i ((Finset.prod_ne_zero_iff.mp he) i (mem_compl.mpr hh)) (SU.group.chord_nonneg _)).2 g).le.trans_eq (by ring)
lemma flags_K(t:ℝ)(p:∀ i,i∉ M.key.costs→toll U i ≤ t) : flags t U= brushK M.key U t:=by
 ext i; rw [flags_spec,brushK,mem_biUnion]; exact ⟨fun ⟨c,g,h⟩=> ⟨c,mem_filter.mpr ⟨by by_contra k; exact (p _ k).not_gt h,h⟩,g⟩,fun ⟨c,g,h⟩=> ⟨c,h,(mem_filter.mp g).2⟩⟩ -- tune
end YM.CF.Eire
