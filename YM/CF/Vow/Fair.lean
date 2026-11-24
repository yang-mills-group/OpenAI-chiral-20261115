import YM.CF.Vow.Roll
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
variable {X D Y Z:Support (More n)}{U:Pane n}
-- all seeds use child scales $Y∈H$. cost numerator.Post.S.Unit. equations read even if paux markers.H.St.
open Trees
variable {K W:Cusp n}
abbrev blazeK(n:Side):= Aura n→ Support (More n)→ ℝ
variable {C:blazeK n}{G:Aura n→ℝ}
variable(S:Aura n)(T:Finset (Palot.Duo (More n))) (p:D⊆S.val)
abbrev pill (X:Aura n)(C:blazeK n)(G:Aura n→ℝ)(D:Support (More n))(T:Finset (Palot.Duo (More n))): ℝ:= if lumpD T D X then (∏ i∈T.toLeft,C i (D∩i.val))*∏ j∈T.toRight,G j else 0
abbrev windF (C:blazeK n)(G:Aura n→ℝ): blazeK n:= fun x D=>∑ i:Finset (Palot.Duo (More n)), pill x C G D i
lemma trunk_L (hp:lumpD T D S):robe T.toLeft∪robe T.toRight=S.val:=by rw [rim_beat,hp.1,bay_beam]
lemma stun_v (hp:lumpD T D S)(L:Aura n)(v:L∈T.toLeft): (D∩L.val).Nonempty ∧ L.val⊆ S.val:=⟨let h:=hp.2.2.1 L v; Finset.not_disjoint_iff_nonempty_inter.mp (fun g=>h g.symm),fun i u=> trunk_L S T hp ▸ mem_union_left _ (show i∈ robe T.toLeft from mem_biUnion.mpr ⟨_,v,u⟩) ⟩
lemma strum_v (hp:lumpD T D S)(L:Aura n)(v:L∈T.toRight): L.val⊆ S.val:= fun i u=> trunk_L S T hp ▸ mem_union_right _ (show i∈ robe T.toRight from mem_biUnion.mpr ⟨_,v,u⟩)
include p
lemma deck_r (hp:lumpD T D S): ∀ i∈ D,∃ j∈ T.toLeft,i∈ D∩j.val:=by
 let U:=Stilo.bay (beatB T); have ht: U=S.val:=by unfold U; rw [hp.1,bay_beam]
 intro i v; obtain ⟨j,u,f⟩:=mem_biUnion.mp (hp.2.2.2.2 (show i∈ D∩U from mem_inter.mpr ⟨v,ht.symm ▸ p v⟩)); exact ⟨_,u,mem_inter.mpr ⟨v,f⟩⟩
lemma grantP (t: Aura n)(v:t.val ⊆ S.val) : t.val \ (D∩t.val) ⊆ S.val\D:=fun i u=>let q:=mem_sdiff.mp u; mem_sdiff.mpr ⟨v q.1,fun h=> q.2 (mem_inter.mpr ⟨h,q.1⟩)⟩
variable (j: ArmsK P K C h)(G':∀ i:Aura n,∀ D:Support (More n),D ⊆ i.val → Medal P i.val D (W i D) h (G i))
include j
lemma enough_v (V:Orbit n)(g:gemB D K W T (beamH S.val) V ≠0): lumpD T D S ∧ inspected D⊆ S.val ∧ D⊆ flags P.threshold V.1:=by
 rw [gear_v] at g; split at g; swap; · exact False.elim (g rfl)
 rename_i h
 have ht(y:Aura n)(t:y∈T.toLeft): inspected (D∩y.val)⊆ y.val ∧ D∩y.val ⊆ flags P.threshold V.1 := by
    let Y:= D∩y.val
    have hp:K y Y V≠0:=by
       intro z; apply g; rw [Pi.mul_apply,Finset.prod_apply,prod_eq_zero t z, zero_mul]
    let P:= j.claim y Y (stun_v S T h y t).1 inter_subset_right; exact ⟨by_contra fun g=> hp ((congrFun (P.readV g) V).trans rfl), P.litK V hp⟩
 have hh:=deck_r S T p h
 refine ⟨h,fun i y=>?_ ,fun i u=>?_⟩
 · rcases mem_union.mp y with z|z; exact p z
   obtain ⟨k,-,z⟩:= mem_biUnion.mp z; split at z; rename_i g'; · exact False.elim (notMem_empty _ z)
   rename_i u; obtain ⟨x,t,c⟩:= not_disjoint_iff.mp u; obtain ⟨m,e,b⟩:= hh x t; refine (stun_v S T h m e).2 ((ht m e).1 (mem_union_right _ (mem_biUnion.mpr ⟨k,mem_univ _, ?_⟩))); rw [if_neg fun w=> Finset.disjoint_left.mp w b c]; exact z
 obtain ⟨v,w,s⟩:= hh i u; exact (ht v w).2 s
include G'
lemma theme_v (hy:0 ≤ h): Medal P S.val D (gemB D K W T (beamH S.val)) h (pill S C G D T) :=by
 rw [gear_v,pill]; split_ifs with t
 · refine Medal.cross (Medal.prodP _ _ _ (fun i q=> ?_) hy) (Medal.prodP _ _ _ (fun i q=> ?_) hy) hy
   · obtain ⟨y,g⟩:= stun_v S T t i q; exact (j.price i (D∩i.val) y inter_subset_right).stretchB g inter_subset_left (grantP S p _ g)
   let w:= strum_v S T t i q; exact (G' i (D∩i.val) inter_subset_right).stretchB w inter_subset_left (grantP S p _ w)
 exact Medal.zeroT
omit p
lemma trialsB (t:0 ≤ h): ArmsK P (glowV K W) (windF C G) h:=by
 refine ⟨fun i D v p=> ?_ ,fun i D v p=>?_ ⟩
 · unfold glowV windF; rw [if_pos p]; exact Medal.sumP _ _ _ (fun T _=> theme_v i T p j G' t)
 have he(V:Orbit n)(w:glowV K W i D V≠0): inspected D ⊆ i.val∧ D ⊆ flags P.threshold V.1:=by
    unfold glowV mintF at w; rw [if_pos p,Finset.sum_apply] at w; obtain ⟨T,-,g⟩:=exists_ne_zero_of_sum_ne_zero w; exact (enough_v i T p j V g).2
 exact ⟨fun v=> funext fun i=> by by_contra l; exact v (he i l).1,fun V t=> (he V t).2⟩
end YM.CF.Vow
