import YM.CF.Esti.Auto
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){A B:Stores S}{r v:ℕ}
open CF.Jet
variable {S}{F:Forest S.ratio}{i:Bond c}{q:Chi}{x w:ℝ}
def onS (A:Stores S)(x:ℝ)(i:Bond c): Prop:= pinPos i⊆ A.dome (9*radiusB x)
def onF (A:Stores S)(x:ℝ)(i:Site c):Prop:=i ∈ A.dome (9*radiusB x-1)
lemma price_pin(i:Bond c){p q:Site c}(h:p∈pinPos i)(v:q∈pinPos i): separation p q ≤ 1:=by
 rcases Finset.mem_insert.mp h with rfl|h<;> rcases Finset.mem_insert.mp v with rfl|v
 simp
 rw [mem_singleton.mp v]; exact Work.E01.sep_step_le ..
 rw [separation_comm, mem_singleton.mp h]; exact Work.E01.sep_step_le ..
 rw [mem_singleton.mp h,mem_singleton.mp v]; simp
abbrev shovel (K: Patch):=gun K + 25
lemma beam_up (S:StepData c f)(i:Bond c)(g:Site c)(hx:g∈pinPos i)(z:Cell f)(hp:z∈nearT S i):∀ y∈startPos S z,separation g y ≤ shovel S.patch:=by
 intro y hy; obtain ⟨x,p,r⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp hp).2); obtain ⟨c,v,rfl⟩:= Finset.mem_image.mp hy; obtain ⟨k,t,w⟩:=mem_biUnion.mp p; obtain ⟨j,hj,w⟩:=halo_spec.mp w; subst_eqs
 let P:= S.ratio; have ht:separation k (P.parent x) ≤ (gun S.patch+1)+1:=by
    nth_rw 1 [←Ratio.embed_parent P k]; apply (Work.E04.parent_separation ..).trans; have hp : j=P.embed k:=mem_singleton.mp hj; rw [hp] at w; omega
 refine (separation_triangle _ (P.parent x) _).trans ((Nat.add_le_add ((separation_triangle _ k _).trans (Nat.add_le_add (price_pin _ hx t) ht)) (Work.E04.parent_separation ..)).trans ?_); have he:=separation_triangle x z.1 c; rw [separation_comm x z.1] at he; have hp:=Work.E01.sep_touched z x r; have hg:=Work.E01.sep_touched z c v; unfold shovel; omega
lemma bubble (hp: shovel S.patch+10 ≤ radiusB x)(hb: ¬onS A x i){z:Cell f}(hx:z∈nearT S i):z∉A.costs:=by
 obtain ⟨q,t,k⟩:= Set.not_subset.mp hb -- tune
 intro s; let p:= S.ratio.parent z.1; have hg:p∈ startPos S z:= mem_image_of_mem _ (Work.E01.base_touched z); have hx:= beam_up S i q t z hx p hg
 refine k (halo_spec.mpr ⟨p,?_,?_⟩); swap; · rw [separation_comm]; omega
 exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨z,s,hg⟩))
lemma bubbleF {k:Site c}(hp: shovel S.patch+10 ≤ radiusB x)(hb: ¬onF A x k)(hk:k∈pinPos i){z:Cell f}(hx:z∈nearT S i):z∉A.costs:=by
 intro s; let p:= S.ratio.parent z.1; have hg:p∈ startPos S z:= mem_image_of_mem _ (Work.E01.base_touched z); have hx:= beam_up S i k hk z hx p hg
 refine hb (halo_spec.mpr ⟨p,?_,?_⟩); swap; · rw [separation_comm]; omega
 exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨z,s,hg⟩))
lemma tuck (hp:shovel S.patch+10 ≤ radiusB x){p:Site c}(h:onF A x p){i:Bond c}(v:p∈pinPos i):onS A x i:=by
 intro q u
 obtain ⟨z,t,h⟩:=halo_spec.mp h; have he:=price_pin _ v u
 exact halo_spec.mpr ⟨z,t,(separation_triangle _ p _).trans (by omega)⟩
lemma husk(hp:shovel S.patch+10 ≤ radiusB x)(h:onS A x i) (e:Active A x F):¬ (e.val.val.1 ∈ sideP S i) :=by
 intro g; obtain ⟨q,t,v⟩:=halo_spec.mp (h (mem_insert_self i.1 _)); have ht:=Psalm.home_reaches g
 refine remote e (halo_spec.mpr ⟨q,t,(separation_triangle _ i.1 _).trans (by unfold shovel gun at hp; unfold Psalm.stride at ht; omega)⟩)
-- actual V extent for isolated core declarations
abbrev total (A:Stores S)(x:ℝ)(q:Chi)(U:Config SU.group f)(X:Support c):= ∏ i∈nearFace S X, tokenF A q x U i
lemma withinReach (O:Stores S)(Y:Support c)(h:O.dome v ⊆ Y)(r:ℕ)(l:r+shovel S.patch ≤ v)(g:i∈nearNoise (O.dome r)): nearT S i⊆ nearFace S Y:=by
 obtain ⟨k,p,t⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp g).2); obtain ⟨e,u,z⟩:=halo_spec.mp t; intro j b
 have hg:S.ratio.parent j.1∈ startPos S j:=mem_image_of_mem _ (Work.E01.base_touched j); have ht:=beam_up S i k p j b _ hg
 exact mem_filter.mpr ⟨mem_univ _,fun x=> disjoint_left.mp x hg (h (halo_spec.mpr ⟨_,u,(separation_triangle _ k _).trans (by omega)⟩))⟩
lemma yes_z(hp:shovel S.patch+10 ≤ radiusB x)(l:r+shovel S.patch ≤ v)(g:i∈nearNoise (B.dome r))(U:Config SU.group f)(X:Support c)(hq:B.dome v⊆ X)(ha:0<fiery SU.group x S.patch.L)(b: ¬onS A x i)(hb:total A x q U X≠0):ResV S (a:=fiery SU.group x S.patch.L) i U:=by -- need Ambient A ≠ B normally; remove
 rw [charged]; intro z V; let a:=fiery SU.group x S.patch.L; have hZ:tokenF A q x U z≠0:=fun p=> hb (Finset.prod_eq_zero (withinReach _ _ hq _ l g V) p)
 have he:= bubble hp b V; have hh : Pressure.toll U z < 2*(a/4):=(profile_charged _ _ _ (by positivity :0<a/4) _ hZ (SU.group.chord_nonneg _)).2 he
 change Pressure.toll U z ≤ a; change 0<a at ha; linarith only [hh,ha]
lemma yes_f {k:Site c}(hp:shovel S.patch+10 ≤ radiusB x)(l:r+shovel S.patch ≤ v)(g:i∈nearNoise (B.dome r))(U:Config SU.group f)(X:Support c)(hq:B.dome v⊆ X)(ha:0<fiery SU.group x S.patch.L)(b: ¬onF A x k)(p:k∈pinPos i)(hb:total A x q U X≠0):ResV S (a:=fiery SU.group x S.patch.L) i U:=by -- need Ambient A ≠ B normally; remove
 rw [charged]; intro z V; let a:=fiery SU.group x S.patch.L; have hZ:tokenF A q x U z≠0:=fun p=> hb (Finset.prod_eq_zero (withinReach _ _ hq _ l g V) p)
 have he:= bubbleF hp b p V; have hh : Pressure.toll U z < 2*(a/4):=(profile_charged _ _ _ (by positivity :0<a/4) _ hZ (SU.group.chord_nonneg _)).2 he
 change Pressure.toll U z ≤ a; change 0<a at ha; linarith only [hh,ha]
end YM.CF.Esti
