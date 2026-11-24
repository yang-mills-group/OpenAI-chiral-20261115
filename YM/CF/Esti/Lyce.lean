import YM.CF.Prism.Col
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
abbrev Palm (S:StepData c f)(r:ℕ)(i: Mark S):= halo r (spotting S i)
def vase (S:StepData c f)(X: Finset (Mark S)): Stores S:=⟨X.toLeft.toLeft,X.toLeft.toRight,X.toRight⟩
lemma vase_a(X: Stores S) : plots X=(X.costs.disjSum X.aisles).disjSum X.flags:=by
 ext i; rcases i with (p|p)|p <;> simp [plots,planted]
lemma vase_b(X: Stores S):vase S (plots X)=X:=by simp [vase,vase_a S]
lemma vase_c(X: Finset (Mark S)):plots (vase S X)=X:=by rw [vase_a]; ext i; rcases i with (p|p)|p <;> simp [vase] -- tune
lemma vase_d(X:Stores S): (plots X).card=X.shares:=by rw [vase_a]; simp [Stores.shares]
lemma vase_i:Injective (vase S):=HasLeftInverse.injective ⟨_,vase_c _⟩ -- tune
lemma vase_j:Injective (plots (S:=S)):=HasLeftInverse.injective ⟨_,vase_b _⟩ -- tune
lemma palm_p(r:ℕ)(i:Mark S):(Palm S r i).Nonempty:=by
 suffices p:(spotting S i).Nonempty from p.mono (halo_subset r _)
 rcases i with (p|p)|p; exact ⟨_,mem_image_of_mem S.ratio.parent (YM.Work.E01.base_touched p)⟩; exact ⟨_,mem_insert_self ..⟩; exact singleton_nonempty _
lemma palm_v(r:ℕ)(A:Stores S):A.dome r=(plots A).biUnion (Palm S r):=by
 ext i; rw [Stores.dome]; constructor
 · intro h; obtain ⟨k,t,l⟩:=halo_spec.mp h; obtain ⟨j,p,h⟩:= (planted_owns ..).1 t; exact mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,p⟩,halo_spec.mpr ⟨_,h,l⟩⟩
 intro h; obtain ⟨j,p,h⟩:=mem_biUnion.mp h; obtain ⟨k,hq,h⟩:=halo_spec.mp h; exact halo_spec.mpr ⟨k,(planted_owns ..).mpr ⟨_,(mem_filter.mp p).2,hq⟩,h⟩
abbrev Hos(S:StepData c f)(r:ℕ) := {X :Stores S//Spark (Palm S r) (plots X)}
def blip (A:Stores S)(r:ℕ): Finset (Hos S r) := (Ac.Parts (Palm S r) (plots A)).attach.image fun p=> ⟨vase S p.val, by rw [vase_c]; exact (Ac.lives _ _ p.property).2⟩
lemma blip_p (X:Hos S r)(A:Stores S): X∈ blip S A r ↔ plots X.val ∈ Ac.Parts (Palm S r) (plots A):=by
 rw [blip,mem_image]; constructor
 · rintro ⟨Y,-,rfl⟩; simpa only [vase_c] using Y.property -- tune
 intro h; exact ⟨⟨_,h⟩,mem_attach ..,Subtype.ext (vase_b ..) ⟩
def stem (p:Hos S r):=p.val.dome r
lemma stem_p(p:Hos S r):(stem S p).Nonempty:=by
 obtain ⟨i,h⟩:=p.property.1; obtain ⟨z,t⟩:=palm_p S r i; unfold stem; exact ⟨z,palm_v S r p.val ▸ mem_biUnion.mpr ⟨i,h,t⟩⟩ -- tune
lemma stem_d(A:Stores S): Set.PairwiseDisjoint ((blip S A r): Set (Hos S r)) (stem S):=by
 intro i p j l v
 have hi:=Ac.separate (Palm S r) (plots A); change Disjoint (i.val.dome r) (j.val.dome r); rw [palm_v,palm_v]; exact hi ((blip_p S i A).1 p) ((blip_p S j A).1 l) (fun u=>v (Subtype.ext (vase_j S u)))
abbrev Pear (S:StepData c f)(p: Finset (Hos S r)):= vase S (p.biUnion fun i=>plots i.val)
lemma stem_t(A:Stores S) (r:ℕ):Pear S (blip S A r)=A:=by
 rw [Pear, show Finset.biUnion _ _=plots A from ?_,vase_b]; ext i; rw [← (Ac.reconstruct (Palm S r) (plots A)),mem_biUnion,mem_biUnion]; constructor
 · rintro ⟨j,t,l⟩; exact ⟨_,(blip_p S j A).mp t,l ⟩
 rintro ⟨j,t,l⟩; let k:Hos S r:=⟨vase S j,vase_c S j|>.symm ▸ (Ac.lives _ _ t).2⟩; exact ⟨k,(blip_p S k A).mpr (by rw [show plots k.val=j from vase_c ..]; exact t), (vase_c S j).symm ▸ l⟩ -- tune
lemma stem_u(p: Finset (Hos S r))(h: Set.PairwiseDisjoint (p: Set (Hos S r)) (stem S)): blip S (Pear S p) r=p:=by
 let f(x:Hos S r):=plots x.val; let Y:= p.image f; have hp: plots (Pear S p)=Y.biUnion id:=by
    rw [Pear,vase_c]; ext i; simp [Y,f]
 have he: Parts (Palm S r) (Y.biUnion id)=Y:=by
    apply Ac.separates; intro i t; obtain ⟨x,h,rfl⟩:=mem_image.mp t; exact x.property
    intro i t j l v; obtain ⟨x,u,rfl⟩:=mem_image.mp t; obtain ⟨y,w,rfl⟩:=mem_image.mp l; change Disjoint ((plots x.val).biUnion (Palm S r)) ((plots y.val).biUnion (Palm S r)); rw [←palm_v, ←palm_v]; exact h u w (fun e=>v (congrArg f e))
 ext i; rw [blip_p, hp,he]; constructor; intro h; obtain ⟨z,hz,u⟩:=mem_image.mp h; exact (show z=i from Subtype.ext (vase_j S u)) ▸ hz; intro g; exact mem_image_of_mem f g
lemma pack(p:Hos S r)(h:p∈blip S A r): Packet p.val A r:=by
 refine ⟨(Ac.lives _ _ ((blip_p S p A).mp h)).1,fun i u v=>?_⟩
 have hi : i∈ plots A:=mem_filter.mpr ⟨mem_univ _,u⟩
 have hp : i∈ plots (Pear S (blip S A r)):= (stem_t S A r).symm ▸ hi; rw [Pear,vase_c] at hp
 obtain ⟨x,t,l⟩:= mem_biUnion.mp hp; have ht: x≠p:=fun g=> v ((mem_filter.mp (g ▸ l : i∈plots p.val)).2)
 refine Disjoint.mono_left ?_ (stem_d S A (show x∈ ((blip S A r): Set (Hos S r)) from t) (show p∈ ((blip S A r): Set (Hos S r)) from h) ht); unfold stem; rw [palm_v]; exact fun _ w=> mem_biUnion.mpr ⟨_,l,w⟩
end YM.CF.Esti
