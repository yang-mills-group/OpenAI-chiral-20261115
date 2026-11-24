import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(X:Stores S)(r k:ℕ)
abbrev loftX:Equiv.Perm (Mark S):= (Equiv.sumCongr (Equiv.sumCongr (shiftFaces f.s (S.ratio.embed (Facet.pasta f))) (StepData.sendBonds f.s (Facet.pasta f))) (chart f)).symm
lemma story(i: Mark S): loftX S f i∈ plots (airport f X)↔ i∈ plots X:=by
 rcases i with (v|v)|v
 · rw [vase_a,vase_a]; change Sum.inl (Sum.inl ((shiftFaces f.s (S.ratio.embed (Facet.pasta f))).symm v))∈ _↔_; unfold airport book; simp -- tune
 · rw [vase_a,vase_a]; change Sum.inl (Sum.inr ((StepData.sendBonds f.s (Facet.pasta f)).symm v))∈ _↔ _; unfold airport book; simp
 rw [vase_a,vase_a]; change Sum.inr ((StepData.sendSites f.s (Facet.pasta f)).symm v)∈ _↔_; unfold airport book; simp
lemma church : plots (airport f X)=(plots X).image (loftX S f):=by ext i; obtain ⟨i,rfl⟩:=(loftX S f).surjective i; rw [story,mem_image]; simp only [(loftX S f).injective.eq_iff, exists_eq_right]
lemma stout(i:Mark S): spotting S (loftX S f i)=actY f (spotting S i):=by
 let a:=Facet.pasta f; let z:=chart f; have h(Q Q':Support (Domain N B))(p:Q'.image (affine f.s a)=Q): Q'=actY f Q:=by
    subst Q; unfold actY; rw [←sit_k]; change Q'= (Q'.image z).map z.symm.toEmbedding; rw [Finset.map_eq_image,image_image,show ⇑z.symm.toEmbedding ∘ ⇑z=id from funext fun i=> z.symm_apply_apply i,image_id]
 rcases i with (i|i)|i; · apply h; let H:= start_map (S:=S) f.s a ((shiftFaces f.s (S.ratio.embed a)).symm i); rw [Equiv.apply_symm_apply] at H; exact H.symm -- unknown _
 · apply h; let b:= StepData.sendBonds f.s a; have hp:= pin_map f.s a (b.symm i); rw [←show b (b.symm i) =sendEdge _ _ _ from rfl,Equiv.apply_symm_apply] at hp; exact hp.symm
 unfold actY; rw [←sit_k]; exact (Finset.map_singleton (chart f).symm.toEmbedding i).symm
lemma trough(i:Mark S): Palm S r (loftX S f i)=actY f (Palm S r i):=by unfold Palm; rw [stout,walkA]
lemma lay_o (A B:Support (Domain N B)): Disjoint (actY f A) (actY f B) ↔ Disjoint A B:=by rw [actY,actY]; exact Finset.disjoint_map _
lemma carryP (i:Hos S r): Spark (Palm S r) (plots (airport f i.val)):=by
 rw [church]; refine ⟨i.property.1.image _,?_⟩; intro x v y p; obtain ⟨x,u,rfl⟩:=mem_image.mp v; obtain ⟨y,w,rfl⟩:=mem_image.mp p; apply Relation.ReflTransGen.lift _ _ _ _ (i.property.2 _ u _ w); rintro p j ⟨v,g,z,t,h⟩; refine ⟨mem_image_of_mem _ v,mem_image_of_mem _ g,(boxA f).symm z,?_,?_⟩ <;> rw [trough]; exact mem_map_of_mem _ t; exact mem_map_of_mem _ h
abbrev laden (r:ℕ):Equiv.Perm (Hos S r) :=
 let Y(i:Hos S r):Hos S r:= ⟨airport f i.val,carryP S f r i⟩
 let p: Injective Y:=fun i j h=> by
    apply Subtype.ext; apply vase_j S; ext x; rw [←story S f i.val,←story S f j.val,show airport f i.val=airport f j.val from congrArg Subtype.val h] --  rw [←church,←church]; exact congrArg (fun x:Hos S r=>plots x.val) h
 letI : Finite (Hos S r):=Finite.of_injective (fun i:Hos S r=> plots i.val) (fun i j h=>Subtype.ext (vase_j S h)); Equiv.ofBijective Y ⟨p, Finite.surjective_of_injective p⟩ -- tune
lemma stack_r(k:Hos S r): Esti.stem S (laden S f r k)=actY f (Esti.stem S k):=by ext i; rw [actY, ←sit_k,mem_map_equiv]; exact dome_map ..
include p
open Atala
local notation "W"=> reSweep G f
lemma can_a : S.ratio.embed ∘ boxA f= (boxA (reSweep G f)) ∘ S.ratio.embed:=by rw [←sit_k,←sit_k,stroll _ _ p]; exact funext (fun x=> affine_root ..)
lemma twirl (i: Hos S r): danceL S (laden S f r i).val r=actY (reSweep G f) (danceL S i.val r):=by
 let D:=actY f i.val.place; let q:=boxA f; have hp:(airport f i.val).place=D:=by ext i; unfold D actY; rw [Finset.mem_map_equiv,←sit_k]; exact place_map ..
 let T:= twinkle S; have z(y): T (q.symm y) r = actY W (T y r):=by
    have ht:= congrFun (can_a G S p f) ((boxA f).symm y); simp only [Function.comp_apply, Equiv.apply_symm_apply] at ht; unfold T twinkle; rw [←walkA]; congr 1; unfold actY; rw [map_singleton]; exact congrArg _ ( (boxA W).injective (by rw [←ht]; simp))
 unfold danceL; change (airport f i.val).place.biUnion _= _; rw [hp]; ext x; constructor
 · intro u; obtain ⟨y,p,v⟩:=mem_biUnion.mp u; obtain ⟨j,u,rfl⟩:=mem_map.mp p; change x∈T (q.symm j) r at v; rw [z] at v; change x∈actY W _; unfold actY; exact Finset.map_subset_map.mpr (show twinkle S j r⊆_ from fun i p=> Finset.mem_biUnion.mpr ⟨_,u,p⟩) v
 intro v; obtain ⟨j,u,rfl⟩:=mem_map.mp v; obtain ⟨y,v,t⟩:=mem_biUnion.mp u; refine mem_biUnion.mpr ⟨q.symm y, mem_map_of_mem _ v,?_⟩; change _∈ T _ _; rw [z]; exact mem_map_of_mem _ t -- tune
end YM.CF.Salt
