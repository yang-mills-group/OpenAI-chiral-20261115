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
variable {x:Type}[Fintype x][DecidableEq x]
private def cartV(F:Harper x)(T:Equiv.Perm x): Harper x where
 pair:= univ.filter fun i=>rail F (T i.1) (T i.2)
 flip {_ _} p:=mem_filter.mpr ⟨mem_univ _, F.flip (mem_filter.mp p).2⟩
 tran {_ _ _} h p:= mem_filter.mpr ⟨mem_univ _, F.tran (mem_filter.mp h).2 (mem_filter.mp p).2⟩
private lemma cv_s(F:Harper x)(T:Equiv.Perm x)(i j:x):rail (cartV F T) i j↔ rail F (T i) (T j):=by simp [rail, cartV] -- tune
abbrev quill (T:Equiv.Perm x):OrderIso (Harper x) (Harper x) where
 toFun x:=cartV x T
 invFun x:=cartV x T.symm
 left_inv x:=harp_ext (by ext ⟨i,j⟩; change rail (cartV ..) i j↔ _; rw [cv_s,cv_s,Equiv.apply_symm_apply,Equiv.apply_symm_apply])
 right_inv x:=harp_ext (by ext ⟨i,j⟩; change rail (cartV ..) i j↔ _; rw [cv_s,cv_s,Equiv.symm_apply_apply,Equiv.symm_apply_apply])
 map_rel_iff':=by
    intro i j; change cartV i T≤cartV j T↔ _
    constructor
    · rintro h ⟨x,y⟩ u; obtain ⟨x,rfl⟩:=T.surjective x; obtain ⟨y,rfl⟩:= T.surjective y; exact (cv_s j T x y).mp (@h _ ((cv_s i T x y).mpr u))
    rintro p ⟨x,y⟩ u; exact (cv_s ..).mpr (@p _ ((cv_s i T x y).mp u))
lemma runV(T:Equiv.Perm x)(A:Finset x): quill T (beamH A)=beamH (A.map T.symm.toEmbedding):=by apply harp_ext; ext ⟨i,j⟩; change rail (cartV _ _) _ _↔ _; rw [cv_s]; change _∈ _ ×ˢ _ ↔ _∈ _ ×ˢ _; simp -- tune
lemma bayV(T:Equiv.Perm x)(A:Harper x): bay (quill T A)=(bay A).map T.symm.toEmbedding:=by ext i; rw [bayH]; change rail (cartV _ _) _ _ ↔ _; rw [cv_s,← bayH]; simp
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(O: Sweep (mid P B))(k:ℕ)(X:Support (Domain P B)) (A:Eire.Ride S)
lemma sew_b (F:Sweep (mid N B)): (assembly _).embed F.b=Facet.pasta F:=by
 let R:= mid N B; have he: F.b = wrap R (castX F).t:= (wrap_lift _).symm
 exact ((show (assembly _).embed F.b=(assembly _).embed (wrap R (castX F).t) from congrArg _ he).trans (Ratio.embed_wrap ..)) -- tune
lemma sit_k : chart f=boxA f:= by ext i; rw [sitA,sew_b]; rfl
local notation "R'"=> reSweep G f
include p
lemma stroll : chart (reSweep G f)= StepData.sendSites f.s (S.ratio.embed (Facet.pasta f)):=by
 unfold chart; have he: Facet.pasta R'= S.ratio.embed (Facet.pasta f):=by rw [p,←sew_b, ←sew_b]; exact (reA G f).symm
 rw [he]; rfl -- tune indentation
abbrev actY {n:Side}(F:Sweep n)(X:Support (More n)): Support (More n):= X.map (boxA F).symm.toEmbedding
lemma broadK : actY (reSweep G f) X=toRoar G f⁻¹ X:=by
 apply (weaveS G f).injective; rw [show weaveS G f (toRoar G f⁻¹ X)= X from (weaveS G f).apply_symm_apply X]; unfold actY; change (_:Support _).image _=X; let Y:= boxA (reSweep G f); have hx:(Shape.broad G (castX f)).anon _=Y:=by
    funext i; change affine f.s (wrap (Domain P B) (2 • (Shape.broad G (castX f)).t)) i= (boxA (reSweep G f)) i; rw [←sit_k, stroll G S p]; unfold Shape.broad; rw [smul_comm]; change affine f.s _ _= affine f.s _ _; rw [p]; exact congrArg (fun b=> affine f.s b i) (Ratio.embed_wrap (ratio G) _).symm
 rw [hx]; unfold Y; ext i; obtain ⟨i,rfl⟩:=(boxA R').surjective i; simp
lemma pace_k : S.ratio.parent ∘ (boxA (reSweep G f)) = boxA f ∘ S.ratio.parent:=by funext i; rw [←sit_k, stroll G S p]; exact AnalyticBridge.GaussianFieldAlignment.Locations.parent_map ..
lemma peg_k : Eire.hatY S (actY R' X)=actY f (Eire.hatY S X):=by
 have hx:= pace_k G S p f; unfold actY Eire.hatY; simp_rw [Finset.map_eq_image,image_image]; refine congrArg (fun q=> X.image q) (funext fun i=>?_); apply (boxA f).injective; change boxA f (S.ratio.parent _)=(boxA f) ((boxA f).symm _); rw [Equiv.apply_symm_apply]; have he:= congrFun hx ((boxA R').symm i); simp only [Function.comp_apply, Equiv.apply_symm_apply] at he; exact he.symm
omit p
lemma walkA {N:Side} (H:Sweep N)(P:Support (More N))(k:ℕ): halo k (actY H P) = actY H (halo k P):=by unfold actY; rw [←sitU,paysT]
include p
open Eire
lemma lootT : Eire.gleans S k (quill (chart f) A)=(Eire.gleans S k A).image (toRoar G f⁻¹):=by
 ext i; let F:=weaveS G f⁻¹; obtain ⟨i,rfl⟩:=F.surjective i; change F i∈ gleans S _ _ ↔ F i∈(gleans S k A).image F; simp only [F.injective.eq_iff,mem_image, exists_eq_right]; change toRoar G f⁻¹ i∈ _↔_; rw [←broadK _ _ p,gleans,gleans]; simp only [mem_filter,mem_univ,true_and]; rw [peg_k G S p,walkA,sit_k,actY,←runV]; exact (quill (boxA f)).le_iff_le
end YM.CF.Salt
