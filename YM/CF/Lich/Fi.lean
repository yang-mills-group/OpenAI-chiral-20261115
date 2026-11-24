import YM.CF.Lich.Line
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne Font
local notation "τ"=> mid N B
local notation "m"=> More τ
abbrev Mz:= Single (mid N B) -- N B implicits
local notation "Q₁"=> A.Fame
local notation "V₁"=> led G x Q₁ V
abbrev Hop(A:Op (Single τ))(E:Support m):Prop:= ∀ i k,A i k≠0→ place_x i∈E ∧ place_x k∈E
def maskS(o:Site m): Op (Single τ):= Matrix.of fun i k=> if place_x i=o then V₁ i k else 0
lemma chronological : ∑ i, maskS A V i= V₁ :=by
 ext i k; rw [Matrix.sum_apply,sum_eq_single (place_x i)]; exact if_pos rfl
 · intro b _ h; exact if_neg (Ne.symm h)
 simp
lemma flourish_b(Z:Op (Single τ))(X:Support m)(p:Hop Z X): Flour (camp X) (boat Z).val :=by
 change Flour _ (faceD true false Z); apply Flour.sum; intro i _; apply Flour.sum; intro z _; by_cases h:Z i z=0
 · rw [h,zero_smul]; exact Flour.trivial
 apply Flour.smul; exact Flour.putPut _ (mem_filter.mpr ⟨mem_univ _,(p i z h).1⟩) (mem_filter.mpr ⟨mem_univ _,(p i z h).2⟩)
variable (hx:S.ratio=ratio G)
abbrev Panel(A:Muster G S x e T)(D:Support (Domain N B))(k:ℕ)(V W:Rent0 G e): Prop:=∀ P:mSeal P B,Lattice.halo k (hatY S P) ⊆ D→ (dressL G e).rel P V W
include hx
lemma sights {P':mSeal P B}{o:Site m}(v:Grove (terr _) P')(u:o∈Facet.mount (ratio G) P')(hf:P'.card ≤ Stores.till x): hatY S P' ⊆ halo (radiusB x+1) {o}:=by intro i t; obtain ⟨z,h,rfl⟩:=mem_image.mp t; exact halo_spec.mpr ⟨_,mem_singleton_self _, (hx.symm ▸ (thigh (ratio G) v u _ h)).trans (Nat.add_le_add_right (hf.trans (Nat.div_le_self _ _)) _)⟩ -- tune ambiguous
lemma sermon {P':mSeal P B}{i:Site m}(p:i∈ cloudG G P'): i∈hatY S P':=by unfold hatY; rw [hx]; exact mem_image.mpr ⟨_,(mem_filter.mp p).2, Ratio.embed_parent ..⟩
variable {a b c D':ℝ}{k:ℕ}{Z' :nomA N P B→ Op (Single (mid N B))}(H: Ind G A.Fame a b c n Z')
include H
section
variable (o:Site (More (mid N B)))(X:Support (More (mid N B)))
lemma joy_p : Hop (maskS A V o) (halo (radiusB x+1) {o}) := by
 obtain ⟨W,h,u⟩:= H.port; intro i k p; dsimp only [maskS, Matrix.of_apply] at p; split at p
 next t=> refine ⟨halo_subset _ _ (mem_singleton.mpr t),?_⟩; unfold led at p; rw [Matrix.sum_apply] at p; obtain ⟨z,t',P⟩:= exists_ne_zero_of_sum_ne_zero p; have hp:W z i k≠0:= fun v=>P (norm_le_zero_iff.mp ((h z).gate i k _|>.trans_eq v)); obtain ⟨hp,hz,hw⟩:= (h z).root i k hp; have ho:o ∈Facet.mount (ratio G) z:= t ▸ mem_image.mpr ⟨_,(mem_filter.mp hz).2,Ratio.embed_parent ..⟩; exact sights hx hp ho (mem_filter.mp t'|>.2) (sermon hx hw)
 next =>exact False.elim (p rfl)
lemma peg(p:Panel A X k V W)(h:Beat.shadows (o:=o) X (radiusB x+1+k)):maskS A V o=maskS A W o:=by
 ext i z; unfold maskS; dsimp only [Matrix.of_apply]; split
 next v=> unfold led; rw [Matrix.sum_apply,Matrix.sum_apply]; obtain ⟨R,t,u⟩:= H.port; exact sum_congr rfl (fun i' j' => by
    by_cases hv:R i' i z=0; · simpa only [norm_le_zero_iff] using (norm_le_zero_iff.mp ((t i').gate i z V|>.trans_eq hv)).trans (norm_le_zero_iff.mp ((t i').gate i z W|>.trans_eq hv)).symm
    obtain ⟨hx',ht,_⟩:= (t i').root i z hv
    have he:o∈Facet.mount (ratio G) i':= v ▸ mem_image.mpr ⟨_,(mem_filter.mp ht).2, Ratio.embed_parent ..⟩; refine congrArg (fun X:Op (Single τ)=>X i z) ((t i').reads _ _ (p i' ?_)); exact (Corona.halo_mono le_rfl (sights hx hx' he (mem_filter.mp j'|>.2))).trans ((icing (by omega)).trans h))
 rfl
-- long both Phase and F root leaves group supports regardless connected
end
omit H hx
abbrev bigS:= (portA (X:=P) (B:=B) (Stores.till x))ᶜ -- tune binder
abbrev Ax:= Palot.leaf (Site m)
local notation "M'"=> (portA (X:=P) (B:=B) (Stores.till x))ᶜ
-- use support directly; Lens analyzer over nonempty
lemma echoM(P':mSeal P B)(p:Ind G Q₁ a b c n Z')(Z:Support (Domain N B))(hx:S.ratio=ratio G)(v:hatY S P' ⊆ Z): Hop (A.Fame P' V) Z:=by
 obtain ⟨R,t,H⟩:=p.port; intro i z w; obtain ⟨hp,ht,he⟩:= (t P').root i z (fun h=> w (norm_le_zero_iff.mp ((t P').gate _ _ _ |>.trans_eq h))); exact ⟨v (sermon hx ht),v (sermon hx he)⟩
lemma echoF{Z:nomA N P B→ℂ} (h:S.ratio=ratio G)(p:Tally Q' Z a b c D' n)(i:Site m)(X:Support m)(hp:Panel A X k V W)(ht:Beat.shadows (o:=i) X (radiusB x+1+k)): fJ G Q' x V i=fJ G Q' x W i:=by
 unfold fJ; obtain ⟨R,t,H⟩:= p.members; apply sum_congr rfl; intro u hu; by_cases v:i∈Facet.mount (ratio G) u; swap; simp only [turtle, if_neg v,zero_smul]
 apply congrArg (turtle (ratio G) u i • ·); by_cases z:R u=0
 · rw [show Q' u=0 from funext fun i=> norm_le_zero_iff.mp ((t u).sumline _|>.trans_eq z)]; rfl
 exact (t u).reads _ _ (hp _ ((Corona.halo_mono le_rfl (sights h ((t u).travel z) v ((mem_filter.mp hu).2))).trans ((icing (by omega)).trans ht)))
end Muster
end YM.CF.Lich
