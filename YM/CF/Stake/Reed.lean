import YM.CF.Stake.Pole
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
open Corne Font Lich.Muster
variable {Xf:nomA N P B→Op (Single (mid N B))}{x p1 p2 p3:ℝ}(H:Muster G S x d T)
local notation "τ"=> mid N B
variable (h: Ind G H.Fame p1 p2 p3 k Xf)(u:S.ratio=ratio G)(i:Site (Domain N B))(a a':Rent0 G d){Ω:Support (Domain N B)}
include h u
set_option maxHeartbeats 700000 in
lemma royalty_p: Hop (led G x H.Fame a*Tye.stock i) (halo (radiusB x+1) {i}):=by
 obtain ⟨W,y,R⟩:=h.port; rw [capZ]; intro j k0 p; dsimp only [Matrix.of_apply] at p; split at p
 next z=>
    refine ⟨?_,halo_subset _ _ (mem_singleton.mpr z)⟩; unfold Corne.led at p; rw [Matrix.sum_apply] at p; obtain ⟨a1,p0,g0⟩:= exists_ne_zero_of_sum_ne_zero p; have ht:W a1 j k0 ≠0:=fun ht=> g0 (norm_le_zero_iff.mp ((y a1).gate j k0 a|>.trans_eq ht)); obtain ⟨x0,v,w⟩:= (y a1).root _ _ ht; have he:i∈ Facet.mount (ratio G) a1:=z ▸ mem_image.mpr ⟨_,(mem_filter.mp w).2,Ratio.embed_parent ..⟩; exact sights u x0 he (mem_filter.mp p0|>.2) (sermon u v)
 contradiction
lemma royalty_a(p:Panel H Ω l a a')(g:Beat.shadows (o:=i) Ω (radiusB x+1+l)) : doubleK (led G x H.Fame a) i=doubleK (led G x H.Fame a') i:=by
 unfold doubleK; rw [cupZ,cupZ]; apply congrArg halfY; apply congrArg₂ (·+·) (peg H a a' u h i Ω p g) -- check base
 rw [capZ,capZ]; obtain ⟨W,y,R⟩:= h.port; ext j k2; change (if place_x k2=i then _ else 0)=(if place_x k2=i then _ else _); split; swap; · rfl
 next z=> unfold led; rw [Matrix.sum_apply,Matrix.sum_apply]; refine sum_congr rfl fun t w=>?_ ; by_cases q:W t j k2=0; · exact (norm_le_zero_iff.mp ((y t).gate j k2 a|>.trans_eq q)).trans (norm_le_zero_iff.mp ((y t).gate j k2 a'|>.trans_eq q)).symm
          obtain ⟨x0,v0,e⟩:=(y t).root j k2 q; have hi:i∈ Facet.mount (ratio G) t:= z ▸ mem_image.mpr ⟨_,(mem_filter.mp e).2, Ratio.embed_parent ..⟩; exact congrArg (fun Q:Op (Single τ)=> Q j k2) ((y t).reads _ _ (p t ((Corona.halo_mono le_rfl (sights u x0 hi (mem_filter.mp w|>.2))).trans ((Eire.icing (by omega)).trans g))))
lemma rum_h : Hop (doubleK (led G x H.Fame a) i) (halo (radiusB x+1) {i}) :=by
 unfold doubleK halfY; rw [cupZ]; intro u' v w; change (1/2:ℂ)* ((_ :Op _) +_) _ _≠0 at w; rw [Matrix.add_apply] at w; by_cases hy:maskS H a i u' v ≠0
 · exact joy_p H a u h i u' v hy
 apply royalty_p H h u i a u' v; have he:= not_ne_iff.mp hy; change (1/2:ℂ)*(maskS H a i u' v+(Corne.led G x H.Fame a*Tye.stock i) u' v)≠0 at w; rw [he,zero_add] at w; exact right_ne_zero_of_mul w
end YM.CF.Stake

#print axioms YM.CF.Stake.royalty_p
#print axioms YM.CF.Stake.royalty_a
#print axioms YM.CF.Stake.rum_h
