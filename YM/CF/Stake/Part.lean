import YM.CF.Stake.Root
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
variable {d e:ℝ} {j k k' m n l:ℕ} {x y β:ℝ}
open Lich.Muster
open Jet Vol Corne
-- Core reads and sites lifts.
open Font
variable{Ω:Support (Domain N B)} {A A': Monk SU.group S}
variable {xU yU xV yV: Rent0 G d} {F0: nomA N P B→ Op (Single (mid N B))}{D0:nomA N P B→ℂ}{μ Y0 Yb σ z0 z1 z2:ℝ}
variable{R1 R2 K0:ℕ}
variable(Z:Muster G S x d T)(W:Gard (n:=n) (a:=μ) (a':=σ) (C:=Y0) (D:=Yb) (c:=z0) (v:=z1) (Z:=z2) (J:=F0) (Φ:=D0) (R₁:=K0) Z R1 R2 k k')
variable {V₁ V₂ T₁ T₂:Rent0 G d}
variable (h: Duo SU.group S A A' Ω)(P':Kind S (A.park,A.k) (A'.park,A'.k) Ω)(v:Muster.Post Z A A' V₁ V₂ T₁ T₂ k' Ω)(i:Site (Domain N B))
local notation "τ"=>mid N B
local notation "δ"=>Domain N B
-- output READ P footprint `halo1` for leaf (later add15). seeds note r2+k+2≤. At C' outer Ω includes. currency measured after halo pad.
variable (t w L0:ℝ)
def asp (J:Words S):Palot.leaf (Site (Domain N B)) := let C:= (Z.mapV (k+2) J); ⟨halo 1 C.val,C.property.mono (halo_subset ..)⟩
def vast (J:Words S) : Palot.leaf (Site (Domain N B)):= let X:= asp (k:=k) Z J; ⟨halo 20 X.val,X.property.mono (halo_subset ..)⟩
include v W
lemma mass_p (j: Palot.leaf (Site (Domain N B)))(u:halo 1 j.val ⊆Ω): mace Z A j=mace Z A' j:=by
 unfold Tye.mace Tye.patrol; apply congrArg; refine sum_congr rfl fun s _=>?_ ; let X:Palot.leaf (Site δ):= (chute s).symm j
 have ht:X.val.image (affine s.s (pasta s))=j.val:=congrArg Subtype.val ((chute s).apply_symm_apply j)
 have hp:(halo 1 X.val).image (chart s) ⊆ Ω:=by change (halo 1 X.val).image (affine s.s (pasta s))⊆ _; rw [← dignify,ht]; exact u
 obtain ⟨p,h⟩:= clip_b s hp v.duo v.kindB
 exact congrArg (payZ s) (congrArg Complex.ofReal (purse Z _ X (loft_b p|>.toBeat) (Subset.refl _) W.ages W.ash))
lemma pedal_l(j: Palot.leaf (Site (Domain N B)))(u:halo 1 j.val ⊆Ω): pedal Z A V₁ k' j=pedal Z A' T₁ k' j∧ legA Z V₁ k' j=legA Z T₁ k' j:=by
 have hh := (halo_subset ..).trans u; obtain ⟨t,w⟩:= vital_r Z _ _ _ W v _ hh; refine ⟨?_,w⟩; rw [legS,legS,purse Z _ j v.duo.toBeat hh W.ages W.ash] at t; unfold pedal; push_cast at t; rw [mass_p Z W v j u]
 rw [add_assoc,add_assoc] at t; rw [add_assoc,add_assoc, add_left_cancel t]
lemma rootH (s:R2+k+2≤ R1)(j:Hos S R1)(u:stem S j ⊆ Ω): heedP Z A V₂ V₁ R2 R1 t w L0 j=heedP Z A' T₂ T₁ R2 R1 t w L0 j:=by
 unfold heedP rootK senseC; rw [birth_h Z _ v.duo W.ash W.ages t w L0 _ ((farther W.trial).trans u) W.forwards W.tilt]; unfold hont haunt; simp only [sore_l Z _ v.duo W.ash W.ages ((farther W.trial).trans u) W.coze]; let X:=j.val.dome R2; have ht(o)(w:o∈X):Beat.shadows (o:=o) Ω (k+2):=foster w u (by omega)
 rw [sum_congr (s₁:=X) (f:=fun i=>mig Z A V₂ V₁ i) rfl (fun i g=> fisk_l Z W v i (ht i g)),sum_congr (s₁:=X) (f:=fun i=> doubleK _ i) (g:=fun i=>doubleK (Corne.led G x Z.Fame T₁) i) rfl ?_] -- tune proof
 exact fun i q=> royalty_a Z W.ferr W.trih i V₁ T₁ v.port ((Corona.halo_mono (W.hunter.line.trans (by omega)) (Subset.refl _)).trans (ht i q))
lemma rootL(J:Words S)(u:(asp (k:=k) Z J).val ⊆ Ω): wistL Z A V₂ V₁ R2 k' t w J= wistL Z A' T₂ T₁ R2 k' t w J:=by
 let x':= (halo_subset 1 ((Z.mapV (k+2) J).val)).trans (u)
 rcases J with i|i|i
 · unfold wistL sweetK; simp only [Sum.elim_inl,steerC]; rw [payF Z _ _ _ v.duo W.ash W.ages W.forwards _ x']
 · change halo (k+2) {i}⊆ Ω at x'; unfold wistL sweetK DocY DocF; simp only [Sum.elim_inl,Sum.elim_inr,Tye.pendant,fount, gateL A v.duo i _ x' (i:=i) (d:=R2) (by rw [separation_self,zero_add]; exact W.extra.trans (by omega)), fisk_l Z W v _ x',royalty_a Z W.ferr W.trih i _ _ v.port ((Corona.halo_mono (W.hunter.line.trans (by omega)) (Subset.refl _)).trans x')]
 obtain ⟨h,y⟩:= pedal_l Z W v i u; unfold wistL sweetK DocY DocF; simp only [Sum.elim_inr,h,y]
omit v
lemma warmth_R(j:Hos S R1): Hop (haunt Z V₁ R2 R1 j) (stem S j):=by
 intro u x1 w; unfold haunt at w; rw [Matrix.sum_apply] at w; obtain ⟨o,p,t⟩:=exists_ne_zero_of_sum_ne_zero w; let L:= radiusB x+1; have he:halo L ({o}:Support (Domain N B)) ⊆ stem S j:=foster p (show _ ⊆ stem S j from Subset.refl _) (Nat.le_trans (Nat.add_le_add_left ((Nat.le_add_right ..).trans W.hunter.line) _) W.morn)
 have hp:=rum_h Z W.ferr W.trih _ _ _ _ t; exact ⟨he hp.1,he hp.2⟩
lemma rootP (j:Hos S R1): Flour (camp (stem S j)) (heedP Z A V₂ V₁ R2 R1 t w L0 j).val:= primed _ _ (warmth_R Z W j) _ -- tuning
lemma rootQ(j:Words S): Flour (camp (vast (k:=k) Z j).val) (wistL Z A V₂ V₁ R2 k' t w j).val:=by
 have hx:camp (Z.mapV (k+2) j).val⊆ camp (vast (k:=k) Z j).val:=fun i p=> mem_filter.mpr ⟨mem_univ _,halo_subset 20 _ (halo_subset 1 _ ((mem_filter.mp p).2))⟩ -- implicit params
 apply Flour.lift _ hx
 rcases j with i|i|i
 · exact malt _ _ (Flour.grainE.smul _)
 · let T:=halo (k+2) ({i}:Support δ); apply malt T _; apply primed T; intro u v w; change Tye.fount Z A V₁ R2 i u v≠0 at w; unfold fount at w; split at w; next=>exact False.elim (w rfl)
   next=> have h:=rum_h Z W.ferr W.trih _ _ _ _ w; have ht: halo (radiusB x+1) ({i}:Support δ)⊆ T:= Corona.halo_mono ((Nat.le_add_right ..).trans (W.hunter.line.trans (by omega))) (Subset.refl _); exact ⟨ht h.1,ht h.2⟩
 exact malt _ _ (primed i.val _ (farB Z V₁ W i) _)
end YM.CF.Stake
