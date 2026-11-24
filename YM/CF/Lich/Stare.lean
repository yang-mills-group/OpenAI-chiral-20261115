import YM.CF.Lich.Bern
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
open Corne
-- birth Lens budgets.Earth. includes source.Tip.Ph location.E symmetry after.
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
local notation "Ta"=> mid N B
open Font Rel
variable{k b d r' R₁:ℕ}{a a' C D c v Z:ℝ}{J:nomA N P B→Op (Single (mid N B))}{Φ:nomA N P B→ℂ}
structure Gard(r r' b k:ℕ):Prop where
 trih : S.ratio=ratio G
 ash : Ready T x
 ages: 1000 ≤ radiusB x
 tilt : spanO T x
 forwards : shovel S.patch+10≤radiusB x
 coze : A.phaseLow.threshold=temp x
 pays : A.phaseUp.threshold=fiery SU.group x S.patch.L
 beta : 0<β
 morn : r'+b≤ r
 trial: (j+l+200)*radiusB x ≤ r
 extra : r'≤ b
 rib : (l+90)*radiusB x≤ k
 ferr : Ind G A.Fame a C D n J
 pole : Tally A.LawQ Φ a' c v Z n
 hunter : Census A R₁ k b
local notation "CK"=> Gard (a:=a) (a':=a') (C:=C) (D:=D) (c:=c) (v:=v) (Z:=Z) (n:=n) (R₁:=R₁) (J:=J) (Φ:=Φ) A r r' b k -- binder order?
-- apply physical Vic
variable{W':Monk SU.group S}{Y' D':Rent0 G e}{X:Support (Domain N B)}(h:Gard (a:=a) (a':=a') (C:=C) (D:=D) (c:=c) (v:=v) (Z:=Z) (n:=n) (R₁:=R₁) (J:=J) (Φ:=Φ) A r r' b k)
structure Post (A:Muster G S x e T)(U U':Monk SU.group S)(V W Vw Ww:Rent0 G e)(k:ℕ)(X:Support (Domain N B)) :Prop where
 duo: Forge.Duo SU.group S U U' X
 kindB: Kind S (U.park,U.k) (U'.park,U'.k) X
 port : Panel A X k V Vw
 noth: Panel A X k W Ww
variable(p:Post A U W' V W Y' D' k X)
include h p
lemma vital_l (i:Site m)(hp: Beat.shadows (o:=i) X b) :docS A U V W r' i= docS A W' Y' D' r' i∧docA A U V r' i=docA A W' Y' r' i:=by
 unfold docS docA; simp only [gateL U p.duo i b hp (d:=r') (i:=i) (by rw [separation_self]; exact (zero_add _).le.trans h.extra)]; split; next => exact ⟨rfl,rfl⟩
 exact ⟨fisc A U V W R₁ k b Y' p.duo h.ash h.ages i p.kindB h.hunter hp D' h.trih h.beta h.pole p.port p.noth, peg A V Y' h.trih h.ferr i X p.port ((Corona.halo_mono h.hunter.line (Subset.refl _)).trans hp)⟩
lemma vital_r (i:Palot.leaf (Site m))(hp:i.val ⊆ X):legS A U V k i=legS A W' Y' k i ∧ legA A V k i=legA A Y' k i:=by
 unfold legS legA; rw [purse A U i p.duo.toBeat hp h.ages h.ash, hulk A U k p.duo h.ash h.ages h.rib i hp h.coze h.pays h.tilt]; obtain ⟨R,u,hY⟩:= h.ferr.port; obtain ⟨S,t,v⟩:=h.pole.members
 constructor; refine congrArg (_+·) (sum_congr rfl fun i' t'=>?_ ); · rw [(t i').reads _ _ (p.port i' ((mem_filter.mp t').2.symm ▸ hp))] -- ▸ wrong dir rewrite
 exact sum_congr rfl fun i' t=> (u i').reads _ _ (p.port i' ((mem_filter.mp t).2.symm ▸ hp))
lemma vital_g (i:Hos S r)(hp:stem S i⊆ X) : onyx r A U V W r' i=onyx r A W' Y' D' r' i ∧ hush r A V r' i=hush r A Y' r' i:=by
 have he(z)(v:z∈ i.val.dome r'):Beat.shadows (o:=z) X b:=foster v hp h.morn
 unfold onyx; rw [sore_l A U p.duo h.ash h.ages (Subset.trans (farther h.trial) hp) h.coze]
 exact ⟨congrArg (_+·) (sum_congr rfl fun i v=> fisc A U V W R₁ k b Y' p.duo h.ash h.ages i p.kindB h.hunter (he i v) D' h.trih h.beta h.pole p.port p.noth), sum_congr rfl fun i v=>peg A V Y' h.trih h.ferr i X p.port ((Corona.halo_mono h.hunter.line (Subset.refl _)).trans (he i v))⟩
omit p
lemma existH(i:Site m): Hop (docA A U V r' i) (halo b {i}):=by
 unfold docA; split; exact fun u v w=>False.elim (w rfl); intro u v w; have he:=joy_p A V h.trih h.ferr i u v w; have hp:halo (radiusB x+1) {i} ⊆ halo b {i}:= Corona.halo_mono ((Nat.le_add_right ..).trans h.hunter.line) (Subset.refl _); exact ⟨hp he.1,hp he.2⟩
lemma farB(i:Palot.leaf (Site m)): Hop (legA A V k i) i.val:=by
 intro u v w; unfold legA at w; rw [Matrix.sum_apply] at w; obtain ⟨z,p,t⟩:=Finset.exists_ne_zero_of_sum_ne_zero w; apply echoM A V z h.ferr i.val h.trih _ u v t; rw [←(mem_filter.mp p).2]; apply halo_subset
lemma warmth_c(i:Hos S r): Hop (hush r A V r' i) (stem S i):=by
 intro u v w; unfold hush at w; rw [Matrix.sum_apply] at w; obtain ⟨o,p,t⟩:=exists_ne_zero_of_sum_ne_zero w; let L:= radiusB x+1; have he:halo L ({o}:Support (Domain N B)) ⊆ stem S i:=foster p (show _ ⊆ stem S i from Subset.refl _) (Nat.le_trans (Nat.add_le_add_left ((Nat.le_add_right ..).trans h.hunter.line) _) h.morn)
 have hp:=joy_p A V h.trih h.ferr _ u v t; exact ⟨he hp.1,he hp.2⟩
end Muster
end YM.CF.Lich
