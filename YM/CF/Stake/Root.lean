import YM.CF.Stake.Hull
import YM.CF.Stake.Reed
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
lemma clip_b {X:Support (Domain N B)}(f:Sweep (mid N B))(u:(halo 1 X).image (chart f)⊆Ω) (h:Duo SU.group S A A' Ω)(p:Kind S (A.park,A.k) (A'.park,A'.k) Ω): Duo SU.group S (rot f A) (rot f A') X ∧ Kind S ((rot f A).park,(rot f A).k) ((rot f A').park,(rot f A').k) X:=by
 let H:=clue S f.s (Facet.pasta f) A; let H':= clue S f.s (Facet.pasta f) A'; have ht:= clip_u A A' f.s (pasta f) h u p; have hp:=clip_t _ _ _ _ h u p; unfold rot dice; split
 next pf=>
    refine ⟨⟨⟨ht.road,ht.fr,ht.fe,ht.trunks,fun i v t=> ?_,fun i v=> ?_,fun i v=> ?_⟩,ht.cost,ht.aisles,ht.flags⟩,hp⟩
    · exact congrArg Reef.qG (ht.view i v t) -- tune echo morphism
    · exact congrArg Reef.qG (ht.data i v)
    exact congrArg Reef.frolic (ht.color _ v)
 exact ⟨ht,hp⟩
lemma loft_b {X:Support (Domain N B)}(w:Duo SU.group S A A' X): Duo SU.group S (rough A 0) (rough A' 0) X:= ⟨⟨w.road,w.fr,w.fe,w.trunks,w.view,w.data,fun _ _=>rfl⟩,w.cost,w.aisles,w.flags⟩
variable (s:Sweep (mid N B))
include W h P'
lemma boot_b (g:Beat.shadows (o:=i) Ω (k+1)): mare Z A i=mare Z A' i:=by
 unfold Tye.mare Tye.patrol; apply congrArg; refine sum_congr rfl fun s _=>?_ ; let j:Site (Domain N B):= (chart s).symm i; let C:=halo k {j}
 have hv: (halo 1 C).image (chart s) ⊆ Ω:=by
    have hh: ((halo (k+1) {j}).image (affine s.s (pasta s)))= halo (k+1) {i}:=by rw [←dignify, image_singleton]; rw [show affine s.s (pasta s) j=i from (chart s).apply_symm_apply i]
    refine (image_subset_image (Eire.icing ?_)).trans ((hh.symm ▸ (show halo (k+1) {i} ⊆ Ω from g))); omega
 obtain ⟨a,b⟩:= clip_b s hv h P'; let p:= loft_b a; let U:= rough (rot s A) 0; let V:= rough (rot s A') 0; let w':= W.hunter
 have ht: Kind S (U.park,U.k) (V.park,V.k) C:= b
 let r:=R1
 have ho: marble Z U j= marble Z V j:=by
    unfold marble Tye.booth Iva.fotoP Iva.motoP footS; rw [Cloak.issueC,Cloak.issueC]; -- Witter
    have p₁:= oaths U p ht j k (Subset.refl C) w'.witR w'.witX w'.pureT w'.oath w'.toe (w'.hero Z.mup (mem_insert_self ..)); have p₂:= oaths U p ht j k (Subset.refl C) w'.quote w'.note w'.pureT w'.oath w'.toe (w'.hero Z.etap (by simp)); have p₃:= oaths U p ht j k (Subset.refl C) w'.scene w'.wise w'.pureT w'.oath w'.toe (w'.hero Z.xip (by simp)); exact congrArg₂ (·-·) (congrArg (fun t:ℂ=> ((-Z.beta*t.re:ℝ):ℂ)) p₁) (congrArg₂ (·+·) p₂ p₃)
 exact congrArg _ ho
omit h P'
include W v
lemma fisk_l (u:Beat.shadows (o:=i) Ω (k+2)): mig Z A V₂ V₁ i=mig Z A' T₂ T₁ i:=by
 have ht:= W.hunter; have hx:=v.duo; let U:=v.kindB; let r:= W.ash; let t:=W.ages
 have h:Beat.shadows (o:=i) Ω k:= (Corona.halo_mono (by omega : k≤ k+2) (Subset.refl _)).trans u
 unfold mig Tye.mix prum; rw [wish_k Z A K0 k' k hx r t i ht h, bluntB Z A hx r t i k h ht.tag ht.toe,artB Z A hx r t i k h ht.tag,boot_b Z W hx U _ ((Corona.halo_mono (by omega) (Subset.refl _)).trans u)]
 have he: Beat.shadows (o:=i) Ω _:= (Corona.halo_mono ht.line (Subset.refl _)).trans h; simp only [gateL A hx i k h (i:=i) (d:=Z.loft*radiusB x) (by rw [separation_self,zero_add]; exact ht.toe), echoF Z V₁ T₁ W.trih W.pole i _ v.port he, echoF Z V₂ T₂ W.trih W.pole i _ v.noth he]
 have hv:flockK Z A i=flockK Z A' i:=by
    unfold flockK; refine sum_congr rfl fun a g=>?_ ; unfold ansC; split; next q=> refine congrArg _ (opus_p T x _ _ _ _ _ a (aroundBk Ω u ((Nat.add_le_add (Tarn.innZ _ a q) ht.mask).trans (by omega))) r t W.beta hx.toBeat) -- tune
    simp only [zero_mul]
 rw [hv]
end YM.CF.Stake
