import YM.CF.Stake.Part
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
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations Girt Eire
variable (f:Sweep (mid N B)){a e0:ℝ}(i:Site (Domain N B))
lemma parent_s (F_:Rent0 G d)(p:S.ratio=ratio G): let X:= male d G f F_; X.val.1=focus f.charge (pull f.s (S.ratio.embed (pasta f)) F_.val.1) ∧ X.val.2=focus f.charge (pull f.s (pasta f) F_.val.2):=by
 intro X; let T:= (castX f).broad G; let b:= wrap (Domain P B) (2 • T.t); have h:b= S.ratio.embed (pasta f):=by
    unfold b T Shape.broad; rw [p]; change wrap _ (2 • G.count.val • (castX f).t)=_; rw [smul_comm]; exact (Ratio.embed_wrap (ratio G) _).symm
 have he{N:Side}(u:Shape)(P:Bkg (More N)) : stir (xtra f.charge) u P= focus f.charge (pull u.s (wrap (More N) (2 • u.t)) P):=by
    unfold focus; cases t:f.charge; rfl; rw [Cour.spin_c,Nacre.mores]; rfl
 change stir _ T _ = _∧stir _ _ _ = _; rw [he,he, ←h]; exact ⟨rfl,rfl⟩
variable (P':K.Funds S T)(hv:120 ≤ radiusB x)(hp:0<a)(hV:∀ (N':Monk SU.group S),Chir N' x→ WaveK (m:=a) Z N')(q: Reef.Rare T.up)(p:Chir A x)
local notation "t"=> Z.trot
local notation "v'"=> Z.room
local notation "l'"=> Z.post
local notation "L"=> Z.beta
local notation "zb"=> (fun U:Monk SU.group S=> U.sent x T t v' l' L)
include P' hv hp hV q p
lemma chamber_s: zb (rot f A)= focus f.charge (Lattice.pull f.s (S.ratio.embed (pasta f)) (zb A)):=by
 let b:=pasta f; let A':=clue S f.s b A; have hx:=Rink.space_s T x Z.trot Z.room Z.post Z.beta f.s b A P' (hV _ p).gap hp hv; unfold rot dice focus; split
 next=> exact Eq.trans (Rink.echo_s T x Z.trot Z.room Z.post Z.beta A' P' (hV _ (sing_b A f.s _ p)).gap hp hv q) (congrArg Reef.echo hx)
 exact hx
lemma mor_r (U:Bride G T x Z.room Z.trot Z.post A V₁ Z.beta (k+2) ((chart f) i)) (p':S.ratio=ratio G) : Bride G T x Z.room Z.trot Z.post (rot f A) (male d G f V₁) Z.beta k i:=by
 obtain ⟨f1,f2⟩:= parent_s f V₁ p'; let H:=chamber_s Z f P' hv hp hV q p
 have he:(rot f A).V=focus f.charge (pull f.s (pasta f) A.V):=by unfold rot dice focus; split<;>rfl
 have hh{D:Side}(i:Bond D)(U V:Config SU.group D)(b:Site D)(p:U (sendEdge f.s b i)=V (sendEdge f.s b i)):focus f.charge (pull f.s b U) i=focus f.charge (pull f.s b V) i:=by
    have hp:pull f.s b U i=pull f.s b V i:=by rw [read_back,read_back,p]
    unfold focus; split; exact congrArg Reef.qG hp; exact hp
 constructor
 · intro k0 h; rw [f2,he]; apply hh k0; let g:=f.s; let b:=pasta f; refine U.feat _ ?_
   have ht:=pin_h g b k0 (Lattice.halo k {i}) (halo_spec.mpr ⟨i,mem_singleton_self _,h⟩); have hp:(sendEdge f.s (pasta f) k0).1∈halo (k+2) {affine f.s b i}:=by
      have he:(halo (k+2) ({i}:Support (Domain N B))).image (affine f.s b)=halo (k+2) {affine f.s b i}:= by rw [←dignify,image_singleton]
      exact he ▸ ((image_subset_image (Eire.icing (by omega))) ht)
   exact (Rel.theatre ..).mp hp
 intro y l; rw [f1]; refine Eq.trans ?_ (congrFun H y).symm; exact hh y _ _ _ (U.pear _ (parent_h _ _ _ _ l))
omit P' hv hp hV q p
-- restore for tags WITHOUT injectivity.Sp gras.Strict ratio.Day
variable (T':Scree.Loom (mid N B))(L':Scree.Loom (mid P B)){t1 σ w:ℝ}{u l0 k1:ℕ}{q':Chi}
lemma standsT(I:Ids (mid N B))(J:Ids (mid P B))(Xr:Rill.Arch G d)(u:S.ratio=Rush.ratio G)(s:Eire.Clan G S (T:=T) u I J A T' L' Z.trot q' Z.post x Z.room w Z.beta Xr) (B₁: Roof (mid N B) t1 σ k T')(B₂:Roof (mid P B) t1 σ k1 L')(g:Bell S A x T Z.trot Z.room Z.post Z.beta t1 w)(v:0<w)(he:w<firstRadius SU.group)(hv:k+k1≤radiusB x):∀ i:Site (Domain N B),i∉ A.key.dome (30*radiusB x)→ Bride G T x Z.room Z.trot Z.post A (Lich.Muster.onK Xr) Z.beta (radiusB x+3) i:=by
 intro y p'; have ht:= g.years; have h:=congrArg Prod.fst s -- tune clan
 constructor <;> intro e H
 · have he:Disjoint (flags t1 A.V) (Skye.win k e):=by
      refine Finset.disjoint_left.mpr fun z u l=>p' (halo_spec.mpr ⟨z,?_,?_⟩); exact mem_union_right _ (g.height ((less_fl A.V g.tax) u)); apply (separation_triangle z e.1 y).trans; rw [separation_comm e.1 y]; have he:=win_r l; omega
   change Xr.val.1.2 e=_; rw [h]; exact B₁.lamp _ _ _ he
 have hu: S.ratio.parent e.1∉ A.key.dome (20*radiusB x):=fun z=>p' (dome_u z (by rw [separation_comm]; omega)); have hp:= bridgeV G u q' g B₁ B₂ hv v he I J e hu; change Xr.val.1.1 e=_; rw [h]; exact hp.1.trans hp.2.1
end YM.CF.Stake
