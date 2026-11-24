import YM.CF.Facet.Law
import YM.CF.Facet.Arc
import YM.CF.Facet.Hemp
import YM.CF.Facet.Horn
import YM.CF.Cour.Culm
import YM.CF.Tarn.Sold
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Facet
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff  InnerProductSpace
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
local notation "G₅"=> SU.group
open Cube Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec
variable {n B m X: Side}{T: Roam m X B}{G: Ratio (CSide m B) (CSide X B)}{p:Tube G₅ T}
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{A:Finset (Site f)}{o:Site c}{s:Signed}{b:Site c}{x e d β a r σ w:ℝ}{l k:ℕ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {F:Tab T}{C V R Z η:ℝ}{Q: Msca m X B G e}{Φ:nomA m X B→ ℂ}{i:Site (More (CSide m B))}
variable{U U':Config G₅ (More (CSide m B))}{t:ℕ}
open Levier
abbrev pasta(g:Sweep (CSide m B)):=wrap (More (CSide m B)) (2 • (castX g).t)
abbrev parch (T:Roam m X B)(g:Sweep (CSide m B))(F:Tab T):= Arena.dial T g.s (pasta g) F
lemma gearP(T:Roam m X B)(G)(hg:T.ratio=ratio G)(s:Sweep (CSide m B))(p: Site (More (CSide X B))): T.ratio.parent (((castX s).broad G).anon (CSide X B) p)=(castX s).anon (CSide m B) (T.ratio.parent p):=by
 let b:= pasta s; let a:= castX s
 have he:Shape.anon (a.broad G) (CSide X B) p=affine a.s (T.ratio.embed b) p:=by
    unfold Shape.anon; rw [hg]; change affine a.s (wrap (More (CSide X B)) (2 • (Shape.broad G a).t)) p= _; apply congrArg (fun b=>affine a.s b p)
    change wrap (More (CSide X B)) (2 • G.count.val • a.t)= _; rw [smul_comm]; exact (Ratio.embed_wrap (ratio G) _).symm -- tune
 rw [he]; exact AnalyticBridge.GaussianFieldAlignment.Locations.parent_map ..
lemma mountF (S:mSeal X B)(g:Sweep (CSide m B))(hg:T.ratio=ratio G): mount (ratio G) (toRoar G g S)=roarD _ (castX g) (mount (ratio G) S):=by unfold mount toRoar roarD; rw [image_image,image_image]; refine congrArg (fun i:_=> S.image i) (funext fun i=>?_); have h:= gearP T G hg g i; rw [hg] at h; exact h
lemma turtle_t(g:Sweep (CSide m B))(hg:T.ratio=ratio G)(S:mSeal X B)(i:Site (More (CSide m B))): turtle (ratio G) S i= turtle (ratio G) (weaveS G g S) ((castX g).anon _ i):=by
 unfold turtle; change _= if _∈mount (ratio G) (toRoar G g S) then (↑(mount _ _).card:ℝ)⁻¹ else 0; rw [show mount (ratio G) (toRoar G g S)=_ from mountF S g hg]; change _ = if _ then (↑(mount _ (weaveS G g S)).card:ℝ)⁻¹ else 0; rw [show mount (ratio G) (weaveS G g S)=_ from mountF S g hg]; unfold roarD; simp [card_image_of_injective _,(castX g).anon_b.1, (castX g).anon_b.1.eq_iff] -- tune
variable (p:Tube G₅ T)(x:ℝ)(q:Chi)(d u:ℝ)(l:ℕ)(Q:Msca m X B G e)(h:0<e)
variable (hp:K.Funds T p)(he:Ready p x)(v:∀ F:Tab T,Fleck G h F.1 η C k)(H: Tally Q Φ η C a Z k)(hx:∀ F:Tab T,InterestP p x l F k u η V R)(hG:T.ratio=ratio G)(hz:Rare p.up)(hv:tyke G Q)
include hp he v H hx hG hz hv
lemma torn (i:Site (More (CSide m B)))(U:Config G₅ (More (CSide m B)))(t:U∈pines G₅ _ u)(F:Tab T)(g:Sweep (CSide m B)): turf G p q x d l Q h (parch T g F) i (flashA g U)=payZ g (turf G p q x d l Q h F ((castX g).anon _ i) U):=by
 let D:=turf G p q x d l Q h; let Y:=parch T g F; let j:=(castX g).anon _ i; let U':= hornY p q x d l F U; let V:=hornY p q x d l Y (flashA g U); have hi: U' ∈Rent0 G e:= firm p x q d u l Q h hp he (v _) H (hx _) hG _ t; have hx := bright p q x d l hG F g U hp hz
 let N:Rent0 G e:=⟨_,hi⟩; let W:=male e G g N; have hm: V=W.val:=hx; have hJ: V∈ Rent0 G e:=hm.symm ▸ W.property
 let L:=univ.filter fun j:mSeal X B=>j.card ≤ Stores.till x; have hL: L.image (toRoar G g)= L:=by
    let A:=weaveS G g; ext q; obtain ⟨q,rfl⟩:=A.surjective q; change A q ∈ L.image A↔ _; simp only [mem_image,A.injective.eq_iff, exists_eq_right,L,mem_filter,mem_univ,true_and]; rw [show (A q).card= q.card from rumR g q]
 change (∑ s∈L, turtle _ s i • Q s (pear G h V))=payZ g (∑ s∈L,turtle _ s j • Q s (pear G h U'))
 rw [pear_even _ _ hi, pear_even _ _ hJ, ←din_t,map_sum]; conv_rhs=>rw [← hL,Finset.sum_image (by exact fun i _ j _ h=>(weaveS G g).injective h)]
 refine sum_congr rfl fun k _=>?_ ; rw [map_smul,din_t]; change turtle _ k i • Q k ⟨V,hJ⟩= turtle (ratio G) (weaveS G g k) j • payZ g (Q _ N); rw [turtle_t g hG]; congr 1
 have ht:=hv g (weaveS G g k) N; rw [show toRoar G g⁻¹ (weaveS G g k)=k from (weaveS G g).symm_apply_apply k] at ht; exact (congrArg (Q k) (show (⟨V,hJ⟩:Rent0 G e)= W from Subtype.ext hm)).trans ht
omit hp he v H hx hG hz hv in
lemma glacial(N:Side)(g:Sweep N):flashA g (1:Config G₅ _)=1:=by
 ext1 i; unfold flashA stir; simp only [Function.comp_apply,Lattice.pull,Step.read, Pi.one_apply]; simp -- tune
lemma viz (g:Sweep (CSide m B))(p':1000 ≤radiusB x)(i:Site (More (CSide m B)))(U:Config G₅ (More (CSide m B)))(F:Tab T)(t:U∈pines G₅ _ u)(s:flashA g U∈pines G₅ _ u): franc p x q d u l Q h (parch T g F) i (flashA g U)=payZ g (franc p x q d u l Q h F ((castX g).anon _ i) U):=by
 let A:= parch T g F; let Z:=turf G p q x d l Q h; have hO:= pines_o p x u l Q h hp he (v F) H (hx F) hG -- args
 have hy(P:Tab T)(j:Site _)(u')(h:u'∈pines G₅ _ u): franc p x q d u l Q ‹0<e› P j u'= Z P j u'-Z P j 1:=by unfold franc; rw [song _ _ _ _ _ _ _ _ hp he (v _) H (hx _) hG p' h,song _ _ _ _ u _ _ _ hp he (v _) H (hx _) hG p' hO]
 rw [hy A i _ s,hy F _ _ t,←din_t,map_sub]; let Y:= (castX g).anon _ i; refine congrArg₂ (·-·) (torn p x q d u l Q h hp he v H hx hG hz hv i _ t F g|>.trans (din_t ..).symm) ?_; have he:= torn p x q d u l Q h hp he v H hx hG hz hv i _ hO F g; rw [glacial] at he; exact he.trans (din_t ..).symm -- tune
end YM.CF.Facet
