import YM.CF.Facet.Gust
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
structure Thu(p:Tube G₅ T)(x:ℝ)(u:ℝ)(l:ℕ)(Q:Msca m X B G e)(h:0<e)(K:Teller G₅)(k:ℕ)(η C a Z V R:ℝ)(Φ:nomA m X B→ℂ):Prop where
 funds : K.Funds T p
 ready : Ready p x
 tall: ∀ F:Tab T, Fleck G h F.1 η C k
 pay :Tally Q Φ η C a Z k
 ears:∀ F:Tab T,InterestP p x l F k u η V R
 sizes:T.ratio=ratio G
 read:Rare p.up
 tone :tyke G Q
 fine:1000≤radiusB x
 width:0 < u
variable{u:ℝ}{q:Chi}{h:0<e}
lemma offer(H:Thu p x u l Q h K k η C a Z V R Φ)(F:Tab T)(i): Kind T F F (pavilion (Cay.horn x l) i):= ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma rate_pP(H:Thu p x u l Q h K k η C a Z V R Φ)(i:Site (More (CSide m B)))(F F':Tab T)(t:Kind T F F' (pavilion (Cay.horn x l) i)) : franc p x q d u l Q h F i=franc p x q d u l Q h F' i:=by
 have he i':plain p x q d u l Q h F i i' = plain p x q d u l Q h F' i i':=by
    unfold plain salsa; split; swap; · rfl
    next e=>
       let U:=e.choose_spec.choose; let H'(F:Tab T):= firm p x q d u l Q h H.funds H.ready (H.tall F) H.pay (H.ears _) H.sizes U e.choose_spec.choose_spec.1
       exact threads G _ _ _ _ _ H.sizes Q h _ _ _ 0 _ _ H.pay _ _ (H' F) (H' F') H.ready H.fine t (fun _ _=>rfl)
 ext1 i; unfold franc; rw [he,he 1] -- tune maybe rw all
lemma layer_k(H:Thu p x u l Q h K k η C a Z V R Φ) : let U:=franc p x q d u l Q h; LayerP (CSide m B) (fun i=> Arena.aria fun f=> U f i):=by
 intro U i y; let N:=CSide m B; let D:=More N; let b:= (assembly N).embed y; let P(w:Config G₅ D):= Lattice.translate b w
 let K':= Sweep.mk 1 y false; let H':=Arena.spun T 1 b; have hz:pasta K'= b:= (Ratio.embed_wrap (assembly N) _).symm.trans (by rw [show (castX K').t=Lattice.lift y from rfl,wrap_lift])
 have ht(f'): parch T K' f'=H' f':=by rw [parch,hz]; rfl
 have hp(z:Site D): (castX K').anon _ z=z+b:=by rw [stir_l]; change affine (1:Signed) b z=z+b; simp [affine]
 have he(v:Config G₅ D):flashA K' v=P v:=by change pull (1:Signed) (pasta K') v=_; rw [hz, pull_one]; -- tune d_eq
 have hv(v:ℂ): payZ K' v=v:=by unfold payZ wageZ; change cSignX (false.xor (detX 1)) _= _; rw [det_i]; rfl
 have hm(F:Tab T)(V:Config G₅ D): plain p x q d u l Q h F (i+b) V=plain p x q d u l Q h (H' F) i (P V):=by
    let X:=pines G₅ D u; let r:=Cay.horn x l
    have ht'(U:Config G₅ D)(hx:U∈X):turf G p q x d l Q h (H' F) i (P U)=turf G p q x d l Q h F (i+b) U:=by
       have ht' := torn p x q d u l Q h H.funds H.ready H.tall H.pay H.ears H.sizes H.read H.tone i _ hx F K'; rwa [he,ht,hp,hv] at ht'
    by_cases g:found X (i+b) r V
    · obtain ⟨g,U,h',t⟩:=g; rw [honor _ _ _ _ _ _ _ h H.funds H.ready (H.tall _) H.pay (H.ears _) H.sizes H.fine _ h' t]
      have h:Lattice.translate b U=P U:=rfl; rw [honor _ _ _ _ _ _ _ ‹0<e› H.funds H.ready (H.tall _) H.pay (H.ears _) H.sizes H.fine _ (transT _ _ _ h') (show Tarn.drift G₅ i (horn x l) (Lattice.gauge (fun i=>g (i+b)) (Lattice.translate b U)) (Lattice.translate b V) from ?_)]; exact (ht' U h').symm
      exact trop .. ▸ pivotU _ _ _ _ _ _ t -- tune
    have hh:¬found X i r (P V):=fun p=>by
       have hp:i=(i+b)+ -b:=by simp
       have ht:= Tarn.paveT (r:=r) u (i+b) (-b) (hp ▸ p)
       rw [show Lattice.translate (-b) (P V)=V by ext1 x; change V (x.1+ -b+b,x.2)=_; simp] at ht; exact g ht
    unfold plain salsa; rw [dif_neg g,dif_neg hh]
 have hP:Fintype.card (Tab T)=Fintype.card (Tab T):=rfl
 funext v; let W:= Arena.aria (fun f=>U f i); change _=W (P v); unfold W Arena.aria; simp only [Pi.smul_apply,Finset.sum_apply]; apply congrArg ((Fintype.card (Tab T):ℂ)⁻¹ • ·); rw [← Equiv.sum_comp H' (fun i'=> U i' i (P v))]; apply sum_congr rfl; intro j _; unfold U franc; rw [← hm j v, hm j 1,show P 1=1 by ext1; rfl] -- tune
end YM.CF.Facet
