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
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G₅"=> SU.group
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{T:Tube G₅ S}{s:Signed}{b:Site c}{x d β a r:ℝ}{l k:ℕ}
section
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows Locations Channels
variable (T:Tube SU.group S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)
lemma train(P:Tab S)(V:Config G₅ c)(h:K.Funds S T)(ht:Reef.Rare T.up): (bunk S P (Reef.echo V)).sent x T q d l 0 =Reef.echo ((bunk S P V).sent x T q d l 0):=by
 let U:=bunk S P V; let F:= U.park; let M:=bunk S P (Reef.echo V); let L:=room x U.key F; let a:= U.fuel x T q d l 0; let Y:= M.fuel x T q d l 0
 obtain ⟨v,D,hH,s⟩:=h.feeds; rw [←h.high] at hH
 have hu:M.bush x=Reef.echo (U.bush x):=funext fun i=>False.elim ((notChilled S M.park x i.val) i.property)
 have he:Y=Orthogonal.move (onBond (Char.shiftF (Bond f))) L.onKey a:=by
    unfold Y a; rw [oasisN T q x d l rfl,oasisN T q x d l rfl,hu]; apply boxL (storyE T _ _ _ _ _ _ _ _ (funds_branch h) hH ht) (fun _=>Iff.rfl) (funds_branch h) hH
 let Z:=landed x U.key F U.V (U.bush x) a; change landed x U.key F (Reef.echo V) (M.bush x) Y=Reef.echo Z
 ext1 i; by_cases hi:i∈ F.trunks
 · have ht(x:LinkArray G₅ F.Free):F.drape x i=1:=F.on_tree _ ⟨i,hi⟩; unfold Z landed Next.SectorChange.physical; change F.drape _ i=qG (F.drape _ i); rw [ht,ht,map_one]
 let j:F.Free:=⟨i,hi⟩; let t:Active U.key x F:=⟨j,notChilled S F x _⟩; unfold Z landed Next.SectorChange.physical
 change F.drape _ t.val.val=qG (F.drape _ t.val.val); rw [F.off_tree,F.off_tree]; unfold Next.SectorChange.returned thaw; rw [freeze_regular,freeze_regular, he]; unfold release; rw [move_tape]; change SU.group.lieExp (Reef.frolic (tape a t))*replica S.ratio (Reef.echo V) _=qG _; rw [repE, cool_a,map_mul] -- tune
end
open Cube Lat Rush Cour Scroll Laic Kennel Spire Paige
variable {n B m X: Side}{T: Roam m X B}{G: Ratio (CSide m B) (CSide X B)}{p:Tube G₅ T}
section
variable(T: Tube G₅ S)(q:Chi)(F:Tab S)
lemma roots(y:Mast G₅ c)(h:Fire T x F.1 F.2 l a k r y): (bunk S F (satU G₅ a y)).sent x T q d l 0= Push.Uniform.fine G₅ F.1 (Souk.flute F.1 (sol S T F.2 x F.1 l) a y):=by
 have ht:=originY T x (bunk S F (satU G₅ a y)) y rfl rfl rfl h q d 0 1; -- tune
 unfold fX Jazz pulse Function.comp at ht; simp only [zero_add] at ht; rw [pull_one,pull_one] at ht; have he(V:Config SU.group f): Lattice.translate 0 V=V:=by funext j; change V (j.1+0,j.2)=_; rw [add_zero,Prod.eta]
 simp_rw [he] at ht; exact ht
end
section
variable(p:Tube G₅ T)(q:Chi)(x d:ℝ)(l:ℕ)
def hornY (F:Tab T)(v:Bkg (More (CSide m B))): nomA m X B:= ((bunk T F v).sent x p q d l 0,v)
lemma bright (h:T.ratio=ratio G)(F:Tab T)(g:Sweep (CSide m B))(V: Config SU.group (More (CSide m B)))(hp:K.Funds T p)(hx:Rare p.up):
 let s:=castX g; let b:= wrap (More (CSide m B)) (2 • s.t)
 hornY p q x d l (Arena.dial T s.s b F) (flashA g V) = Scroll.stanza G s (xtra g.charge) (hornY p q x d l F V):=by
 intro s b; let i:= wrap (More (CSide X B)) (2 • (Shape.broad G s).t); have he:i= T.ratio.embed b:=by
    unfold i b Shape.broad; rw [h]; change wrap (More (CSide X B)) (2 • G.count.val • s.t)= _; rw [smul_comm]; exact (Ratio.embed_wrap (ratio G) _).symm -- tune
 let W:=hornY p q x d l F V; let t:= Arena.dial T s.s b F; have hz:(hornY p q x d l t (pull s.s b V)).1=pull s.s i W.1:=by
    unfold hornY; dsimp only; unfold t; rw [←bench]; change _=pull _ _ ((bunk T F V).sent x p q d l 0); rw [he]; exact Arena.shine_T s.s b (bunk T F V) hp rfl
 refine Prod.ext ?_ rfl; change (hornY p q x d l t (stir (xtra g.charge) s V)).1=stir (xtra g.charge) (Shape.broad G s) W.1
 cases g.charge
 · exact hz
 rw [spin_c,spin_c]; rw [show (hornY p q x d l t (Reef.echo (Yg s V))).1=Reef.echo ((hornY p q x d l t (Yg s V)).1) from train p x q d l t _ hp hx]; exact congrArg Reef.echo hz
lemma wreath (F:Tab T)(v:Mast G₅ (More (CSide m B)))(h:Fire p x F.1 F.2 l a k r v) : hornY p q x d l F (satU G₅ a v)= Laic.hats F.1 (Souk.flute F.1 (sol T p F.2 x F.1 l) a v):=by
 refine Prod.ext (roots p q F v h) ?_; -- tune hats
 unfold Laic.hats Push.Uniform.outer Souk.flute Push.Uniform.curve; rw [Push.Uniform.paint_meet]; rfl
lemma candle (h:T.ratio=ratio G)(F:Tab T)(V: Config SU.group (More (CSide m B)))(g:Site (More (CSide m B))→ SU.E)(hp: K.Funds T p): hornY p q x d l F (Lattice.gauge g V)= Peaks.july G (constantGauge g T.ratio) (hornY p q x d l F V):=by
 refine Prod.ext (gaZ p x q d l K hp F g V) ?_; have he: Peaks.scaleG G (constantGauge g T.ratio) = g:=by rw [h]; ext1 i; simp only [Peaks.scaleG,Function.comp_apply,constantGauge,Ratio.embed_parent]
 change _=Lattice.gauge (Peaks.scaleG G (constantGauge g T.ratio)) V; rw [he]; rfl
end
end YM.CF.Facet
