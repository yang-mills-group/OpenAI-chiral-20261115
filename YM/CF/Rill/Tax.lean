import YM.CF.Rill.Luci
import YM.CF.Rill.Oboe
import YM.CF.Rill.Hugs
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Jet Atala Cube
-- coating Eta.κ linear tents d uncertain.Can sample Q mixture measure. support fits Region.ShapeReal. For Renewal context Beta not diff separate.
variable {S: StepData (More c) (More f)} {E F X:Support (More c)}{M N:Monk G S}{T:Tube G S}{A:Loom c}{A':Loom f}{k k' m:ℕ}{P: HomeL (More c) (More f)}
structure TasteZ (P: HomeL (More c) (More f))(M: Monk G S) (A:Loom c)(A':Loom f)(Y X:Support (More c))(x d e b t w:ℝ) (T:Tube G S)(q:Chi)(m r v l k k':ℕ):Prop where
 opt:MarkP M Y x e b P l m T q d
 earn: Roof c e w k' A
 hue: Roof f e t k A'
 reach:0<fiery G x S.patch.L
 span: fiery G x S.patch.L < e
 cost:k+k' ≤ radiusB x
 ho: b <firstRadius G
 age:1000≤radiusB x
 cap: M.key.dome (5*radiusB x) ⊆ Y
 spirit:halo (k+k'+30) X ⊆ Y
 call:looseV x M r v (legL M T x q d l P)
namespace TasteZ
variable (h:TasteZ P M A A' F X x d e b t w T q m r v l k k')
variable {B:Type}[NormedAddCommGroup B][NormedSpace ℝ B]{y:B}{a:ℝ}
include h
lemma cutsZ(J:B→ HomeL (More c) (More f))(hs:J y=P)(hu: ContinuousAt J y)(r':∀ᶠ i in 𝓝 y,P.2.1=(J i).2.1)(l':∀ᶠ i in 𝓝 y,Agrees (halo 12 (halo (4*radiusB x) M.key.flags)) P.1 (J i).1) (i:Ids f)(j:Ids c) (t':∀ z:Bond (More f),S.ratio.parent z.1∈X→ Tender (fun a=>legL M T x q d l (J a) z) y a m)(u:∀ z:Bond (More c),z.1∈X → Tender (fun a=>(J a).1 z) y a m):
 (∀ z:Bond (More f),S.ratio.parent z.1∈X→ Tender (fun a=>A' (legL M T x q d l (J a),i) z) y a m)∧(∀ z:Bond (More c),z.1∈X→ Tender (fun a=>A ((J a).1,j) z) y a m):=by
 have he:=loomM J hs r' l' hu h.opt h.reach h.span h.hue h.earn h.call h.ho h.cost h.age h.spirit h.cap i j
 refine ⟨fun z p=>?_,fun z p=>?_⟩
 · let W(a):=A' (legL M T x q d l a,i) z; have hp:=t' z p; by_cases k:z.1∈ halo (k+2) (Passage S M.key.place)
   · apply ((Shake.holds (SU.group.mat (W P))).bag hp.price).same (he.mono fun i' p'=> ?_); obtain g:=(p'.1 z p); rw [if_pos k] at g; exact congrArg SU.group.mat g.symm
   refine hp.same (he.mono fun i' p'=>?_); obtain g:=(p'.1 z p); rw [if_neg k] at g; exact congrArg SU.group.mat g.symm
 let W(a:HomeL (More c) (More f)):=A (a.1,j) z; have hp:=u z p; by_cases k:z.1∈ halo (k'+2) M.key.flags
 · refine ((Shake.holds (SU.group.mat (W P))).bag hp.price).same (he.mono fun i' p'=>?_); obtain g:=(p'.2 z p); rw [if_pos k] at g; exact congrArg SU.group.mat g.symm
 refine hp.same (he.mono fun i' p'=>?_); obtain g:=(p'.2 z p); rw [if_neg k] at g; exact congrArg SU.group.mat g.symm
-- priced region.X controls tents. actual birth sectors comparison M.ray.Y etc. Pulse films F_move.
variable (D:B→L[ℝ] Directions G (More c))
omit h
def hover(W:Config SU.group (More c))(D:B→Directions SU.group (More c))(z:B)(x:ℝ)(P: HomeL (More c) (More f)): HomeL (More c) (More f):= (Vmove x W (D z), P.2)
lemma pact (hp:Beat (monkD M P) N F)(p: halo ((l+70)*radiusB x) X ⊆ F)(ht:Ready T x)(he:1000≤ radiusB x)(hD: ‖D‖≤a)(v:1≤a){K:ℝ}(ξ:∀ i,Tender (fun v=> Vmove x N.V v i) 0 K m)(ζ:∀ i,Tender (fun v=>(N.atop v x).sent x T q d l P.2.2.1 i) 0 K m):
 (∀ i: Bond (More f),S.ratio.parent i.1∈X→ Tender (fun v:B=> legL M T x q d l (hover P.1 D v x P) i) 0 (K*a^m) m)∧(∀ i: Bond (More c),i.1∈ X→ Tender (fun v:B=>(hover P.1 D v x P).1 i) 0 (K*a^m) m):=by
 let Q(v):= hover P.1 D v x P
 have hu(v:B):Beat (monkD M (Q v)) (N.atop (D v) x) F:=by
    refine ⟨hp.road,hp.fr,hp.fe,hp.trunks,?_,hp.data,hp.color⟩; intro i a u; exact congrArg (fun y=>SU.group.lieExp (temp x • D v i)*y) (hp.view i a u)
 refine ⟨fun i t=>?_,fun i t=>?_⟩
 · apply (Shake.dil D _ (ζ i) hD v).same; refine Eventually.of_forall fun y=>?_ ; exact congrArg SU.group.mat ((hu y).sym.backF (β:= P.2.2.1) ht he i (Subset.trans (Corona.halo_mono (show (l+62)*radiusB x ≤ _ from by simp_rw [Nat.add_mul]; omega) (singleton_subset_iff.mpr t)) p)) -- tune
 apply (Shake.dil D _ (ξ i) hD v).same; refine Eventually.of_forall fun y=>?_ ; have hz:=Work.E01.sep_step_le i.1 i.2; exact congrArg SU.group.mat ((hu y).view i ((halo_subset ..).trans p t) (p (halo_spec.mpr ⟨_,t,hz.trans (by simp_rw [Nat.add_mul]; omega)⟩))).symm
end TasteZ
end YM.CF.Rill
