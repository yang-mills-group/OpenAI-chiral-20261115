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
section
variable(p:Tube G₅ T)(x:ℝ)(q:Chi)(d u:ℝ)(l:ℕ)(Q:Msca m X B G e)(h:0<e)
def plain (P:Tab T)(i: Site (More (CSide m B))):= salsa (pines G₅ _ u) i (Cay.horn x l) (turf G p q x d l Q h P i)
def franc (P:Tab T)(i: Site (More (CSide m B)))(y:Config G₅ (More (CSide m B))):=plain p x q d u l Q h P i y-plain p x q d u l Q h P i 1
variable (hp:K.Funds T p)(he:Ready p x)(v:Fleck G h F.1 η C k)(H: Tally Q Φ η C a Z k)(hx:InterestP p x l F k u η V R)(hG:T.ratio=ratio G)
include hp he v H hx hG
lemma firn(g:Site (More (CSide m B))→ SU.group.El)(X:Config G₅ (More (CSide m B)))(hX:(hornY p q x d l F X)∈Rent0 G e) :
 let Y:=Lattice.gauge g X; (hornY p q x d l F Y)∈Rent0 G e ∧ turf G p q x d l Q h F i Y=turf G p q x d l Q h F i X:=by
 intro Y; let A:= hornY p q x d l F; let Z:=constantGauge g T.ratio; have hy: A Y=Peaks.july G Z (A X):= candle p q x d l hG F X g hp
 have hA: A Y∈ Rent0 G e:= hy.symm ▸ Peaks.joint_g G (A X) hX Z
 refine ⟨hA,?_⟩; obtain ⟨N,H,Y⟩:= H.members; unfold turf; refine sum_congr rfl fun j _=>?_; apply congrArg; unfold test; rw [pear_even G h hA,pear_even G h hX]; let S:Rent0 G e:=⟨_,hX⟩; let U:Rent0 G e:= ⟨_,hA⟩; change Q j U=Q j S; rw [show U=(dressL G e).dress Z S from Subtype.ext hy]; exact (H j).gauge ..
lemma firm(y:Config G₅ (More (CSide m B)))(ht:y∈pines G₅ _ u):hornY p q x d l F y∈Rent0 G e:= by obtain ⟨w,g,rfl⟩:=ht; exact on_turf F h v hx _ (mem_ball_zero_iff.mp g)
lemma leak (p':1000 ≤radiusB x) :StampP (pines G₅ (More (CSide m B)) u) i (Cay.horn x l) (turf G p q x d l Q h F i):=by
 refine glaze_r fun y ht z ht' g hg=>?_; obtain ⟨hh,h⟩:=firn p x q d u l Q h hp he v H hx hG (i:=i) g y (firm p x q d u l Q h hp he v H hx hG y ht); rw [←h]; exact threads G p q x d l hG _ _ _ _ _ 0 _ _ H _ _ hh (firm p x q d u l Q ‹_› hp he v H hx hG _ ht') he p' (⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩) hg
lemma honor (p':1000 ≤radiusB x) {U' V': Config G₅ (More (CSide m B))}(g:Site (More (CSide m B))→SU.group.El)(hx':U'∈ pines G₅ _ u)(hz:Tarn.drift G₅ i (Cay.horn x l) (Lattice.gauge g U') V'): plain p x q d u l Q h F i V'= turf G p q x d l Q h F i U':=land_s (leak p x q d u l Q h hp he v H hx hG p') hx' g hz
lemma song (p':1000≤radiusB x){U:Config G₅ (More (CSide m B))}(X:U∈pines G₅ _ u): plain p x q d u l Q h F i U=turf G p q x d l Q h F i U:= honor p x q d u l Q h hp he v H hx hG p' 1 X fun _ _=>by rw [fix_s] -- tune
lemma pines_o : (1:Config G₅ (More (CSide m B)))∈pines G₅ (More (CSide m B)) u:=by
 let Y:Mast G₅ (More (CSide m B)):=0; have hp: satU G₅ u Y=1:=by simp [satU,facadeX,Y]
 exact hp ▸ pine_p _ Y (by simp [Y])
lemma caked (p':1000 ≤radiusB x)(hS:0 < u)(hU:u ≤ 1)(hV:0 ≤ a)(hK:0 ≤ R)(hz:1 ≤ k):
 let V:=Jet.composeCost k (Jet.composeCost k (G.count.val^4*Z) R) (1+u⁻¹); let W:=franc p x q d u l Q h F i; CakeF W i (Cay.horn x l) k u (V+V) ∧ cFoot 2 (satX W):=by
 intro X V'; have ht:= leak p x q d u l Q h hp he v H hx hG (i:=i) p'; let U:= plain p x q d u l Q h F i
 have h0: ‖(0:InputZ G₅ (More (CSide m B)))‖<u:=by simp [hS]
 have hp : CakeF U i (Cay.horn x l) k u X:=by
    refine ⟨SpiceU ht,?_⟩; intro y hy
    let L:= chair p F.1; let Y:=u⁻¹ • L; have hc(y:InputZ G₅ (More (CSide m B)))(hy:‖y‖<u):‖Y y‖<1:=by
       rw [show Y y=u⁻¹ • L y from rfl,norm_smul_of_nonneg (by positivity),inv_mul_lt_iff₀ hS, mul_one]; exact (Push.Uniform.tint_inv_le y).trans_lt hy
    have hY:=hc y hy; have hi:=lane i F h v hx H q d hV hK _ hY
    have hv:0 ≤ u⁻¹:=by positivity
    have hψ : ‖Y‖ ≤ u⁻¹:=by unfold Y; erw [norm_smul, Real.norm_of_nonneg hv]; refine mul_le_of_le_one_right hv (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun t=> (Push.Uniform.tint_inv_le t).trans_eq (one_mul _).symm))
    apply (hi.comp (f:=Y) (allows_linear (hψ.trans (le_add_of_nonneg_left zero_le_one)) (hY.le.trans (le_add_of_nonneg_right hv)))).germ
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with y hy
    have hψ : satU G₅ u (Y y)= represent y:= by unfold satU; rw [show u •Y y= L y from smul_inv_smul₀ hS.ne' (L y)]; exact chap p F.1 y
    change turf _ _ _ _ _ _ _ _ _ _ (satU G₅ u _) = U (represent y); rw [←hψ]; exact (song p x q d u l Q h hp he v H hx hG p' (pine_p u (Y y) (hc _ (mem_ball_zero_iff.mp hy)))).symm
 let V:SpaceX G₅ (More (CSide m B)):=fun _=> U 1
 have ht :‖U 1‖ ≤ X:=by simpa only [satX,Function.comp_apply,link_one] using (hp.ledger _ h0).value
 have hV':CakeF V i (Cay.horn x l) k u X:=⟨⟨fun _ _=>rfl,fun _ _ _=>rfl⟩,fun y _=>allows_const y ht⟩
 have ho:=hp.less hV'; exact ⟨ho, kleur V' i ho.toAtom hz (sub_self _) (ho.ledger 0 h0|>.smooth) Thera.yet_one⟩
end
end YM.CF.Facet
