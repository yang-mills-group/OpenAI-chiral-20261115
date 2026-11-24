import YM.CF.Facet.Wealth
import YM.CF.Facet.Warm
import YM.CF.Facet.Sole
import YM.CF.Facet.North
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
variable{u:ℝ}{q:Chi}{h:0<e}
open Stationary Push.Loops
open Stationary Push.Loops
variable{α:ℝ}{J:ChartRatio G₅}
private lemma foodZ{D E:Type}[NormedAddCommGroup D] [NormedSpace ℝ D][NormedAddCommGroup E][NormedSpace ℝ E]{F H:D→E}(h:cFoot 2 F)(v:cFoot 2 H)(ht:ContDiffAt ℝ (↑k) F 0)(hs:ContDiffAt ℝ (↑k) H 0)(hp:1 ≤ k): cFoot 2 (F+H) ∧ cFoot 2 (F-H):=by
 constructor <;> intro i l
 · rw [iteratedFDeriv_add_apply (ht.of_le (by exact_mod_cast (by omega : i ≤ k))) (hs.of_le (by exact_mod_cast (by omega : i ≤ k))), h _ l,v _ l,add_zero]
 rw [iteratedFDeriv_sub_apply (ht.of_le (by exact_mod_cast (by omega:i ≤ k))) (hs.of_le (by exact_mod_cast (by omega : i ≤ k))), h _ l,v _ l,sub_self]
lemma paysY {u v t γ w Mx:ℝ}{Y:Tab T} (H:Thu p x u l Q h K k η C a Z V R Φ)(hp:FreshT p x v q J r α γ k l Y w Mx)(hu:FreshT p x v q J r 0 γ k l Y w Mx)(ht:0 < t)(hv: t ≤ u)(hl:u ≤1)(hc:t ≤ v)(hz:1 ≤ k)(hd:0≤a)(hR:0≤ R): let F:=snowG G p q x u α d l Q h Y; let A:=Jet.composeCost k (Jet.composeCost k ((G.count.val:ℝ)^4*Z) R) (1+u⁻¹)
 ∀ i,CakeF (F i) i (Cay.horn x l) k t (A+A+(w+w)) ∧ cFoot 2 (satX (F i)):=by
 intro V' D i; obtain ⟨xk,hx⟩:=hp.bonds d i; obtain ⟨rK,hK⟩:=hu.bonds d i; obtain ⟨fK,hF⟩:= caked p x q d u l Q h H.funds H.ready (H.tall Y) H.pay (H.ears Y) H.sizes (i:=i) H.fine H.width hl hd hR hz
 let K':=Tarn.Coin p x v q J r d α l Y i; let V':=Tarn.Coin p x v q J r d 0 l Y i
 let T':=franc p x q d u l Q h Y i; let S:=Cay.horn x l; have hKK: CakeF (K'-V') i S k t (w+w):= (xk.less rK).under hc le_rfl le_rfl
 have hℓ:CakeF T' i S k t (D+D):= fK.under hv le_rfl le_rfl
 have ht':‖(0:InputZ G₅ (More (CSide m B)))‖< t:=by rw [norm_zero]; exact ht
 have he:i=i:=rfl
 change CakeF (snowG G p q x u α d l Q h Y i) _ _ _ _ _∧ cFoot 2 (satX (snowG G p q x u α d l Q h Y i)); rw [show snowG G p q x u α d l Q h Y i=T'+(K'-V') from ?_]; swap; · unfold snowG; rw [kappaY p q x α d l Y J v r]; rfl
 have hE:cFoot 2 (satX (K'-V')):= (foodZ hx hK ((xk.under hc le_rfl le_rfl).ledger _ ht').smooth (((rK.under hc le_rfl le_rfl).ledger _ ht').smooth) hz).2
 refine ⟨hℓ.add hKK,?_⟩; exact (foodZ hF hE (hℓ.ledger _ ht').smooth (hKK.ledger _ ht').smooth hz).1
end YM.CF.Facet
