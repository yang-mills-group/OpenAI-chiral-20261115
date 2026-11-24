import YM.CF.Vp929.Stage.Institute
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
open Test TestW QuiltB

abbrev capScale (F G:ℝ→ℝ)(x:ℝ):=|F x| + |G x|
lemma capAll (F G) : F ≤ capScale F G ∧ G ≤ capScale F G:=by
 constructor <;> intro i
 · exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
 exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
variable {δ F' G' Q₀ C:ℝ→ℝ}{N0:ℕ}{h:ℝ}
lemma joinPermit (p:Appointed J q Q₀ δ C h N0)(hv:sizeK R.L 2 F')(ht:Chill_v G') : Appointed J q (capScale Q₀ F') (capScale δ G') C h N0:=by
 have he:sizeK R.L 2 (capScale Q₀ F'):= (p.fiscal.cost_d (W:= (fun i : ℝ=> |Q₀ i|)) (Eventually.of_forall (fun x=> Eq.le (abs_abs _)))).accrue (hv.cost_d (Eventually.of_forall (fun x=>Eq.le (abs_abs _))))
 have hp:Chill_v (capScale δ G'):= (p.post.trend (F:= (fun i:ℝ=>|δ i|)) (Eventually.of_forall (fun x=>Eq.le (abs_abs _)))).noteR (ht.trend (Eventually.of_forall fun x=>Eq.le (abs_abs _)))
 obtain ⟨P,e,hG,v,V⟩:=p.temperature
 refine ⟨⟨P,e,?_,v,cutMono V le_rfl (capAll ..).1 (capAll ..).1 ⟩,hp,Eventually.of_forall fun _=> add_nonneg (abs_nonneg _) (abs_nonneg _),he⟩
 refine ⟨?_, hG.compare⟩; intro m n u x p p' ξ r
 let h:= hG.provides m n u x p p' ξ r; refine ⟨fun b F z t=>?_ ,h.analytic,fun b F q v z=> ?_, ?_⟩
 · obtain ⟨e,t⟩:= h.cost b F z t; exact ⟨e,t.trans ((capAll ..).1 x)⟩
 · obtain ⟨e,w,t,a,c,l⟩:= h.real b F q v z; exact ⟨e,w,t.trans ((capAll ..).1 x),a,c,l⟩
 intro a c b b' F F'' o ht he hu v; obtain ⟨t,e⟩:= h.stars a c b b' F F'' o ht he hu v; refine ⟨t,e.trans ?_⟩; gcongr; exact (capAll ..).1 x
end Focus
end Pitching
end YM.CF.Py.Rate
