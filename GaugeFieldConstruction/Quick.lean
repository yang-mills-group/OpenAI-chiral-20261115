import GaugeFieldConstruction.Caliber
import GaugeFieldConstruction.Bough
import GaugeFieldConstruction.Kasol
import GaugeFieldConstruction.Bracer
import GaugeFieldConstruction.Savio
set_option autoImplicit false
set_option maxHeartbeats 85000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Trees Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten
open Layout Fren
open TableF Lenten.Bank Lenten Lenten.Layout Fren
-- detector at chart.Height.Board. aggregate.
variable {N:Side}{P:BudgetPoint}{o:Seat N}{E:InkD N}{X:Scree.Hub N}{M:Tulip.Male}{h t a v x k b d:ℝ}{r l L n:ℕ}(F:Waves)
omit F
-- Ol.CPM.W science
-- mask poly depends on x.Calendars
variable (p:PressB P X E h b)(q:0≤h) (θ: P.threshold=temp x)
include p q θ
local notation "Xo"=> OratorX N P (lagE X) E x (X.val.1)
lemma meter_G (y:tangD N): let L:=Manor P X.val.1 X.val.2 (radiusB x); Xo (L y)= (E (increment 1 y)).val:=by
 intro L; apply congrArg Subtype.val; refine p.term _ _ fun j v k=>?_ ; unfold Vmove; rw [show temp x • lineP P X.val.1 (lagE X).val (radiusB x) (L y) = highlight X.val.2 y from θ ▸ reprV P _ _ (radiusB x) X.property y]; exact congrArg (fun x=>SU.group.lieExp x* (1:Pane N) j) (highlight_A X.val.2 y _ v k).symm
lemma K_Post (k:ℕ)(V:BookTarget)(y:HeadX k Xo P X.val.1 X.val.2 M h (radiusB x) V a)(xq:Charter N Xo) : CostOle (Shorten k (winJ X.val.1 M h (orbitPH (E 1)))- V.S) ≤ a ∧ (1 ≤ k → ∀ i j:Gem,‖i‖≤1/50→‖j‖≤1/50→‖fave P X.val.1 E i j-V.v (hem i (AnalyticBridge.VerifiedReset.spike SU.group)) (hem j (AnalyticBridge.VerifiedReset.spike SU.group))‖≤a) ∧ (2≤ k → (∀ i:Gem,∀ j:Sut, ‖i‖≤1/50→‖j‖≤1/50→‖claw P X.val.1 E i j-V.l (hem i (AnalyticBridge.VerifiedReset.spike SU.group)) (loomH j (AnalyticBridge.VerifiedReset.spike SU.group))‖ ≤a)∧ ∀ i: ComG,‖i‖≤1/50→ ‖landA M X.val.1 E P h i - V.p i‖ ≤ a):=by
 let K:= Xo; let o:= X.val.1; let R:=radiusB x; let T:=Manor P o X.val.2 R; let E':=fun i:tangD N=> E (increment 1 i)
 let z:= AnalyticBridge.VerifiedReset.spike SU.group
 have hx: ∀ i,K (T i)=(E' i).val:=meter_G p q θ
 constructor
 · have he:= y.1
   have hp:orbitPH (E 1)= siphon K 0:=by
      ext i j; change Prism.portB _ _ _= Prism.portB _ _ _; have hp : K 0=(E 1).val:=by simpa only [map_zero,E',Work.G07.at_zero_increment] using hx 0
      rw [hp]
   rw [hp]; exact he
 have hz : captain K ∅ ∘ T=term E :=funext fun i=> congrArg (fun x=>crumb x ∅) (hx _)
 have hK(i j:tangD N): ploy E i j= iteratedFDeriv ℝ 2 (captain K ∅) 0 ![T i,T j]:=by
    rw [ploy_iter,←hz, Next.Foundations.jets_linear T ((xq _).of_le (by decide)), ContinuousMultilinearMap.compContinuousLinearMap_apply]; congr 1; ext1 j; fin_cases j <;> rfl
 have ht:‖z‖=1:=AnalyticBridge.VerifiedReset.spike_norm Thera.yet_one
 have hU(i:Gem): ‖hem i z‖ ≤ ‖i‖:=by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).2; intro j; apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).2; intro k; change ‖i.val j k • z‖≤_; rw [norm_smul,ht,mul_one]; exact (norm_le_pi_norm (i.val j) _).trans (norm_le_pi_norm i.val j)
 constructor
 · intro u i j v w
   change ‖ploy E (gateC o _ _) (gateC o _ _)- _‖ ≤ _; rw [hK]; exact y.2.1 u _ _ ((hU _).trans v) ((hU _).trans w)
 intro u; constructor
 · intro i j v w; have hX(i:Sut): ‖loomH i z‖ ≤ ‖i‖:=by
       apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).2; intro j; apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).2; intro l; apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).2; intro k; change ‖i.val j l k • z‖≤_; rw [norm_smul,ht,mul_one]; exact (norm_le_pi_norm (i.val j l) _).trans ((norm_le_pi_norm (i.val j) _).trans (norm_le_pi_norm i.val _))
   change ‖ploy E (gateC o _ _) (gateT o _ _)-_‖≤_; rw [hK]; exact ((y.2.2 u _ ((hU _).trans v)).1 _ ((hX _).trans w))
 intro i v; have hp:= (y.2.2 u i v).2
 -- can control congr
 let J:=gateC o P.threshold i
 have he(t:tangD N): siphon K (T t)= orbitPH (E' t):=by ext i j; change winsock i j (K _) = winsock i j _; rw [hx]
 have hw: fderiv ℝ (siphon K) 0 (T J)=Paint E J:=by
    have hx:(siphon K∘T)=fun i=>orbitPH (E' i):=funext he
    have hp: HasDerivAt (fun t:ℝ=>siphon K (T (t • J))) (Paint E J) 0:=by
       simp_rw [he]; exact painted p J
    have hy : HasDerivAt (fun t:ℝ=>siphon K (T (t • J))) (fderiv ℝ (siphon K) 0 (T J)) 0:=by
       simp_rw [map_smul]; exact Push.side _ (siphon_C K xq |>.differentiableAt (by norm_num)) _ -- tune
    exact hy.unique hp
 rw [show SiphonT X.val.1 P X.val.2 (radiusB x) (OratorX N P (lagE X) E x (X.val.1)) M h i=landA M o E P h i from congrArg (αxp M o h) hw] at hp; exact hp
end
end YM.CF.Oath
end
