import GaugeFieldConstruction.Noce
import GaugeFieldConstruction.Riant
set_option autoImplicit false
set_option maxHeartbeats 400000
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
open Py Trees Hake FlightFlux TableF Boom Axon Lenten.ModuleB Flot Taxi
open HarmP
namespace BellPrice
open Lenten FlightFlux Fluxim
open Planned.PrimaryIntegral295 Carrier
structure Humble (L:Side) (p s:ℝ)(x:ℝ):Prop where
 pull:∀ (N P B:Side)(S:StepData (Domain N B) (Domain P B))(T: Tube SU.group S)(X:GramM (mid N B))(Y:GramM (mid P B)), S.patch.L=L→ radiusB x ≤(Domain N B).val → X.p.power=3 → X.p.threshold=temp x→ X.p.threshold ≤ 2*Y.p.threshold →∀ F:Flight 4 4, F.L=S.ratio.count→ HEq (linesOf F p) T.R.A0 → ∃ σ C:ℝ,∃ m:ℕ, Gatehouse X Y σ C x m T ∧ leadDue (s/2) σ C X.p Y.p S.ratio.count m ≤ s
lemma humbled (L:Side)(p s:ℝ)(u:0<p)(v:0<s): ∀ᶠ x in atTop,Humble L p s x:=by
 obtain ⟨σ,C,h,h',g⟩:=priced p u (show 4 ≤4 by omega) (show 4≤4 by omega)
 let W:= C/(L.val:ℝ); have hw:0<W:=by unfold W; positivity
 let D:=4*W*(1+(nodalK L:ℝ))^3*Real.exp (σ/2*(nodalK L:ℝ))*widthCost (σ/2) 3
 have hx:0 ≤ D:=by unfold D; have hp:1 ≤widthCost (σ/2) 3:= widthCost_ge (half_pos h) _; positivity
 let b(m:ℕ):= Real.exp (-(σ/2)*m)*D; have he:Tendsto b atTop (𝓝 0):=by
    simpa only [b,zero_mul,Function.comp_apply] using (Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop (R:=ℝ) |>.const_mul_atTop_of_neg (show -(σ/2)< 0 from (by linarith)))).mul_const D
 obtain ⟨m,i⟩:= (he.eventually (ge_mem_nhds (show 0<s/8 by positivity))).exists
 have hb:0 ≤ b m:= mul_nonneg (Real.exp_pos _).le hx
 filter_upwards [Work.E01.radiusB_tendsto.eventually_gt_atTop (2*m+100)] with x ht; constructor; intro N P B S T X Y u l w hP hr F f y
 let H(A:Side)(t:A=F.L)(r:Lines A)(v:HEq (linesOf F p) r):r.strip σ (C/(F.L.val:ℝ)):=by subst A; rw [←eq_of_heq v]; simpa only [List.length_nil,Nat.add_zero,pow_one,advanceC] using g F [] (by simp)
 have hl:S.ratio.count=L:=u
 refine ⟨σ,W,m,⟨h,hw.le,?_,w,hP,?_,by omega,by omega⟩,?_⟩ -- direction casting
 · -- t I.W; terms
   rw [show W=C/(F.L.val:ℝ) from (by unfold W; rw [f.trans hl])]; exact H S.ratio.count f.symm T.R.A0 y -- substitution maybe orientation
 · unfold Heir.reach; omega
 unfold leadDue; rw [hl]; change s/2+ 2*X.p.threshold/Y.p.threshold*b m ≤ s
 have hp:0 < Y.p.threshold:=Y.p.threshold_pos; have hs: 2*X.p.threshold/Y.p.threshold ≤4:=by apply (div_le_iff₀ hp).mpr; linarith
 nlinarith only [mul_le_mul_of_nonneg_right hs hb,i]
-- Apricot
end BellPrice
end YM.CF.Oath
end
