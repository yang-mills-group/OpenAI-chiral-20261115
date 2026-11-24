import Rods.Stage
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
variable {NC Np:Side}(x:Ratio NC Np)(Xs:StepData (More NC) (More Np))(b:ℕ) (c:Op SU.Slot)(T:Male)(t:Odd x.count.val)(q:Chi)(r β:ℝ)(l:Scree.Loom NC)
local notation "psM"=>pushMark x Xs b c T t q r β l
-- Mark is real-scalar link only. Propagates without small or large sector costs. actual branches, uniform. extends scalar ℂ
structure SoloC (A:Mark NC)(w:ℝ):Prop where
 store:∃ f:Pane NC→ℝ,(∀ z,A z=((f z.1:ℝ):ℂ) • (1:FC (Single NC))) ∧(∀ z, |f z|≤ w)
section
variable {M:Mark NC}{wA:ℝ}(hr: Xs.patch.Branches Xs.kernel SU.group)(g:SoloC M wA)
include hr g
lemma upgrades: SoloC (psM M) wA:=by
 obtain ⟨⟨f,fe,fh⟩⟩:=g
 letI: Nonempty (Forest (ratio x)):=Tree.select (ratio x) t
 let D:= gathered x b c T t q r M
 have hg (V:Fields Np)(i:Fields NC):D V i=((f i.1:ℝ):ℂ) • (1:FC (Single Np)):=by
    unfold D gathered avgF before
    simp_rw [fe, map_smul,sub_one,sum_const,card_univ,← Nat.cast_smul_eq_nsmul (R:=ℝ)]
    simp [inv_smul_smul₀ (show (Fintype.card (Forest (ratio x)):ℝ) ≠0 by positivity)]
 let g := assembled x b c T t q r l M
 have ht(V:Fields Np)(a:Pane NC):g V a = (f a:ℝ) • (1:FC (Single Np)):=by -- cast RHS real rewrite using algebra scalar compat
    change (∫ u , D V (a,l (a,u)) ∂depot NC) = _
    simp_rw [hg]; simp
 let U(v:Pane Np)(p:Pane NC):=Xs.density β v p
 let G(v:Pane Np):= ∫ p:Pane NC,U v p * f p ∂prior SU.group (More NC)
 refine ⟨G,fun z=>?_ ,fun y=>?_⟩
 · change linkLaw Xs β (g z) z.1=_; unfold linkLaw; simp_rw [ht,smul_smul,integral_smul_const]; exact (Complex.coe_smul ..).symm
 let Vv:= prior SU.group (More NC)
 rw [← Real.norm_eq_abs]; unfold G U; refine (norm_integral_le_of_norm_le ((Xs.density_integrable β y).mul_const wA) ?_).trans ?_
 · apply Filter.Eventually.of_forall; intro z; rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Xs.density_positive β y z)]; exact mul_le_mul_of_nonneg_left (fh z) (Xs.density_positive ..)
 rw [integral_mul_const,(Xs.isKernel hr β).total]; simp
#check Complex.coe_smul
end
end Decaf
end YM.CF.Py.Rate
end
