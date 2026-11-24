import Rods.Folder
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
open Lifted Pannier.Chancel
variable (j r p:ℕ){G:Calibration}(uA:f ≤ j)(uQ:j ≤ r)(uE:r ≤ v)
-- equivalent Calibration side.W. Build generic Sport requiring equality $q$. avoid cast bookkeeping via helper.
private def conveys {m a n:Side}{X:Type}(e:a=G.c m)(F:X → Support (More a))(g:X→Mark n)(u:Axis→ℤ→X→X)(x:Axis→ℤ→ℤ)
 (s:∀ i z o,F o ⊆ band a i (Heat.gaugeShift G.B z) G.ℓ→AtSupport false (band n i (Heat.gaugeShift G.B (x i z)) G.ℓ) (g o))
 (k:∀ i z o,F o ⊆ band a i (Heat.gaugeShift G.B z) G.ℓ → g (u i z o)= reflMark i (Heat.gaugeShift G.B (x i z)) (g o))
 (w:∀ i z o,F (u i z o)= (F o).image ((plane i (Heat.gaugeShift G.B z)).anon a)) : Sport G m n X where
 place o:= (e ▸ F o)
 pose:=g
 mirror:=u
 castM:=x
 stage i z:=by subst a; exact s i z
 charge i z:=by subst a; exact k i z
 town i z:=by subst a; exact w i z
-- ↑ commute lift. coal
#check coal_halo
#check pose2
variable {m:Side}(e:Scree.mid (A.side j) B = G.c m)(hx: U=G.ℓ)(hp:22≤ p)(C D₁:ℕ→ℝ)
abbrev tote (q:Tix A j) := sitepad q.1 p
abbrev turn(Gx:Calibration)(j:ℕ)(a:Axis)(s:ℤ)(q:Tix A j):Tix A j:=(center _ a (Heat.gaugeShift Gx.B s) q.1,q.2) -- G implicit binder term only -> explicit

def sportT (J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Buffered.Margin R.L D0 D Q U)(uA:f ≤ j)(uQ:j ≤ r)(uE:r ≤ v)(hx: U=G.ℓ)(hp:22 ≤ p)(C D₁:ℕ→ℝ)(e:Scree.mid (A.side j) B = G.c m): Sport G m (Scree.mid (A.side v) B) (Tix A j):=
   conveys (e:=e) (tote A j p) (fun x:Tix A j=>pose2 A j r x v φ C D₁) (turn A G j) (fun _ z=> (R.L.val:ℤ)^(v-j)*z)
   (by
     intro i z o ht; subst U
     let s:= Heat.gaugeShift G.B z
     have hk:(R.L.val:ℤ)^(v-j)*s= _:=show _= Heat.gaugeShift G.B ((R.L.val:ℤ)^(v-j)*z) from (by unfold s Heat.gaugeShift;ring)
     have h':= (folded2 A J S h j r o i s C D₁ uA uQ uE ((Corona.halo_mono hp le_rfl).trans ht)).1
     rw [hk] at h'; exact h')
   (by
     intro i z o ht; subst U
     let s:= Heat.gaugeShift G.B z
     have hk:(R.L.val:ℤ)^(v-j)*s= _:= show _=Heat.gaugeShift G.B ((R.L.val:ℤ)^(v-j)*z) from (by unfold s Heat.gaugeShift; ring)
     have h':= (folded2 A J S h j r o i s C D₁ uA uQ uE ((Corona.halo_mono hp le_rfl).trans ht)).2
     rw [hk] at h'; exact h')
   (by
     intro i z o
     change Lattice.halo p {node (center _ i (Heat.gaugeShift G.B z) _)} = (Lattice.halo p {node _}).image _
     rw [placing, (show ( Finset.image _ _: Support (More (Scree.mid (A.side j) B)))=(Lattice.halo ..) from coal_halo ..) , hyphen, image_singleton] -- may need open names
     )
#check sportT
#print axioms sportT
end Decaf
end YM.CF.Py.Rate
end
