import Rods.Propagate
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
local notation "St" j:max=> mid (A.side j) B
variable {I:Type}[LinearOrder I][Fintype I]{j r:ℕ}(i:Axis){s:ℤ}(x:f ≤ j)(p:j≤ r)(t:r≤v)(o:I→Site (mid (A.side j) B))(b:I)
open Stencil
#check stages
include J S h
lemma cargoV(j:ℕ)(i:Axis)(s:ℤ)(x:f≤j)(p:j≤v)(F:Mark (mid (A.side j) B))(g:AtSupport false (band _ i s U) F):
        let k:= (R.L.val:ℤ)^(v-j)*s
        let V':= blaze V A φ j v
        AtSupport false (band _ i k U) (V' F) ∧ V' (reflMark i s F)= reflMark i k (V' F):=by
 by_cases a:j<v; swap; · have e:j=v:=le_antisymm p (Nat.le_of_not_lt a); subst j; intro k V'; simpa [k,V',Keeping.blaze,hop_here] using g
 intro k V'; obtain ⟨e,t⟩:= stages A J S h i x p (Nat.le_refl _) a g
 have u:= cargoV (j+1) i ((R.L.val:ℤ)*s) (x.trans (Nat.le_succ _)) a (φ j F) e
 have hk: k=(R.L.val:ℤ)^(v-(j+1))*((R.L.val:ℤ)*s):=by unfold k; rw [show v-j=(v-(j+1))+1 from (by omega),pow_succ,mul_assoc]
 unfold V' Keeping.blaze; rw [hop_step _ _ _ _ a,hop_step _ _ _ _ a,t,hk]; exact u
termination_by v-j
decreasing_by omega
-- repeated lift fit halo anchor inc. for each H and each example anchor
lemma fits_one(k:Axis)(z:ℤ)(j:ℕ)(o:I→Site (mid (A.side j) B))(b:I)
    (pS:sitepad (o b) 22⊆ band _ k z U): sitepad (adapt V A j o b) 22⊆ band _ k ((R.L.val:ℤ)*z) U:=by
 have he:node (adapt V A j o b)= (ratio (A.ratio j)).embed (node (o b)):=claw (A.ratio j) (J.odd j) (o b)
 have hg:= band_root k z (A.ratio j) (node (o b)) (pS (by rw [sitepad]; exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_self _).le.trans (Nat.zero_le _)⟩))
 have hn:= R.coarse
 have hm:4*(4*(100*R.L.val*(1+D0)+D+Q+10))< U:= h
 rw [S.side] at hg
 intro x u; unfold sitepad at u; rw [he] at u
 apply band_pad k _ (show U+22 ≤R.L.val*U from (le_trans (by omega) (Nat.mul_le_mul_right U hn)))
 exact Corona.halo_mono (le_refl 22) (singleton_subset_iff.mpr hg) u
lemma fitsV(k:Axis)(z:ℤ)(j r:ℕ)(p:j≤r)(o:I→Site (mid (A.side j) B))(b:I)(pS:sitepad (o b) 22⊆ band _ k z U): sitepad (liftCanvas V A j r o b) 22⊆band (mid (A.side r) B) k ((R.L.val:ℤ)^(r-j)*z) U:=by
 by_cases a:j<r; swap; · have e:j=r:=le_antisymm p (Nat.le_of_not_lt a); subst r; simpa [liftCanvas,hop_here]
 unfold liftCanvas; rw [hop_step (h:=a),show (r-j)=(r-(j+1))+1 from (by omega),pow_succ,mul_assoc]; exact fitsV k ((R.L.val:ℤ)*z) (j+1) r a (adapt V A j o) b (fits_one A J S h k z j o b pS)
termination_by r-j
decreasing_by omega
#check fitsV
#print axioms cargoV
end Decaf
end YM.CF.Py.Rate
end
