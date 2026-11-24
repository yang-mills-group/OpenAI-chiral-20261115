import SatinThinThimble
import SatinThinSkyline

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/-! Uniform sample qualification, eventual on the underlying Patch. -/
open Fief
variable (R:Patch){F W V1 K:ℝ→ℝ}(u:BladeQ R F W V1 K)
variable (D E A:ℝ)
local notation "ℓ"=> R.L
include u
lemma attain_step (g:ChoiceCost D E A R.L): ∀ᶠ x:ℝ in atTop,∀ P:BudgetPoint,P.B=radiusB x→ Thimble D E A (allotΨ R.L (x+Vale.billX R.L)) (allotΨ R.L x) (W x) (K x) (F x) R.L P:=by
 let C:= compassκ R.L; have hc:0<C:=zero_lt_one.trans_le (compass_pos ℓ); obtain ⟨v,v',p⟩:=book_ε R.L
 let Tc(x:ℝ):= allotΨ R.L x; have hm: Tendsto Tc atTop (𝓝 0):= ((size_ψ ℓ).low (k:=1) (by omega)).spine
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop ((ℓ).val+10),nut_V _ C (compass_pos ℓ) v 2 _ _ _ _ u,hm.eventually (ge_mem_nhds zero_lt_one),u.mint.spine_a.eventually (ge_mem_nhds (show 0<C⁻¹ from inv_pos.mpr hc)),computed_rc _ R (compass_pos R.L)] with x h H w y m B pB
 let s:=Tc x; let t:=Tc (x+Vale.billX ℓ); let q:=B.B; let e:=PongR ℓ; have hp:s≤2*t:=H.day.2.2; have ht:0<t:=H.day.1; have hs:0<s:=ht.trans_le H.day.2.1
 have eb:s/(compassκ ℓ)=C⁻¹*s:=by unfold C; ring
 refine ⟨ht,H.day.2.1,hp,w,g,H.pays.trans ?_, pB.symm ▸ H.pitch,pB.symm ▸ H.term,pB.symm ▸ m, ?_,?_,?_,?_⟩
 · change e*s ≤ _*t; linarith only [mul_le_mul_of_nonneg_right p ht.le,mul_le_mul_of_nonneg_left hp (show 0≤PongR ℓ from v.le)] -- let e maybe dsimp
 · rw [pB]; exact (le_abs_self _).trans (H.spool.trans (mul_le_of_le_one_left hs.le v'))
 · rw [pB]; exact (le_abs_self _).trans (H.warp.trans (mul_le_of_le_one_left hs.le v'))
 · change K x≤ s/_; rw [eb]; exact (div_le_iff₀ hs).mp y
 rw [←pB] at h; have he:(ℓ).val+1≤ q:= (by dsimp only [q]; omega); have hv:10 ≤ q:=by dsimp only [q]; omega
 unfold cape_B; have hm:= Nat.mul_le_mul_right (4*q+2) he; change ((ℓ).val+1)*(4*q+2)+2*q≤q+q^3; apply le_trans (Nat.add_le_add_right hm _); have hq:10*q^2≤q^3:=by nlinarith
 nlinarith
end YM.CF.QuadClock
