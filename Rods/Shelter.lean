import Rods.Press
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
variable(j r p:ℕ){G:Calibration}{m:Side}(u₁: U=G.ℓ)(hf:f≤ j)(hr:j≤r)(hv:r≤ v)(hp:22≤ p)(C D₁:ℕ→ℝ)(he:Scree.mid (A.side j) B=G.c m)
local notation "tK"=> sportT A h j r p u₁ J S h hf hr hv u₁ hp C D₁ he
local notation "Σs" k:max=>mid (A.side k) B
variable (l:List (Tix A j))
include J
-- norm & envelope. Exact all words.
lemma born_b {j r:ℕ}(s:f≤ r)(vQ:r≤ v) (w:∀ i,j≤ i → i<v→Niche R.L (C i) 0)(y:|revenue R.L C D₁ r j-1|≤1/4)(z:j≤r)(b:Tix A j):
    RG.Envelope (pose2 A j r b v φ C D₁) ∧∀ x,‖pose2 A j r b v φ C D₁ x‖≤ steamPrice R.L j r v (A.gram v).p (A.gram r).p (A.money v) (A.money r):=by
 refine ⟨?_ ,hot_upper A J j r C D₁ z s vQ w y b⟩
 let Y:=Keeping.blaze V A φ r v
 have hu(u:Site (mid (A.side r) B)): benign (Y (cameo u (A.gram r).p (A.money r))):= blaze_at V A J r v s vQ le_rfl _ ((cameo_C ..).mono (subset_univ _))
 unfold pose2 playto; dsimp only; have he(j:Site (mid (A.side v) B)):benign (cameo j (A.gram v).p (A.money v)):= (cameo_C ..).mono (subset_univ _); exact (((he _).smulM _).addM ((hu _).smulM _)).env
include S h hf hr hv hp u₁
lemma shelter(w:∀ i,j≤ i → i<v→Niche R.L (C i) 0)(y:|revenue R.L C D₁ r j-1|≤1/4) :RG.Envelope (Sport.film tK l) ∧∀ x:Fields _,‖Sport.film tK l x‖≤Real.exp (steamPrice R.L j r v (A.gram v).p (A.gram r).p (A.money v) (A.money r)*l.length) :=by
 let eP:= steamPrice R.L j r v (A.gram v).p (A.gram r).p (A.money v) (A.money r)
 let K:=tK
 induction l with
 | nil=> refine ⟨(AtSupport.oneM (univ:Support (More (Σs v)))).env,?_⟩ -- film nil
         intro x; simp only [Sport.film,List.map_nil,List.prod_nil,Pi.one_apply,List.length_nil,Nat.cast_zero,mul_zero, Real.exp_zero]; exact le_of_eq norm_one
 | cons i l ih=>
   let f:=Sport.pose K i; let g:=Sport.film K l
   change RG.Envelope (f*g)∧∀ x,‖f x*g x‖ ≤ _
   obtain ⟨k,g0⟩:=born_b A J C D₁ (hf.trans hr) hv w y hr i
   refine ⟨env_mult k ih.1, fun x=>?_⟩
   apply (norm_mul_le ..).trans
   have a : (‖f x‖:ℝ)≤eP:=g0 x
   have b : eP ≤ Real.exp eP := le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp eP)
   apply le_trans (mul_le_mul (a.trans b) (ih.2 x) (norm_nonneg _) (Real.exp_pos _).le)
   change Real.exp eP * Real.exp (eP* (l.length:ℝ)) ≤ Real.exp (eP*((i::l).length:ℝ)); rw [← Real.exp_add,List.length_cons]; push_cast; rw [mul_add,mul_one,add_comm]
#check hot_upper
#check Env.scale
#check env_mult
#check blaze_at
#print axioms shelter
end Decaf
end YM.CF.Py.Rate
end
