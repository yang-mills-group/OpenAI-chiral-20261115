import Compass.Arrays
import Compass.Hall
import Compass.Prime
import Compass.Starglass
import Compass.Spokes
import Compass.Poetry
import Compass.Reynolds
import Compass.Bullion
import YM.CF.Neon.Ten
import Compass.Hubs
import YM.CF.Ione.Jost
import Compass.Lode
import YM.CF.Brood.Tips
import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
import Compass.Jazz
import Compass.Needle
import Compass.Sloop
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
variable {Nq:Side}
open Ione
open scoped Mew
local notation "Ck"=> carriers Nq
open Neon
variable {Nq:Side}(o:Site Nq)
lemma offsetGone (r:ℂ)(j:Site Nq):pad o r castPay j=0:=by
 let a:Signed:= (Signed.mirror 0) * Pec.X side01; let f:=pad o r castPay
 have h:detX a=false:=by unfold a; rw [det_p,det_t,detSwap _ _ (by decide:(0:Axis)≠1)]; rfl
 obtain ⟨v,q,z,k⟩:=stabilizes j a (Anchored.prod (allFlips _ rfl) quad_anchor) false
 have ht:= pool o r j v; rw [k,wage_t,taxK,taxF,taxB,q,taxes,tax_m,show tariffX (Pec.X side01)=true from tax_s 0 1 (by decide)] at ht
 have hv:wageZ v.val⁻¹=false:=by change (v.val.charge).xor (detX v.val.s⁻¹)=_; rw [z,det_inv,q,h]; rfl
 unfold Spire.payZ at ht; rw [hv] at ht; change f j=(-1:ℝ) • f j at ht; rw [neg_one_smul] at ht
 suffices f j+f j=0 by
    have h:= congrArg Complex.re this; have g:=congrArg Complex.im this; apply Complex.ext
    · change (f j).re=0; simp only [Complex.add_re,Complex.zero_re] at h; linarith
    change (f j).im=0; simp only [Complex.add_im,Complex.zero_im] at g; linarith
 exact eq_neg_iff_add_eq_zero.mp ht
-- actual monetary shape. common independent of position and real. Pank.Ar. need y:=re of o etc.
lemma h_allow (r:staff Nq)(S:ArcΦ)(p:ℂ)(τ:p.im=0) (B1:ℝ)(e:‖S.1-paintS p‖ ≤ B1): ‖(tiltA r.val S).1-taxK r • paintS p‖≤ B1:=by
 have hB:= (norm_nonneg _).trans e
 refine (pi_norm_le_iff_of_nonneg hB).mpr fun i=>(pi_norm_le_iff_of_nonneg hB).mpr fun j=>?_
 let s:=r.val.s; let b:=r.val.charge
 obtain ⟨a,rfl⟩:= (Lattice.PlaqAxes.transform s).surjective i; obtain ⟨c,rfl⟩:=(Lattice.PlaqAxes.transform s).surjective j
 have hp:p=(p.re:ℂ):=Complex.ext rfl τ
 have hf:=prime_C p.re s b r.property a c; rw [←hp] at hf -- ambiguities, tax_spec private
 let s':= StressFlux.sign
 let V:= AnalyticBridge.VerifiedReset.dirS s a* AnalyticBridge.VerifiedReset.dirS s c
 change ‖(AnalyticBridge.VerifiedReset.dirS s _ * AnalyticBridge.VerifiedReset.dirS s _) • Spire.payZ r.val⁻¹ (S.1 (Lattice.PlaqAxes.rotate _ (Lattice.PlaqAxes.rotate _ a)) (Lattice.PlaqAxes.rotate _ (Lattice.PlaqAxes.rotate _ c))) - taxK r • paintS p (Lattice.PlaqAxes.rotate s a) (Lattice.PlaqAxes.rotate s c)‖≤_
 simp only [Lattice.PlaqAxes.transform,Lattice.PlaqAxes.rotate_inv, Equiv.coe_fn_mk]
 change taxK r • paintS p _ _= _ at hf; rw [hf]
 have hz:wageZ r.val⁻¹=SkateGlyph s b:=by change b.xor (detX r.val.s⁻¹)=_; rw [det_inv]; rfl
 unfold Spire.payZ; rw [hz, show (r.val.s)=s from rfl,Lattice.PlaqAxes.rotate_inv,Lattice.PlaqAxes.rotate_inv,← smul_sub]; change ‖V • _‖≤_
 have hW(Q:Bool)(t w:ℂ): ‖cSignX Q t-cSignX Q w‖=‖t-w‖:=by cases Q; rfl; change ‖star t -star w‖= _; rw [←star_sub]; exact norm_star _
 rw [norm_smul, hW,show ‖V‖=1 from (by unfold V AnalyticBridge.VerifiedReset.dirS StressFlux.sign; split_ifs<;>norm_num),one_mul]
 exact (norm_le_pi_norm ((S.1-paintS p) a) _ |>.trans (norm_le_pi_norm _ a)).trans e
lemma approveAcc(z:Site Nq)(S:ArcΦ)(p:ℂ)(hp:p.im=0)(B1:ℝ)(e: ‖S.1-paintS p‖≤B1): ‖(approve S o z).1-paintS p‖≤B1:=by
 let A:=frames orbitT o z; let T (r:staff Nq):=tiltA r.val S; let Z:= fun _ : Site Nq=>paintS p
 change ‖(∑ r∈A,taxN o z r • T r).1-Z z‖≤_
 have hs(W:staff Nq→ArcΦ): (∑ r∈A,W r).1=∑ r∈A,(W r).1 := by exact (Prod.fst_sum ..) -- find
 have ht:Z z=∑ r∈A,taxN o z r • taxK r • Z z:=(union_frames o z Z _ (fun _ _=>rfl)).symm
 rw [hs]; rw [ht] -- nth maybe denominator occurrence? 
 rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; apply le_trans (sum_le_sum (g:=fun r=> |taxN o z r| *B1) ?_); swap
 · intro j _; change ‖_ • (T j).1-(taxN o z j) • (taxK j • Z z)‖≤_; rw [←smul_sub,norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (h_allow j S p hp B1 e) (abs_nonneg _)
 exact le_of_eq (by rw [←sum_mul,sumshares,one_mul])
#check pool
end YM.CF.Compass
