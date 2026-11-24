import Gingham.Linen.Tatting
import Gingham.Linen.Ogive
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Ione


open Swell Incidence Trees
variable {n:Side}
variable {p:BudgetPoint} {a b c d q:ℝ}

abbrev brighten (p:BudgetPoint):ℝ:=p.supportExponent+10/p.B
abbrev anchorH (i: Scree.Hub n): Skye.Seat n:=i.val.1
abbrev holdH (i:Scree.Hub n): Support (Cube.More n):=i.val.2
abbrev Groat (n:Side):= Scree.Hub n→ℝ
def mixB (p:BudgetPoint)(v w:Groat n):Groat n:= fun i=> if sizeB p i ≤p.B then v i else w i

def bird (f:ℕ→ℝ) (b:ℕ):ℝ:=Real.exp 10*((νlot b b:ℝ)*2)+Incidence.feeU b 1*f b
lemma poly_bird {f:ℕ→ℝ} (p:PolyBill f): PolyBill (bird f):=by
 have t: PolyBill fun b=> (νlot b b:ℝ):=by
   simp only [νlot, Nat.cast_mul, Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
   exact (((PolyBill.const (by norm_num:(0:ℝ) ≤ 16)).mul
      (PolyBill.mid.plus (PolyBill.const zero_le_one))).expN 4).mul ((PolyBill.mid.plus (PolyBill.const zero_le_one)).expN 4)


 have w: PolyBill fun b=> Incidence.feeU b 1:= by
   simp only [Incidence.feeU,Nat.cast_one,mul_one]
   exact (((PolyBill.const (by norm_num:(0:ℝ) ≤ 16)).mul
      (PolyBill.mid.plus (PolyBill.const zero_le_one))).expN 4).mul (PolyBill.const Incidence.κRepoH)
 exact ((PolyBill.const (Real.exp_pos _).le).mul (t.mul (PolyBill.const (by norm_num:(0:ℝ) ≤2)))).plus (w.mul p)

/-- mass premium when cover bounded -/
lemma warm_egg (k:ℕ)(h:k≤p.B):
 Real.exp (brighten p*k) ≤Real.exp 10 * Real.exp (p.supportExponent*k):=by
 rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
 rw [add_comm (10:ℝ), brighten, add_mul]
 refine add_le_add le_rfl ?_
 rw [div_mul_eq_mul_div]
 exact (div_le_iff₀ (Nat.cast_pos.mpr p.B_pos)).mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (by norm_num))

/-- mass discount when cover large -/
lemma cool_egg (g:40 ≤p.B)(k:ℕ)(h:p.B<k):
 Real.exp (brighten p*k) ≤Real.exp (-1/4*(p.B:ℝ)) * Real.exp ((p.supportExponent+1/2)*k):=by
 rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
 have t:(10:ℝ)/(p.B:ℝ) ≤ 1/4 := (div_le_iff₀ (Nat.cast_pos.mpr p.B_pos)).mpr (by linarith [show (40:ℝ) ≤p.B by exact_mod_cast g])
 unfold brighten
 nlinarith [show (p.B:ℝ) < k by exact_mod_cast h,Nat.cast_nonneg (α:=ℝ) k]


lemma ruffle {v w:Groat n} (u:40 ≤p.B) (f:ℕ→ℝ) (hf:0 ≤ f p.B) (deficit: Real.exp (-1/4*(p.B:ℝ))≤q)
 (vp:0 ≤v) (wv:0 ≤w)
 (vmatch:∀ z, χbank p p.supportExponent z anchorH holdH v≤2*q)
 (wmatch:∀ z, χbank p p.raisin.supportExponent z anchorH holdH w≤f p.B)
 (y:Seat n) :
 Λpay p.B (brighten p) y holdH (mixB p v w) ≤ bird f p.B*q:=by
 have hq:0 ≤q:= (Real.exp_pos _).le.trans deficit
 let S:=univ.filter fun i:Scree.Hub n=> y∈holdH i
 let H:=S.filter fun i=>sizeB p i≤p.B
 let z: Support (Cube.More n)→ℝ:= currency p.B (brighten p)
 have small:
   (∑ i∈H,z (holdH i)*mixB p v w i) ≤ Real.exp 10*((νlot p.B p.B:ℝ)*(2*q)):=by
   apply le_trans _ (mul_le_mul_of_nonneg_left (Incidence.townSmall anchorH holdH v (mul_nonneg (by norm_num) hq) vp (fun i=>i.property) y _ vmatch) (Real.exp_pos _).le)
   rw [mul_sum,←filter_filter]; apply sum_le_sum (s:=H); intro i t
   rw [mixB, if_pos (mem_filter.mp t).2,←mul_assoc]
   exact mul_le_mul_of_nonneg_right (warm_egg _ (mem_filter.mp t).2) (vp i)


 have wy:∀ z,χbank p (p.supportExponent+1/2+1/2) z anchorH holdH w≤ f p.B:=by
    rw [add_assoc,add_halves]; exact wmatch
 have big:
   (∑ i∈S \ H,z (holdH i)*mixB p v w i) ≤ q*(Incidence.feeU p.B 1*f p.B):=by
   apply le_trans _ (mul_le_mul_of_nonneg_left (Incidence.town_U anchorH holdH w hf wv (fun i=>i.property) y _ wy) hq)
   rw [Λpay,mul_sum]
   apply le_trans _ (sum_le_sum_of_subset_of_nonneg sdiff_subset (s:=S \ H)
      (fun i _ _=>mul_nonneg hq (mul_nonneg (Real.exp_pos _).le (wv i))))
   apply sum_le_sum; intro i t
   have h : p.B < sizeB p i:=lt_of_not_ge (fun r=>(mem_sdiff.mp t).2 (mem_filter.mpr ⟨(mem_sdiff.mp t).1,r⟩))
   rw [mixB, if_neg (not_le.mpr h),←mul_assoc]
   exact mul_le_mul_of_nonneg_right ((cool_egg u _ h).trans (mul_le_mul_of_nonneg_right deficit (Real.exp_pos _).le)) (wv i)
 have hs:H⊆S:=filter_subset ..
 change (∑ i∈S,z (holdH i) *mixB p v w i) ≤ _
 rw [←sum_sdiff hs]
 apply (add_le_add big small).trans_eq
 rw [bird]; ring

