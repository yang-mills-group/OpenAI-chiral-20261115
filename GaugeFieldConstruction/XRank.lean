import GaugeFieldConstruction.Certification
import GaugeFieldConstruction.X5Reps
/-!
# Certificate for U1-x. Pivot columns ordered as in RankSupplement. Complex rank.
-/
namespace YM.GaugeFieldConstruction.U1.xRanks
set_option autoImplicit false
set_option synthInstance.maxSize 4000
open Raw Vouchers Cauchy Row Camera Stub Certificate Record

-- Names for writing out the dual functionals used in the pivot proofs
def gg (b : Nat) (a : S3) (i j k : Nat) (h : a=2 → k=0 := by decide) : GIndex := (decide (b=1),⟨(a,i,j,k),h⟩)
-- 1-indexed pivots: [1]
def wMatP := [true]
private def wMatCheck : List (Stub (Axis × Row.x)) := [success [((0,(((0,0,0,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)]]
def wMatBills : List ((Axis) → Bill Row.x) := x5W.map (inspect x5Act Raw.v xCost)
noncomputable def wMat : List ((Axis) → J Row.x) := x5W.map (Record.column Raw.v x5Act evalX)
lemma wMatSure : Certified recX Raw.v wMatBills wMat := endorses _ _ x5W_ok _ readingX mixed

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma wMat_checked : verify [] ((wMatBills.map (bundleCost wTest)).map Bill.norm) wMatP wMatCheck=true := by decide +kernel

theorem wMat_verified : Scan0 wMat wMatP := wMatSure.accepted _ (by decide) wTest_ok _ _ wMat_checked
-- 1-indexed pivots: [1, 2, 3, 4, 5, 6]
def vMatP := [true,true,true,true,true,true]
private def vMatCheck : List (Stub (VS × Row.x)) := [success [(((0,(S 0 1)),(((0,0,0,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)],
  success [(((0,(S 1 1)),(((0,0,0,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)],
  success [(((0,(S 0 0)),(((0,0,0,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)],
  success [(((0,(S 1 1)),(((0,0,0,0),(0,0,0,0)),(gg 1 1 0 0 0))),1)],
  success [(((0,(S 0 1)),(((0,0,0,0),(0,0,0,0)),(gg 1 0 0 0 0))),1)],
  success [(((0,(S 1 2)),(((0,0,0,0),(1,0,0,0)),(gg 1 1 0 0 0))),1)]]
def vMatBills : List ((VS) → Bill Row.x) := x5V.map (inspect x5Act vsAct xCost)
noncomputable def vMat : List ((VS) → J Row.x) := x5V.map (Record.column vsAct x5Act evalX)
lemma vMatSure : Certified recX vsAct vMatBills vMat := endorses _ _ x5V_ok _ readingX mixed

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma vMat_checked : verify [] ((vMatBills.map (bundleCost vTest)).map Bill.norm) vMatP vMatCheck=true := by decide +kernel

theorem vMat_verified : Scan0 vMat vMatP := vMatSure.accepted _ (by decide) vTest_ok _ _ vMat_checked
-- 1-indexed pivots: [1, 2, 3, 4, 5, 6, 7]
def ranksP := [true,true,true,true,true,true,true]
private def ranksCheck : List (Stub ((Axis × Axis) × Row.x)) := [success [(((0,1),(((0,1,0,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)],
  success [(((0,0),(((0,0,1,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)],
  success [(((0,1),(((0,0,1,0),(1,0,0,0)),(gg 1 2 0 0 0))),1)],
  success [(((0,0),(((0,1,0,0),(0,0,0,0)),(gg 1 1 0 0 0))),1),(((0,0),(((0,0,1,0),(1,0,0,0)),(gg 1 2 0 0 0))),1),(((0,1),(((0,1,0,0),(1,0,0,0)),(gg 1 2 0 0 0))),⟨-1,0⟩)],
  success [(((0,1),(((0,0,1,0),(0,0,0,0)),(gg 1 1 0 0 0))),1)],
  success [(((0,0),(((0,0,0,1),(1,0,0,0)),(gg 1 0 0 0 0))),1)],
  success [(((0,1),(((0,0,0,1),(1,0,0,0)),(gg 1 1 0 0 0))),1)]]
def ranksBills : List ((Axis × Axis) → Bill Row.x) := 
  (pick wMatP wMatBills).map (gradTest dx) ++ (pick vMatP vMatBills).map (vecTest dx)
noncomputable def ranks : List ((Axis × Axis) → J Row.x) := 
  (pick wMatP wMat).map (recX.heatP Axis) ++ (pick vMatP vMat).map recX.divA
lemma ranksSure : Certified recX (Raw.v.tensorProd Raw.v) ranksBills ranks := Certified.combines
  ((wMatSure.keep _).scope _ _ (fun i=>funext (fun x=> grad_cost _ dx dx_c _ _ (fun _=>rfl) x)) (recX.chargeP Raw.v))
  ((vMatSure.keep _).scope _ _ (fun i=>funext (fun x=> vec_cost _ dx dx_c _ _ (fun _=>rfl) x)) recX.paid_A)

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma ranks_checked : verify [] ((ranksBills.map (bundleCost vvTest)).map Bill.norm) ranksP ranksCheck=true := by decide +kernel

theorem ranks_verified : Scan0 ranks ranksP := ranksSure.accepted _ (by decide) vvTest_ok _ _ ranks_checked
end YM.GaugeFieldConstruction.U1.xRanks
