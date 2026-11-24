import GaugeFieldConstruction.Certification
import GaugeFieldConstruction.G5Reps
import GaugeFieldConstruction.G4Reps
/-!
# Certificate for U1-g. Pivot columns ordered as in RankSupplement. Complex rank.
-/
namespace YM.GaugeFieldConstruction.U1.gRanks
set_option autoImplicit false
set_option synthInstance.maxSize 4000
open Raw Vouchers Cauchy Row Camera Stub Certificate Record

-- Names for writing out the dual functionals used in the pivot proofs
def gg (b : Nat) (a : S3) (i j k : Nat) (h : a=2 → k=0 := by decide) : GIndex := (decide (b=1),⟨(a,i,j,k),h⟩)

def unitTest : List Unit := [()]
lemma unitTest_ok : Hits (Labels.unitL Unit) unitTest := fun i=> ⟨i,by simp [unitTest],1,rfl⟩
-- 1-indexed pivots: [1, 2, 3]
def tMatP := [true,true,true]
private def tMatCheck : List (Stub (Raw.Sym × Row.g)) := [success [(((S 0 0),((gg 1 2 0 0 0),(gg 1 2 0 0 0))),1)],
  success [(((S 0 0),((gg 1 0 0 0 0),(gg 1 0 0 0 0))),1)],
  success [(((S 0 1),((gg 1 1 0 0 0),(gg 1 0 0 0 0))),1)]]
def tMatBills : List ((Raw.Sym) → Bill Row.g) := g4T.map (inspect g4Act symAct g4Cost)
noncomputable def tMat : List ((Raw.Sym) → J Row.g) := g4T.map (Record.column symAct g4Act evalTg)
lemma tMatSure : Certified recG symAct tMatBills tMat := endorses _ _ g4T_ok _ readingTg polar4

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma tMat_checked : verify [] ((tMatBills.map (bundleCost sTest)).map Bill.norm) tMatP tMatCheck=true := by decide +kernel

theorem tMat_verified : Scan0 tMat tMatP := tMatSure.accepted _ (by decide) sTest_ok _ _ tMat_checked
-- 1-indexed pivots: [1, 2]
def wMatP := [true,true,false,false]
private def wMatCheck : List (Stub (Axis × Row.g)) := [success [((0,((gg 1 2 0 0 0),(gg 1 2 1 0 0))),1)],
  success [((0,((gg 1 0 0 0 0),(gg 1 0 1 0 0))),1)],
  decline (⟨2,0⟩) [⟨-1,0⟩],
  decline (⟨2,0⟩) [0,1]]
def wMatBills : List ((Axis) → Bill Row.g) := g5W.map (inspect g5Act Raw.v g5Cost)
noncomputable def wMat : List ((Axis) → J Row.g) := g5W.map (Record.column Raw.v g5Act evalG)
lemma wMatSure : Certified recG Raw.v wMatBills wMat := endorses _ _ g5W_ok _ readingG polar5

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma wMat_checked : verify [] ((wMatBills.map (bundleCost wTest)).map Bill.norm) wMatP wMatCheck=true := by decide +kernel

theorem wMat_verified : Scan0 wMat wMatP := wMatSure.accepted _ (by decide) wTest_ok _ _ wMat_checked
-- 1-indexed pivots: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 24, 26, 28, 29, 30]
def vMatP := [true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,false,false,false,false,false,false,false,true,false,true,false,true,true,true,false,false]
private def vMatCheck : List (Stub (VS × Row.g)) := [success [(((0,(S 0 0)),((gg 1 2 0 0 0),(gg 1 2 1 0 0))),1)],
  success [(((0,(S 1 1)),((gg 1 2 0 0 0),(gg 1 2 1 0 0))),1)],
  success [(((0,(S 1 1)),((gg 1 1 0 0 0),(gg 1 1 1 0 0))),1)],
  success [(((0,(S 0 1)),((gg 1 2 0 0 0),(gg 1 2 0 1 0))),1)],
  success [(((0,(S 0 1)),((gg 1 0 0 0 0),(gg 1 0 0 1 0))),1)],
  success [(((0,(S 0 1)),((gg 1 1 0 0 0),(gg 1 1 0 1 0))),1)],
  success [(((0,(S 1 1)),((gg 1 0 0 0 0),(gg 1 0 1 0 0))),1)],
  success [(((0,(S 0 0)),((gg 1 0 0 0 0),(gg 1 0 1 0 0))),1)],
  success [(((0,(S 1 1)),((gg 0 2 0 0 0),(gg 0 2 1 0 0))),1)],
  success [(((0,(S 0 1)),((gg 0 2 0 0 0),(gg 0 2 0 1 0))),1)],
  success [(((0,(S 1 2)),((gg 1 2 0 0 0),(gg 1 1 1 0 0))),1)],
  success [(((0,(S 1 2)),((gg 1 2 0 0 0),(gg 1 0 0 1 0))),1)],
  success [(((0,(S 1 2)),((gg 1 0 0 0 0),(gg 1 2 0 1 0))),1)],
  success [(((0,(S 0 1)),((gg 1 1 0 0 0),(gg 1 0 1 0 0))),1)],
  decline (1) [1,0,0,0,0,0,0,0,⟨-1,0⟩],
  success [(((0,(S 1 1)),((gg 1 0 0 0 0),(gg 1 1 0 1 0))),1)],
  decline (1) [1,0,0,0,0,0,0,0,⟨-1,0⟩],
  decline (⟨2,0⟩) [0,0,0,0,0,0,0,⟨-1,0⟩],
  decline (⟨2,0⟩) [0,0,0,0,0,0,⟨-1,0⟩],
  decline (⟨2,0⟩) [0,0,0,0,0,⟨-1,0⟩],
  decline (⟨2,0⟩) [0,0,0,0,0,0,0,0,0,0,0,1],
  decline (⟨2,0⟩) [0,0,0,0,0,0,0,0,0,0,0,0,0,1],
  decline (⟨2,0⟩) [0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
  success [(((0,(S 1 1)),((gg 1 1 0 0 0),(gg 1 0 0 1 0))),1)],
  decline (1) [1,0,0,0,0,0,0,0,0,0,0,0,0,1],
  success [(((0,(S 0 1)),((gg 1 0 0 0 0),(gg 1 1 1 0 0))),1)],
  decline (1) [1,0,0,0,0,0,0,0,0,0,0,0,1],
  success [(((0,(S 1 2)),((gg 0 0 0 0 0),(gg 0 1 0 0 1))),1)],
  success [(((0,(S 1 2)),((gg 0 1 0 0 0),(gg 0 0 0 0 1))),1)],
  success [(((0,(S 1 2)),((gg 0 1 0 0 0),(gg 0 2 1 0 0))),1)],
  decline (1) [⟨-1,0⟩,1],
  decline (1) [0,0,0,0,0,0,0,0,⟨-1,0⟩,1]]
def vMatBills : List ((VS) → Bill Row.g) := g5V.map (inspect g5Act vsAct g5Cost)
noncomputable def vMat : List ((VS) → J Row.g) := g5V.map (Record.column vsAct g5Act evalG)
lemma vMatSure : Certified recG vsAct vMatBills vMat := endorses _ _ g5V_ok _ readingG polar5

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma vMat_checked : verify [] ((vMatBills.map (bundleCost vTest)).map Bill.norm) vMatP vMatCheck=true := by decide +kernel

theorem vMat_verified : Scan0 vMat vMatP := vMatSure.accepted _ (by decide) vTest_ok _ _ vMat_checked
-- 1-indexed pivots: [1, 2]
def divsP := [true,true,false]
private def divsCheck : List (Stub (Axis × Row.g)) := [success [((0,((gg 1 2 1 0 0),(gg 1 2 0 0 0))),1)],
  success [((0,((gg 1 0 1 0 0),(gg 1 0 0 0 0))),1)],
  decline (⟨2,0⟩) [⟨-1,0⟩,1]]
def divsBills : List ((Axis) → Bill Row.g) := 
  (pick tMatP tMatBills).map (dimTest dg)
noncomputable def divs : List ((Axis) → J Row.g) := 
  (pick tMatP tMat).map recG.divP
lemma divsSure : Certified recG Raw.v divsBills divs := (tMatSure.keep _).scope (dimTest dg) recG.divP (fun i => funext (fun x => dim_cost _ dg dg_c i _ (fun _=>rfl) x)) recG.paid_div

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma divs_checked : verify [] ((divsBills.map (bundleCost wTest)).map Bill.norm) divsP divsCheck=true := by decide +kernel

theorem divs_verified : Scan0 divs divsP := divsSure.accepted _ (by decide) wTest_ok _ _ divs_checked
-- 1-indexed pivots: [1]
def facesP := [true,false,false]
private def facesCheck : List (Stub (Unit × Row.g)) := [success [(((),((gg 1 2 0 0 0),(gg 1 2 0 0 0))),1)],
  decline (1) [⟨-1,0⟩],
  decline (1) []]
def facesBills : List ((Unit) → Bill Row.g) := (pick tMatP tMatBills).map trTest
noncomputable def faces : List ((Unit) → J Row.g) := (pick tMatP tMat).map trace
lemma facesSure : Certified recG (Labels.unitL Unit) facesBills faces := (tMatSure.keep _).scope trTest _ (fun i => funext (fun x => tr_cost _ _ (fun _=>rfl) x)) recG.paid_trace

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma faces_checked : verify [] ((facesBills.map (bundleCost unitTest)).map Bill.norm) facesP facesCheck=true := by decide +kernel

theorem faces_verified : Scan0 faces facesP := facesSure.accepted _ (by decide) unitTest_ok _ _ faces_checked
-- 1-indexed pivots: [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def ranksP := [true,true,true,true,true,true,true,true,false,true,false,true,true,true,true,true,true,true,true,true,true,false]
private def ranksCheck : List (Stub ((Axis × Axis) × Row.g)) := [success [(((0,0),((gg 1 2 1 0 0),(gg 1 2 1 0 0))),1)],
  success [(((0,1),((gg 1 1 1 0 0),(gg 1 1 0 1 0))),1)],
  success [(((0,1),((gg 1 2 1 0 0),(gg 1 2 0 1 0))),⟨2,0⟩),(((0,0),((gg 1 2 1 0 0),(gg 1 2 1 0 0))),⟨-1,0⟩)],
  success [(((0,1),((gg 1 0 1 0 0),(gg 1 0 0 1 0))),1),(((0,1),((gg 1 2 1 0 0),(gg 1 2 0 1 0))),⟨-1,0⟩)],
  success [(((0,0),((gg 1 0 1 0 0),(gg 1 0 1 0 0))),1),(((0,1),((gg 1 1 1 0 0),(gg 1 1 0 1 0))),⟨-2,0⟩)],
  success [(((0,0),((gg 1 2 0 1 0),(gg 1 2 0 1 0))),1)],
  success [(((0,0),((gg 1 0 0 1 0),(gg 1 0 0 1 0))),1)],
  success [(((0,0),((gg 1 1 0 1 0),(gg 1 0 1 0 0))),1)],
  decline (⟨2,0⟩) [0,0,0,0,1,1,0,⟨-1,0⟩],
  success [(((0,1),((gg 0 2 1 0 0),(gg 0 2 0 1 0))),⟨2,0⟩),(((0,0),((gg 1 1 0 1 0),(gg 1 0 1 0 0))),1),(((0,0),((gg 1 0 1 0 0),(gg 1 0 1 0 0))),⟨-1,0⟩)],
  decline (1) [1,0,0,0,⟨2,0⟩,0,0,⟨-1,0⟩],
  success [(((0,0),((gg 0 2 0 1 0),(gg 0 2 0 1 0))),1)],
  success [(((0,1),((gg 1 0 1 0 0),(gg 1 1 1 0 0))),1)],
  success [(((0,1),((gg 1 1 0 1 0),(gg 1 0 0 1 0))),1)],
  success [(((0,1),((gg 1 0 0 0 0),(gg 1 1 0 2 0))),1)],
  success [(((0,0),((gg 0 0 0 0 0),(gg 0 0 2 0 0))),⟨4,0⟩),(((0,0),((gg 1 0 0 1 0),(gg 1 0 0 1 0))),1),(((0,0),((gg 1 2 0 1 0),(gg 1 2 0 1 0))),1),(((0,0),((gg 1 2 1 0 0),(gg 1 2 1 0 0))),⟨-2,0⟩)],
  success [(((0,1),((gg 1 1 0 0 0),(gg 1 0 0 0 2))),1),(((0,1),((gg 1 1 0 1 0),(gg 1 0 0 1 0))),1)],
  success [(((0,1),((gg 1 1 0 0 0),(gg 1 0 0 2 0))),1)],
  success [(((0,1),((gg 1 0 0 0 0),(gg 1 1 2 0 0))),1)],
  success [(((0,1),((gg 0 0 0 0 1),(gg 0 2 0 1 0))),1)],
  success [(((0,1),((gg 1 1 0 0 0),(gg 1 1 1 1 0))),1),(((0,1),((gg 0 0 0 0 1),(gg 0 2 0 1 0))),⟨-1,0⟩),(((0,1),((gg 1 1 1 0 0),(gg 1 1 0 1 0))),⟨-1,0⟩)],
  decline (⟨2,0⟩) [0,0,⟨2,0⟩,0,0,⟨-2,0⟩,0,0,⟨2,0⟩,0,0,⟨2,0⟩,0,0,0,0,0,⟨-1,0⟩,1]]
def ranksBills : List ((Axis × Axis) → Bill Row.g) := 
  (pick wMatP wMatBills).map (gradTest dg) ++ (pick vMatP vMatBills).map (vecTest dg)
noncomputable def ranks : List ((Axis × Axis) → J Row.g) := 
  (pick wMatP wMat).map (recG.heatP Axis) ++ (pick vMatP vMat).map recG.divA
lemma ranksSure : Certified recG (Raw.v.tensorProd Raw.v) ranksBills ranks := Certified.combines
  ((wMatSure.keep _).scope _ _ (fun i=>funext (fun x=> grad_cost _ dg dg_c _ _ (fun _=>rfl) x)) (recG.chargeP Raw.v))
  ((vMatSure.keep _).scope _ _ (fun i=>funext (fun x=> vec_cost _ dg dg_c _ _ (fun _=>rfl) x)) recG.paid_A)

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma ranks_checked : verify [] ((ranksBills.map (bundleCost vvTest)).map Bill.norm) ranksP ranksCheck=true := by decide +kernel

theorem ranks_verified : Scan0 ranks ranksP := ranksSure.accepted _ (by decide) vvTest_ok _ _ ranks_checked
end YM.GaugeFieldConstruction.U1.gRanks
