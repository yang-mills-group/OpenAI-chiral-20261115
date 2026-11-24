import GaugeFieldConstruction.Certification
import GaugeFieldConstruction.F5Reps
import GaugeFieldConstruction.F4Reps
/-!
# Certificate for U1-f. Pivot columns ordered as in RankSupplement. Complex rank.
-/
namespace YM.GaugeFieldConstruction.U1.fRanks
set_option autoImplicit false
set_option synthInstance.maxSize 4000
open Raw Vouchers Cauchy Row Camera Stub Certificate Record

def unitTest : List Unit := [()]
lemma unitTest_ok : Hits (Labels.unitL Unit) unitTest := fun i=> ⟨i,by simp [unitTest],1,rfl⟩
-- 1-indexed pivots: [1, 3]
def tMatP := [true,false,true]
private def tMatCheck : List (Stub (Raw.Sym × Row.f)) := [success [(((S 0 0),((0,1,0,0),(1,0,0,0))),1)],
  decline (⟨3,0⟩) [1],
  success [(((S 0 1),((0,0,1,0),(1,0,0,0))),1)]]
def tMatBills : List ((Raw.Sym) → Bill Row.f) := f4T.map (inspect f4Act symAct f4Cost)
noncomputable def tMat : List ((Raw.Sym) → J Row.f) := f4T.map (Record.column symAct f4Act evalTf)
lemma tMatSure : Certified (ferm true) symAct tMatBills tMat := endorses _ _ f4T_ok _ readingTf face4

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma tMat_checked : verify [] ((tMatBills.map (bundleCost sTest)).map Bill.norm) tMatP tMatCheck=true := by decide +kernel

theorem tMat_verified : Scan0 tMat tMatP := tMatSure.accepted _ (by decide) sTest_ok _ _ tMat_checked
-- 1-indexed pivots: [1]
def wMatP := [true,false,false,false]
private def wMatCheck : List (Stub (Axis × Row.f)) := [success [((0,((0,2,0,0),(1,0,0,0))),1)],
  decline (⟨3,0⟩) [1],
  decline (⟨3,0⟩) [1],
  decline (⟨3,0⟩) [1]]
def wMatBills : List ((Axis) → Bill Row.f) := f5W.map (inspect f5Act Raw.v f5Cost)
noncomputable def wMat : List ((Axis) → J Row.f) := f5W.map (Record.column Raw.v f5Act evalF)
lemma wMatSure : Certified (ferm true) Raw.v wMatBills wMat := endorses _ _ f5W_ok _ readingF face5

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma wMat_checked : verify [] ((wMatBills.map (bundleCost wTest)).map Bill.norm) wMatP wMatCheck=true := by decide +kernel

theorem wMat_verified : Scan0 wMat wMatP := wMatSure.accepted _ (by decide) wTest_ok _ _ wMat_checked
-- 1-indexed pivots: [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 24, 26]
def vMatP := [true,true,true,true,true,true,true,true,true,false,false,false,true,true,true,false,false,false,false,false,false,false,false,true,false,true,false,false,false]
private def vMatCheck : List (Stub (VS × Row.f)) := [success [(((0,(S 1 2)),((0,0,1,1),(1,0,0,0))),1)],
  success [(((0,(S 1 2)),((0,0,1,0),(0,0,1,0))),1),(((0,(S 1 2)),((0,0,1,1),(1,0,0,0))),⟨0,1⟩)],
  success [(((0,(S 0 1)),((1,2,0,0),(0,0,0,0))),1)],
  success [(((0,(S 1 1)),((1,1,1,0),(0,0,0,0))),1)],
  success [(((0,(S 0 0)),((0,2,0,0),(1,0,0,0))),1)],
  success [(((0,(S 1 1)),((0,2,0,0),(1,0,0,0))),1)],
  success [(((0,(S 0 1)),((0,0,2,0),(1,0,0,0))),1)],
  success [(((0,(S 0 1)),((0,0,1,0),(1,1,0,0))),1),(((0,(S 0 1)),((1,2,0,0),(0,0,0,0))),⟨0,1⟩)],
  success [(((0,(S 1 1)),((0,0,1,0),(1,1,0,0))),1),(((0,(S 1 1)),((1,1,1,0),(0,0,0,0))),1)],
  decline (⟨3,0⟩) [0,0,0,0,1],
  decline (⟨2,0⟩) [1,0,0,1],
  decline (⟨2,0⟩) [0,1,1],
  success [(((0,(S 1 2)),((0,0,1,0),(0,1,0,0))),⟨2,0⟩),(((0,(S 1 2)),((0,0,1,1),(1,0,0,0))),1)],
  success [(((0,(S 0 1)),((0,0,0,0),(1,1,1,0))),1),(((0,(S 0 1)),((0,0,1,0),(1,1,0,0))),1),(((0,(S 0 1)),((1,2,0,0),(0,0,0,0))),⟨0,2⟩)],
  success [(((0,(S 1 1)),((1,0,2,0),(0,0,0,0))),⟨2,0⟩),(((0,(S 1 1)),((0,0,1,0),(1,1,0,0))),⟨0,1⟩),(((0,(S 1 1)),((1,1,1,0),(0,0,0,0))),⟨0,-1⟩)],
  decline (⟨3,0⟩) [0,0,0,0,0,0,0,1],
  decline (⟨2,0⟩) [1,0,0,0,0,0,1],
  decline (⟨2,0⟩) [0,1,0,0,0,1],
  decline (⟨3,0⟩) [0,0,0,0,0,0,0,1],
  decline (1) [⟨-1,0⟩,0,0,0,0,0,0,0,⟨-2,0⟩],
  decline (⟨2,0⟩) [1,0,0,0,0,0,1,0,⟨2,0⟩],
  decline (1) [0,⟨-1,0⟩,0,0,0,0,0,0,0,⟨-2,0⟩],
  decline (⟨2,0⟩) [0,1,0,0,0,1,0,0,0,⟨2,0⟩],
  success [(((0,(S 1 2)),((0,1,1,0),(0,0,0,0))),⟨2,0⟩),(((0,(S 1 2)),((0,0,1,1),(1,0,0,0))),1)],
  decline (1) [⟨-1,0⟩,0,0,0,0,0,0,0,0,0,0,1,1],
  success [(((0,(S 1 2)),((0,0,2,0),(0,0,0,0))),⟨2,0⟩),(((0,(S 1 2)),((0,1,1,0),(0,0,0,0))),⟨0,2⟩),(((0,(S 1 2)),((0,0,1,0),(0,1,0,0))),⟨0,-2⟩),(((0,(S 1 2)),((0,0,1,0),(0,0,1,0))),1)],
  decline (1) [1,⟨-1,0⟩,0,0,1],
  decline (⟨2,0⟩) [0,0,0,⟨-1,0⟩,0,0,1,0,0,0,0,⟨-2,0⟩],
  decline (⟨2,0⟩) [0,0,⟨-1,0⟩,0,0,1,0,0,0,0,⟨-2,0⟩]]
def vMatBills : List ((VS) → Bill Row.f) := f5V.map (inspect f5Act vsAct f5Cost)
noncomputable def vMat : List ((VS) → J Row.f) := f5V.map (Record.column vsAct f5Act evalF)
lemma vMatSure : Certified (ferm true) vsAct vMatBills vMat := endorses _ _ f5V_ok _ readingF face5

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma vMat_checked : verify [] ((vMatBills.map (bundleCost vTest)).map Bill.norm) vMatP vMatCheck=true := by decide +kernel

theorem vMat_verified : Scan0 vMat vMatP := vMatSure.accepted _ (by decide) vTest_ok _ _ vMat_checked
-- 1-indexed pivots: [1]
def divsP := [true,false]
private def divsCheck : List (Stub (Axis × Row.f)) := [success [((0,((0,2,0,0),(1,0,0,0))),1)],
  decline (⟨3,0⟩) [⟨2,0⟩]]
def divsBills : List ((Axis) → Bill Row.f) := 
  (pick tMatP tMatBills).map (dimTest (dp false))
noncomputable def divs : List ((Axis) → J Row.f) := 
  (pick tMatP tMat).map (ferm true).divP
lemma divsSure : Certified (ferm true) Raw.v divsBills divs := (tMatSure.keep _).scope (dimTest (dp false)) (ferm true).divP (fun i => funext (fun x => dim_cost _ (dp false) dp_c i _ (fun _=>rfl) x)) (ferm true).paid_div

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma divs_checked : verify [] ((divsBills.map (bundleCost wTest)).map Bill.norm) divsP divsCheck=true := by decide +kernel

theorem divs_verified : Scan0 divs divsP := divsSure.accepted _ (by decide) wTest_ok _ _ divs_checked
-- 1-indexed pivots: []
def facesP := [false,false]
private def facesCheck : List (Stub (Unit × Row.f)) := [decline (1) [],
  decline (1) []]
def facesBills : List ((Unit) → Bill Row.f) := (pick tMatP tMatBills).map trTest
noncomputable def faces : List ((Unit) → J Row.f) := (pick tMatP tMat).map trace
lemma facesSure : Certified (ferm true) (Labels.unitL Unit) facesBills faces := (tMatSure.keep _).scope trTest _ (fun i => funext (fun x => tr_cost _ _ (fun _=>rfl) x)) (ferm true).paid_trace

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma faces_checked : verify [] ((facesBills.map (bundleCost unitTest)).map Bill.norm) facesP facesCheck=true := by decide +kernel

theorem faces_verified : Scan0 faces facesP := facesSure.accepted _ (by decide) unitTest_ok _ _ faces_checked
-- 1-indexed pivots: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15]
def ranksP := [true,true,true,true,true,true,true,true,true,true,true,true,false,false,true]
private def ranksCheck : List (Stub ((Axis × Axis) × Row.f)) := [success [(((0,0),((0,3,0,0),(1,0,0,0))),1)],
  success [(((0,1),((0,0,1,2),(1,0,0,0))),1)],
  success [(((0,1),((1,0,3,0),(0,0,0,0))),1)],
  success [(((0,0),((0,1,0,1),(0,1,0,0))),1)],
  success [(((0,1),((1,0,2,0),(0,0,1,0))),1),(((0,1),((1,0,3,0),(0,0,0,0))),1)],
  success [(((0,1),((0,1,2,0),(1,0,0,0))),1),(((0,1),((1,0,3,0),(0,0,0,0))),⟨0,-1⟩),(((0,0),((0,3,0,0),(1,0,0,0))),⟨0,1⟩)],
  success [(((0,1),((0,2,1,0),(1,0,0,0))),⟨4,0⟩),(((0,1),((1,0,2,0),(0,0,1,0))),1),(((0,0),((0,1,0,1),(0,1,0,0))),⟨2,0⟩),(((0,1),((1,0,3,0),(0,0,0,0))),⟨-1,0⟩)],
  success [(((0,0),((0,0,3,0),(1,0,0,0))),1)],
  success [(((0,1),((0,1,1,0),(1,1,0,0))),1)],
  success [(((0,1),((0,1,1,0),(1,0,1,0))),⟨2,0⟩),(((0,1),((1,0,2,0),(0,0,1,0))),⟨0,-1⟩),(((0,1),((1,0,3,0),(0,0,0,0))),⟨0,1⟩)],
  success [(((0,1),((0,0,1,0),(0,1,0,1))),1)],
  success [(((0,1),((0,3,0,0),(1,0,0,0))),⟨4,0⟩),(((0,1),((1,0,2,0),(0,0,1,0))),⟨0,1⟩),(((0,0),((0,1,0,1),(0,1,0,0))),⟨0,2⟩),(((0,1),((1,0,3,0),(0,0,0,0))),⟨0,-1⟩)],
  decline (⟨3,0⟩) [0,0,0,0,0,0,1,0,0,0,0,⟨-1,0⟩],
  decline (⟨6,0⟩) [⟨3,0⟩,0,0,⟨3,0⟩,0,0,0,0,⟨6,0⟩,⟨-6,0⟩,⟨-6,0⟩,⟨2,0⟩],
  success [(((0,1),((1,2,0,0),(0,1,0,0))),1),(((0,1),((0,3,0,0),(1,0,0,0))),1)]]
def ranksBills : List ((Axis × Axis) → Bill Row.f) := 
  (pick wMatP wMatBills).map (gradTest (dp false)) ++ (pick vMatP vMatBills).map (vecTest (dp false))
noncomputable def ranks : List ((Axis × Axis) → J Row.f) := 
  (pick wMatP wMat).map ((ferm true).heatP Axis) ++ (pick vMatP vMat).map (ferm true).divA
lemma ranksSure : Certified (ferm true) (Raw.v.tensorProd Raw.v) ranksBills ranks := Certified.combines
  ((wMatSure.keep _).scope _ _ (fun i=>funext (fun x=> grad_cost _ (dp false) dp_c _ _ (fun _=>rfl) x)) ((ferm true).chargeP Raw.v))
  ((vMatSure.keep _).scope _ _ (fun i=>funext (fun x=> vec_cost _ (dp false) dp_c _ _ (fun _=>rfl) x)) (ferm true).paid_A)

set_option maxRecDepth 800000 in
set_option maxHeartbeats 2000000 in
private lemma ranks_checked : verify [] ((ranksBills.map (bundleCost vvTest)).map Bill.norm) ranksP ranksCheck=true := by decide +kernel

theorem ranks_verified : Scan0 ranks ranksP := ranksSure.accepted _ (by decide) vvTest_ok _ _ ranks_checked
end YM.GaugeFieldConstruction.U1.fRanks
