import GaugeFieldConstruction.MatrixScopeCW
import GaugeFieldConstruction.LexionCW
/-!
# Pivot certificate, normalized and in null-momentum chart
 `RankClasses` already derives dimension from exact bills in shell jets. Read results also as
 exactly the Greedy Scan of the RankSupplement chart of U1 (not Python implementation; mathematically
 complex-polynomial-evaluated entries). No factoring of ratios/code external to Lean. For g/f
 trace receive REDUCED T list. For x,T list empty (no claim on d=5 x to d=4 space; by grade).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6500
noncomputable section
namespace YM.GaugeFieldConstruction.U1.TableDictionary
open Function Raw Cauchy Row Vouchers Certificate
open scoped Matrix BigOperators
variable {S O U β : Type*} (C:S→J U→ₗ[ℂ]ℂ)(R:Record U β)
abbrev OnChart (m : List (O→ J U)) (b:List Bool):= Scan0 (m.map (photo C O)) b
structure CountW (w : List (Axis → J U)) (v : List (VS → J U)) (b c d : List Bool) : Prop where
 rankW: OnChart C w b
 rankV: OnChart C v c
 piv: OnChart C ((pick b w).map (R.heatP Axis) ++ (pick c v).map R.divA) d
structure CountT (t : List (Raw.Sym → J U)) (b c d: List Bool): Prop where
 rankT: OnChart C t b
 divergeT: OnChart C ((pick b t).map R.divP) c
 traceT: OnChart C ((pick b t).map Record.trace) d

variable {t: List (Raw.Sym→ J U)}{w:List (Axis→ J U)}{v: List (VS → J U)} (h:DeterminedBy C) {i j k:List Bool}
include h
lemma leavesW (bw bv)(f:Tracks w bw)(g:Tracks v bv)(F: Scan0 w i)(G: Scan0 v j)(P:Scan0 ((pick i w).map (R.heatP Axis) ++ (pick j v).map R.divA) k):CountW C R bw bv i j k:=by
 refine ⟨pivot_image _ (paid_photo C h) f F, pivot_image _ (paid_photo C h) g G, ?_⟩
 apply pivot_image (photo C (Axis×Axis)) (paid_photo C h) _ P
 exact Tracks.combine (Tracks.transfer _ (f.slice i)) (Tracks.transfer _ (g.slice j))
lemma leavesT (bt)(f:Tracks t bt)(F:Scan0 t i)(S: Scan0 ((pick i t).map R.divP) j)(G:Scan0 ((pick i t).map Record.trace) k): CountT C R bt i j k := by
 exact ⟨pivot_image _ (paid_photo C h) f F, pivot_image _ (paid_photo C h) (Tracks.transfer _ (f.slice i)) S,
      pivot_image _ (paid_photo C h) (Tracks.transfer _ (f.slice i)) G⟩
omit h
section
open gRanks
abbrev gT := receiptMat g4Act symAct evalTg g4T
abbrev gW := receiptMat g5Act Raw.v evalG g5W
abbrev gV := receiptMat g5Act vsAct evalG g5V
lemma gT_rank : CountT gChart recG gT tMatP divsP facesP := leavesT gChart recG chart_g _ (transfers _ _ _ _ (fun i h=>(g4T_ok.good i h).2)) tMat_verified divs_verified faces_verified
   -- prevent parser
lemma gWV_rank : CountW gChart recG gW gV wMatP vMatP ranksP := leavesW gChart recG chart_g _ _
  (transfers g5Act Raw.v evalG g5W (fun i h=>(g5W_ok.good i h).2))
  (transfers _ _ _ _ (fun i h=>(g5V_ok.good i h).2)) wMat_verified vMat_verified ranks_verified
end
section
open fRanks
abbrev fT := receiptMat f4Act symAct evalTf f4T
abbrev fW := receiptMat f5Act Raw.v evalF f5W
abbrev fV := receiptMat f5Act vsAct evalF f5V
lemma fT_rank : CountT fChart ph fT tMatP divsP facesP:= leavesT fChart ph chart_f _
   (transfers _ _ _ _ (fun i h=>(f4T_ok.good i h).2)) tMat_verified divs_verified faces_verified
lemma fWV_rank : CountW fChart ph fW fV wMatP vMatP ranksP:= leavesW fChart ph chart_f _ _
   (transfers _ _ _ _ (fun i h=>(f5W_ok.good i h).2))
   (transfers _ _ _ _ (fun i h=>(f5V_ok.good i h).2)) wMat_verified vMat_verified ranks_verified
end
section
open xRanks
abbrev xW := receiptMat x5Act Raw.v evalX x5W
abbrev xV := receiptMat x5Act vsAct evalX x5V
lemma xWV_rank : CountW xChart recX xW xV wMatP vMatP ranksP:= leavesW xChart recX chart_x _ _
   (transfers _ _ _ _ (fun i h=>(x5W_ok.good i h).2))
   (transfers _ _ _ _ (fun i h=>(x5V_ok.good i h).2)) wMat_verified vMat_verified ranks_verified
end
#print axioms gT_rank
#print axioms gWV_rank
#print axioms fT_rank
#print axioms fWV_rank
#print axioms xWV_rank
#print axioms U1.g_ranks
#print axioms U1.f_ranks
#print axioms U1.x_ranks
end YM.GaugeFieldConstruction.U1.TableDictionary
