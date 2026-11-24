import GaugeFieldConstruction.Vuoto
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{n:ℕ}{K u v w A' B' C':ℝ}
variable (X:Hub f){P:RG.BudgetPoint}{u' v':ℝ}(F:InkD f)(hp:PressB P X F u' v')(U:E→Pane f)(V:E→ Pane c)
variable (A B: Support (More f))(r s:Prism.Rock f)(i j:Prism.Rock c)(Z:E→Rill.Arch G t)(T:Rill.Arch G t)
variable (C Q:Toll (Iota G))(a:Suite (badge _) (pinH G t true) (pinH G t false) A C (W (true,true) A))(b:Suite (badge _) (pinH G t true) (pinH G t false) B Q (W (true,false) B))
-- path error paid.H.Var slots
include a b p in
lemma LithAge (g:Seat c→ SU.E)(Tp:E→Op Slot)(lQ:Allows n Tp z A'): Allows n (fun x=>litho G p W A B r s i j T g (Tp x)) z (wheel_l n*(wheel_l n*(horn*paintL G r i C)*A')*(horn*paintL G s j Q)) :=by
 let V:=fyL G true W (bring p T) A r i; let Y:=fyL G false W (bring p T) B s j
 have hP:‖V‖≤ horn*paintL G r i C:=by
   let I(x y:Slot):= C ((switchG G).symm (r,x)) (patchQ G (i,y)); have hp(x y):0 ≤ I x y:=a.nonn _ _; let W:= paintL G r i C
   have hw(x y): I x y ≤ W:=(single_le_sum (fun l (_:l∈(univ:Finset SU.Slot))=>hp x l) (mem_univ y)).trans (single_le_sum (fun j (_:j∈(univ:Finset SU.Slot))=>sum_nonneg (fun l (_:l∈(univ:Finset SU.Slot))=>hp j l)) (mem_univ x)); exact soft 1 V (sum_nonneg (fun x _=>sum_nonneg (fun y _=> hp x y))) fun x y=> ((a.expo ..).bounded _).trans (hw x y)
 have hQ:‖Y‖≤ horn*paintL G s j Q:=by
   let I(x y:Slot):= Q ((switchG G).symm (s,x)) (patchQ G (j,y)); have hp(x y):0 ≤ I x y:=b.nonn _ _; let W:= paintL G s j Q
   have hw(x y): I x y ≤ W:=(single_le_sum (fun l (_:l∈(univ:Finset SU.Slot))=>hp x l) (mem_univ y)).trans (single_le_sum (fun j (_:j∈(univ:Finset SU.Slot))=>sum_nonneg (fun l (_:l∈(univ:Finset SU.Slot))=>hp j l)) (mem_univ x)); exact soft 1 Y (sum_nonneg (fun x _=>sum_nonneg (fun y _=> hp x y))) fun x y=> ((b.expo ..).bounded _).trans (hw x y)
 let Fq:= putX g i; let Gv:=putX g j
 have hp:= leaf_h _ _ (allows_const _ (norm_star V|>.trans_le hP)) lQ
 have ht:= ship_x Fq Gv (matter _).property (matter _).property _ (leaf_h _ _ hp (allows_const _ hQ)); exact ht
end YM.CF.Haro
end
