import Nankin.Coverer
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option linter.unusedVariables false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
variable (K:Calibration)(o:Cover)(D:BudgetPoint)(q:ℝ)(j:Axis)(s:ℤ)
open Decaf SlabMark
lemma node_du {n:Side}:Injective (@node n):= fun x y h=> (assembly n).embed_injective (add_right_cancel (show _+(1:Site (More n))=_+_ from h))
lemma node_dC:Injective nodeC:=fun x y e=> nsmul_right_injective (M:=Cover) two_ne_zero (add_right_cancel e)
lemma fly{n:Side}: (wrap n) ((plane j s).flee o)= Py.Rate.Decaf.center n j s (wrap n o):=by
 apply node_du; rw [Py.Rate.Decaf.placing,node_of,node_of,←show (plane j s).motion (nodeC o)=nodeC ((plane j s).flee o) from ((plane j s).mote o),Shape.anno] -- inspect
lemma ace: mirror K j s (lining K o D q)= lining K ((plane j s).flee o) D q:=by funext m; change reflMark j s _=_; rw [lining_at,lining_at, fly o j s, cameo_fold]
def slid(j:Axis)(v:ℤ)(o:Cover):=(plane j (gaugeT K v)).flee ((plane j 0).flee o)
lemma coilT(v:ℤ): relocate K j v (lining K o D q)=lining K (slid K j v o) D q:=by rw [←mirror_at K j (v:=v) (z:=0) (sub_zero _) (aux_test (lining_test ..)),ace,ace]; rfl
lemma cone_tick(v:ℤ) (i:Axis):slid K j v o i=o i + if i=j then gaugeT K v else 0:=by unfold slid; by_cases p:j=i <;> simp [flee_pos,p,eq_comm] <;> try omega -- orientation
lemma bellV(v:ℤ)(i:Axis): nodeC (slid K j v o) i=nodeC o i+if i=j then SlabMark.ruler K.B*v else (0:ℤ):=by
 rw [←ruler_offset]; unfold nodeC; simp [cone_tick,nsmul_eq_mul]; split_ifs <;> ring
#check Shape.mote
#print axioms ace
end Calico
end YM.CF.Buffered.Afterglow.Tower
