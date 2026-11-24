import Nankin.Flood
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
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
open VacuumSelection VacuumSelection.Spine Py.Dyad Py.Dyad.Keeping Py.Rate.Decaf
-- uncertain telescope: at base pose o Cover on f=Lodge j. endpoints both appear at heels. Couple at v=s+1. regulator,F. fidelity.
variable (P:VacuumSelection.Spine)(s j i k:ℕ)(u:j≤ s)(t:s+1≤P.run.uv k)(C D:ℕ→ℝ)
local notation "Y"=> P.run
local notation "K"=> tent P.run P.large
local notation "L0"=>P.par.R.L
abbrev denom (b:Bool):Drift.PairKey (Fin 1):= (0,b)
variable (o:Cover)(b:Bool)
-- Born observable at specified tier. Lifts in Cover.
abbrev watch (P:VacuumSelection.Spine)(s:ℕ)(o:Cover):Family (P.calibration):= lining P.calibration o (P.run.meter.a s) (payday P s)
abbrev ridge (P:VacuumSelection.Spine)(s j:ℕ)(o:Cover):=watch P s (orbitB P.par.R.L o (s-j))
abbrev ag (b:Bool):Tix (stageA P i k) j:= (wrap _ o,b)
-- spectacular label pose version.
lemma cash_cons : ‖shareS L0 s j (denom b)‖≥0:=norm_nonneg _
lemma ship_lining {V W:Side}(e:V=W)(o:Cover)(p:BudgetPoint)(q:ℝ):ship e (cameo ((wrap V) o) p q)= cameo ((wrap W) o) p q:=by subst W; rfl
include t
lemma giving (v:ℕ)(h:v≤ s+1)(p:Cover):distribute P.run P.large v i (watch P v p)=cameo ((wrap _) p) ((stageA P i k).gram v).p ((stageA P i k).money v):=by
 unfold distribute watch; rw [lining_at,ship_lining,show ((stageA P i k).gram v).p=P.run.meter.a v from (Papal.prices_plot P.run v i k (h.trans t)).1]
-- pβ at those roots. identity sends etc.
local notation "α"=>shareT L0 C D s (s+1) j (denom b)
local notation "β"=>shareS L0 s j (denom b)
section
include t u
lemma pilgrim (h:distribute P.run P.large (s+1) i (block P.run P.large s i k (bands (orbitB L0 o (s-j)) 22) (ridge P s j o)) = aboveD P.run P.large s i k (ridge P s j o)):
 pose2 (stageA P i k) j s (ag P j i k o b) (s+1) (stageφ P i k) C D = distribute P.run P.large (s+1) i (α • ridge P (s+1) j o + β • block P.run P.large s i k (bands (orbitB L0 o (s-j)) 22) (ridge P s j o)):=by
 let V:=stageA P i k; let a:= fun _:Fin 1=> ((ag P j i k o b).1); let w:= orbitB P.par.R.L o (s-j)
 have ht: liftCanvas P.par.V V j s a 0= wrap _ w:=stylus P i k j o s u _ _ rfl
 have hu:liftCanvas P.par.V V s (s+1) (liftCanvas P.par.V V j s a) 0=wrap _ (orbitB P.par.R.L o (s+1-j)):=by
    rw [stylus P i k s w (s+1) (Nat.le_succ _) _ _ ht]; apply congrArg _; rw [show s+1-j=(s-j)+1 from by omega]; unfold w orbitB; simp [iterate_succ_apply'] -- orientation
 have hΒ (F: Buffered.Mark (mid (V.side s) P.par.block)): Keeping.blaze P.par.V V (stageφ P i k) s (s+1) F= (stageφ P i k) s F:=by unfold Keeping.blaze; rw [hop_step _ _ _ _ (Nat.lt_succ_self _),hop_here]
 rw [(distribute_arith P.run P.large (s+1) i (α • _) (β • _) 0).1, (distribute_arith P.run P.large (s+1) i (ridge P (s+1) j o) 1 _).2.2.1,(distribute_arith P.run P.large (s+1) i _ 1 β).2.2.1,h,←nextboard,(giving P s i k t) _ le_rfl,(giving P s i k t) _ (Nat.le_succ _)] -- abbrev ridge not reducible for rw yes? rewrite no. explicit
 unfold pose2 playto; dsimp only
 unfold a at ht hu
 rw [ht,hu,hΒ]
-- check
end
#check pose2
#check ag
#print axioms pilgrim
end Calico
end YM.CF.Buffered.Afterglow.Tower
