import Merino.Garter.Cast
import YM.SU5.Regis.Easel
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

def silver (q:Clip)(a:StepIn n)(i:Husk G n): Altar G n →L[ℝ] ℝ :=
 LinearMap.toContinuousLinearMap
    {toFun:= fun y=>a.cost i.1 * dust i.2 (river q (a.sent i.1) y)
     map_add':=fun _ _=>by simp [dust,mul_add]
     map_smul':=fun _ _=>by simp [dust,mul_left_comm]}


lemma silver_at(q:Clip)(a:StepIn n)(i:Husk G n)(x):
 silver q a i x=a.cost i.1 * dust i.2 (river q (a.sent i.1) x):=rfl

def gloss(T:Bundle G n)(q:Clip)(a:StepIn n)(x:Altar G n):ℝ :=
 let y i:=silver q a i x; dripQ T y y

lemma shadowC (B:Z.Bounds q η C S)(P:Attached H Z)
  (a:StepIn n)(i:Husk G n)(X:Dir G n):
 silver q a i (tiler B P X)=dust i.2 (faceCurl i.1 (a.steer X)):= by
 rw [silver_at, river_now q B P,a.swirl]; rfl
end YM.CF.Merino.Garter
