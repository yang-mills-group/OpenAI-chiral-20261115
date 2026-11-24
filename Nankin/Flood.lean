import Nankin.Coins
import Nankin.Ship
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
open VacuumSelection VacuumSelection.Spine Py.Dyad Py.Dyad.Keeping
-- heights root with gauge L^d nodeC o -- odd obligation. step by stair.
abbrev hike (L:Side)(o:Cover) : Cover:= fun i=> (L.val:ℤ)*o i+((L.val:ℤ)-1)/2
lemma price_hike (L:Side)(o:Cover)(h:Odd L.val): nodeC (hike L o)=(L.val:ℕ) • nodeC o:=by
 obtain ⟨t⟩:=h; ext i; simp [nodeC,hike,two_smul,nsmul_eq_mul]; have H:(L.val:ℤ)=2*t+1:= by exact_mod_cast ‹_› -- weird
 rw [H,show ((2:ℤ)*t+1-1)/2=t by omega]; ring

variable (P:VacuumSelection.Spine)(i k j:ℕ)
local notation "A"=>stageA P i k
lemma fiscal_mul (P:VacuumSelection.Spine)(i k j:ℕ)(o:Cover):Hove.heel ((stageA P i k).ratio j) (wrap _ o)= (wrap _) (hike P.par.R.L o):=by
 apply node_du; rw [Py.claw _ (show Odd ((stageA P i k).ratio j).count.val from P.par.R.odd_side) _,node_of,node_of,price_hike _ _ P.par.R.odd_side]; rw [Lattice.Ratio.embed_wrap]; rfl
#check Py.claw
#check Ratio.embed_wrap
variable (o:Cover)
abbrev orbitB (L:Side)(o:Cover)(n:ℕ): Cover:= (hike L)^[n] o
lemma dutyT (L:Side)(t:Odd L.val)(n:ℕ):nodeC (orbitB L o n)= (L.val^n) • nodeC o:=by
 induction n with|zero=>simp [orbitB]|succ n ih=> rw [show orbitB L o (n+1)=hike L (orbitB L o n) from Function.iterate_succ_apply' ..,price_hike _ _ t, ih,pow_succ',mul_smul]

lemma stylus(j:ℕ)(o:Cover){I:Type}[LinearOrder I][Fintype I] (r:ℕ)(y:j≤r)(p:I)(c:I→Site (mid ((stageA P i k).side j) P.par.block))(t:c p= wrap _ o):liftCanvas P.par.V (stageA P i k) j r c p=wrap _ (orbitB P.par.R.L o (r-j)):=by
 by_cases u:j=r
 · subst r; simpa [liftCanvas, hop_here,orbitB] using t
 let A':=stageA P i k; have e:j<r:= y.lt_of_ne u
 unfold liftCanvas; rw [hop_step _ _ _ _ e]
 change liftCanvas P.par.V A' (j+1) r (adapt P.par.V A' j c) p=_
 have hp:adapt P.par.V A' j c p=((wrap _) (hike P.par.R.L o)):=by change Hove.heel _ (c p)= _; rw [t,fiscal_mul]
 have hk:= stylus (j+1) (hike P.par.R.L o) r (by omega) p _ hp
 rw [hk,show r-j=(r-(j+1))+1 by omega]
 rfl
termination_by r-j
decreasing_by omega
#check Hove.heel
#check stylus
#print axioms stylus
end Calico
end YM.CF.Buffered.Afterglow.Tower
