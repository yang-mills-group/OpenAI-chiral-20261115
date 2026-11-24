import Rods.Steam
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 6000
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
open Py.Rate.Pitching.Focus Dyad Keeping
open VacuumSelection
variable (P:Spine)
local notation "Y"=> P.run
local notation "K"=> tent P.run P.large
local notation "π" i:max => P.period (P.projection.rows i) -- check
local notation "ζ" i:max => P.cutoff (P.projection.columns i)
open Spine
-- v=r+1
lemma nextboard(s i k:ℕ)(f:Family (tent P.run P.large)): stageφ P i k s (distribute P.run P.large s i f)= aboveD P.run P.large s i k f:=rfl
lemma hot_pay(v i k:ℕ)(h:(P.run.voyage i).kick≤ k)(F:Family K): hot P.run P.large v i k F = solder P.run i k h v (distribute P.run P.large v i F):=by
 unfold hot; rw [dif_pos h]; rfl
#check nextboard
#check Coherent
variable (s:ℕ)(S:Finset Cover)(f:Family (tent P.run P.large))
-- deliver once across aboveD.ignore hS widths variations
lemma refinery (l:InTest K true S false f):∀ᶠ a:ℕ in atTop, distribute P.run P.large (s+1) (π a) (block P.run P.large s (π a) (ζ a) S f)=aboveD P.run P.large s (π a) (ζ a) f := by -- cast bad. use succ
 filter_upwards [P.history.finance (s+1), (P.law.pick.grow_i.comp P.history.growsA).tendsto_atTop.eventually (turning P.run P.large (s+1) (wingspan P.par P.width S))] with a h t
 exact reserved P.run P.large s S _ _ ⟨h.depth,h.enters⟩ l t

lemma passes (L':InTest K true S false f): BQueue (wingspan P.par P.width S) (fun i=> block P.run P.large s (π i) (ζ i) S f) (P.refineTest s f):=by
 -- use implements
 obtain ⟨A,H,h⟩:=P.history.implements s S; obtain ⟨n,v⟩:= Journey.valuation P.run P.large L'; let N:=n+1; have q:0<N:=add_pos_of_nonneg_of_pos (pay_nonneg (F:=f) v) zero_lt_one
 have k:pay f N:=fun i p=> (v i p).trans (le_add_of_nonneg_right zero_le_one)
 have e:=h 1 zero_lt_one; obtain ⟨i,e'⟩:=e.exists
 have e₁:= P.history.circuit.supports s L'|>.1
 exact ⟨fun _=> booked ..,e₁, ⟨A*N,mul_pos H q,(e' f L' N k).1,e.mono fun i h=>(h f L' N k).2.1⟩,fun p b=>(h (p/N) (div_pos b q)).mono fun _ a=> by let l:= (a f L' N k).2.2.1; rw [div_mul_cancel₀ _ q.ne'] at l; exact l⟩
#print axioms passes
end Calico
end YM.CF.Buffered.Afterglow.Tower
