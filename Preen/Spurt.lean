import Preen.Heres
import Preen.Scene
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 220000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Dyad Keeping
open Ballad Cordial Cheer Prototype Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn Designs Twah Six Habitat Habitat.Hemlock
open Py.Rate.Pitching.Focus (Morn)
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))(T:RobeRoad P F C D x)(α:ℝ)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "X"=>ruler P.par.block
local notation "L0"=>P.par.R.L
variable {c r:ℕ→ℕ}{K:P.Register}{J:P.Ellis 3 x}(B:P.Experiment K c r x J)
abbrev pollN(P:Spine):ℕ:=16*P.par.block.val
lemma poll_correct:(pollN P:ℤ)=(X):=rfl
-- ticks oriented pair roots
abbrev trailerH(P:Spine)(d k:ℕ):ℕ:=P.par.R.L.val^k*reachQ P (hikeV d)+P.calibration.ℓ+22+1+pollN P
abbrev idleCar(P:Spine):ℕ:=pollN P+P.calibration.ℓ+22+1
/- Long detection. relative shift at least constant times $L^k (log X_j)^6$ in gauge units, small on all other axes. constant factor independent of j predetermined. enough. -/
def spindle(P:Spine)(d k:ℕ): Cover:= fun i=> ((if i=(3:Axis) then 4*trailerH P d k else 4*idleCar P:ℕ):ℤ)
structure Enrolled(P:Spine)(d k:ℕ) (w:Cover): Prop where
 side(i:Axis)(e:i≠3) : 0 ≤nodeC w i ∧ nodeC w i ≤ (ruler P.par.block)
 clock : (P.calibration.ℓ:ℤ)+22 ≤ nodeC w (3:Axis) ∧ nodeC w (3:Axis) ≤ (P.par.R.L.val:ℤ)^k*reachQ P (hikeV d)
lemma ribbon_ms{d k:ℕ}{w:Cover}(p:Enrolled P d k w)(i:Axis) : (beamU P w i:ℤ)+(beamU P w i:ℤ)< spindle P d k i - (0:Cover) i:=by
 unfold spindle; split_ifs with h
 · subst i; obtain ⟨l,r⟩:= p.clock
   have ho: ((P.par.R.L.val:ℤ)^k*reachQ P (hikeV d))=(↑((P.par.R.L.val:ℕ)^k*reachQ P (hikeV d)):ℤ):=(by push_cast; rfl) --
   unfold beamU trailerH; rw [ho] at r; change _< _-0; omega
 obtain ⟨l,r⟩:=p.side i h
 rw [← poll_correct] at r; unfold idleCar beamU; change _ < _-0; omega
-- expense upper: on actual x, if no interaction at these regulators. Mirror recognition.One solid.L.
noncomputable abbrev altitude(P:Spine)(x:P.Spectrum0 3)(d k:ℕ)(w:Cover):ℝ:=‖expenseR P x (hikeV d+k) w 0 (spindle P d k)‖
include p T v B
lemma enrichment(z:¬Vacation P F C D x B):∀ᶠ d:ℕ in atTop,∀ k:ℕ,∃ w:Cover,Enrolled P d k w ∧ altitude P x d k w ≤ thresholdU P M α d k^2:=by
 filter_upwards [interrogation P F C D x M p T α v B z] with d dZ k
 let j:=hikeV d; let s:=j+k; let o:=cellar P F j; let w:=orbitB L0 o (s-j)
 have hx:= dutyT o L0 P.par.R.odd_side (s-j) -- order?
 have hc: nodeC w 3=(P.par.R.L.val:ℤ)^k*nodeC o (3:Axis):=by unfold w; rw [hx]; unfold s; rw [Nat.add_sub_cancel_left]; simp [nsmul_eq_mul]
 have ht:1 ≤(P.par.R.L.val:ℤ)^k:=by exact_mod_cast (show 1 ≤ P.par.R.L.val^k from Nat.one_le_of_lt (pow_pos P.par.R.L.property _))
 have hΩ : (P.calibration.ℓ:ℤ)+22≤ nodeC w (3:Axis):= by rw [hc]; have he:=fresh P F j; change _ ≤ nodeC o 3 at he; nlinarith only [he,ht,Int.natCast_nonneg P.calibration.ℓ]
 obtain ⟨y,t,g,r⟩:=detross P (ξ) s w hΩ
 have hE:Enrolled P d k y:=⟨g, hΩ.trans_eq t.symm, by rw [t,hc]; exact mul_le_mul_of_nonneg_left (recess P F j|>.2) (zero_le_one.trans ht)⟩
 refine ⟨y,hE,(expense_price P x s y hE.clock.1 J (ribbon_ms P hE)).trans (pow_le_pow_left₀ ?_ ?_ 2)⟩
 exact norm_nonneg _
 exact r.le.trans (show driftCost P (ξ) s w hΩ ≤_ from dZ k) -- equality orientation
#print axioms enrichment
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
