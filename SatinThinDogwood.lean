import SatinFixedContrastNovember4
import SatinThinPilgrim
import SatinThinTripods
import SatinThinCardiff
import YM.SU5.Regis.Legend
import YM.SU5.Hiro.Ladles
import YM.SU5.Regis.Voyance
import YM.SU5.Celeste.Custodian

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
variable (z:PlaqAxes→ℝ) {I U:Type} [Fintype I] [Fintype U] (T:Trip I)(s:ℕ)(b:U→ ℕ)
local notation "xθ"=> hat P.par.R.L P.par.x s
/-! # affine pose bill and count. -/
variable (A:ℝ)
local notation "M"=> P.par
open BProof Py.Rate.Pannier Py.Rate.LocalLimit.Papal
open Signal.Interval (separationCost)
open Lattice
/-! # All heights in a paid stream. `Vetted` budget g for any such stencil.
    Use probabilities already of preparation, with permit in ShelterCost (earned cp6 etc.). -/
local notation "νW"=> Lamour.Bridge.Celeste.breadth 0 noonFrame
open Pressure.Worth Pressure.Worth.Pays
variable (v v₀:ℝ)
/-! # Convergence sufficient for L² first and L¹ pair errors (propagate later through shifts).
      Only this high-moment budget, selected once per regime. -/
open Etch Regis.Head.Brecht
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
local notation "p₀"=> Yoke.paperN (P:=P.par) z
variable {Cε:ℝ}(Q':∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost Cε P.run s i k)
open Regis.Circuit
open Designs Prototype
variable (d:ℝ)
noncomputable abbrev haloCost (s:ℕ)(x:P.Spectrum0 3):= P.mistake 3 witnessZ s (scout P.par d s) (CheckPoint P.par d s) 0 (YM.basis 3) x
include Q'
lemma movement_line (u:0<d) : Tendsto (fun s=> ∫ x,P.haloCost d s x∂P.pillars 3) atTop (𝓝 0):=by
 let v:= 8*d+1; let A:=13+2*v+1; let b:=6*A+2*v+1; have hv:d<b:=by unfold b A v; linarith; -- syntax
 let ρ(s:ℕ):ℝ:= (scout P.par d s:ℝ); apply P.mistake_go 3 witnessZ A v b Q' (ρ:=ρ) (x:=CheckPoint P.par d) (y:=0) (Z:=YM.basis 3) (heightMerit P.par d) (scouts_height P.par d u) _ _ _ _ (lt_add_of_pos_right _ zero_lt_one) (by unfold v; positivity) (lt_add_of_pos_right _ zero_lt_one) -- specify order
 · simp_rw [Pi.zero_apply,sub_zero, ρ, paintedJourney]; exact tendsto_const_nhds
 · intro p; simpa using congrArg norm p
 · filter_upwards [(turnover P.par).eventually (leap (w:=0) (p:=b) (q:=0) (helmBound d u) (Or.inr (Or.inl ⟨rfl,hv⟩)))] with s H x a; cases x
   · exact Nat.zero_le _
   change (((scout P.par d s)• (Lattice.step 3:Cover)) a).natAbs ≤ _; by_cases h:a=(3:Axis); · simp [h]; exact (Nat.le_ceil _).trans (H.trans (Nat.le_ceil _))
   simp [h]
 · exact routeCharge P.par d u (show 8*d<v from by unfold v; linarith)
variable (ε:ℝ)
omit Q' in
lemma choose_gradients (f:ℕ→ℕ): ∃ z':ℕ→ℕ,StrictMono z'∧ f ≤ z':=by let g:ℕ→ℕ := Nat.rec (f 0) (fun i v=>max (f (i+1)) (v+1)); exact ⟨g,strictMono_nat_of_lt_succ fun i=> (Nat.lt_succ_self _).trans_le (le_max_right (f (i+1)) (g i+1)),fun i=> by cases i; rfl; exact le_max_left ..⟩
include Q'
-- assemble c AFTER all spending. high prob implication later.
lemma chooseFarther (u:0<d) (h:0<ε) : ∃ f:ℕ→ℕ,∀ g:ℕ→ℕ,f ≤g→ ∀ᵐ x∂P.pillars 3, ∀ᶠ i in atTop,(P.haloCost d (g i) x)< ε:=by
 have hi(p:ℕ):0< discount p (Real.sqrt ε):=by unfold discount; positivity
 choose f H using fun i=> eventually_atTop.mp ((P.movement_line Q' d u).eventually (ge_mem_nhds (hi i)))
 refine ⟨f,fun g hu=>?_⟩
 filter_upwards [prognosis (I:=fun _=>Unit) (fun i _=> P.haloCost d (g i)) (fun i=> discount i (Real.sqrt ε)) (fun i _=> P.mistake_live 3 witnessZ ..) (fun i _ _=> norm_nonneg _) (fun _=> Real.sqrt ε) (fun _=> Real.sqrt_pos.mpr h) (fun n _=> H n _ (hu n)) (fun _=> by simp)] with x h'
 filter_upwards [h'] with i he; exact (he ()).trans_le (le_of_eq (Real.sq_sqrt h.le))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.movement_line

#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.chooseFarther
