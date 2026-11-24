import SatinThinWyrms
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
include Q'
open Next.Free -- spectrum namespace
open Regis.Circuit
omit Q' in
abbrev wagerQ (x:Gaia) := (Aster P.run P.period P.cutoff s:ℂ)^4 * spectrumℓ z SU.group x
omit Q' in
abbrev mistake (R:ℝ) (x y:Cover)(w:Gaia)(u:P.Spectrum0 j):ℝ:= ‖(R:ℂ)^8 * P.pulseQ j z s x y u- P.wagerQ z s w‖
omit Q' in
lemma mistake_live (R:ℝ)(x y:Cover)(w:Gaia): Continuous (P.mistake j z s R x y w):= ((continuous_const.mul (P.pulseq_live j z s x y)).sub continuous_const).norm
variable {ρ:ℕ→ℝ}{x y:ℕ→ Cover}{Z:Gaia}(p:∀ i,0<ρ i)(zR:Tendsto ρ atTop atTop)(hv:Tendsto (fun i:ℕ=>Onyx.riseX (ρ i) (x i-y i)) atTop (𝓝 Z))(hw:Z≠0)
 (Y0:∀ᶠ i in atTop,CoversT (twinTrip (x i) (y i)) (scout P.par v₀ i))
 (V:Tendsto (fun i:ℕ=> ρ i^8/trailℓ v (hat P.par.R.L P.par.x i)) atTop (𝓝 0))
include p zR hv hw Y0 V -- adapt height budget to more flexible use
lemma mistake_go (h0:13+2*v < A)(u:0< v)(h:v₀> 6*A+2*v) : Tendsto (fun s=>∫ i, (P.mistake j z s (ρ s) (x s) (y s) Z) i∂P.pillars j) atTop (𝓝 0):=by
 let x'(s:ℕ):=hat P.par.R.L P.par.x s; let b:= p₀; let c:=2+2*b
 have hd(s:ℕ):0<ρ s:=p s; let t(s:ℕ):=ρ s^8
 have hs(v:ℝ)(s:ℕ): t s * trailℓ (-v) (x' s)= ρ s^8/trailℓ v (x' s):=by unfold trailℓ; rw [div_eq_mul_inv,coin_inv,neg_zero]
 have ha:Tendsto (fun s=>ρ s^8/trailℓ A (x' s)) atTop (𝓝 0):=by
    have hu:Tendsto (fun s=>trailℓ (v-A) (x' s)) atTop (𝓝 0):= (coin_purchases (a:=0) (b:=v-A) (c:=0) (Or.inr (Or.inl ⟨rfl,by linarith⟩))).comp (turnover P.par)
    have he:= V.mul hu; rw [zero_mul] at he; refine he.congr fun s=>?_; change ρ s^8/_*_=_; rw [← hs,← hs,mul_assoc, shore_mul, show -v+(v-A)= -A from by ring] -- unification x'
 have hct:Tendsto (fun s=> t s * (c * trailℓ (-v) (x' s))) atTop (𝓝 0):= by
    have e:= V.mul_const c; rw [zero_mul] at e; refine e.congr fun i=> ?_; change ρ i^8/ trailℓ v (x' i)*_= _; rw [←hs]; ring
 apply Metric.tendsto_nhds.mpr; intro ε hε
 filter_upwards [hct.eventually (gt_mem_nhds (show 0< ε/2 from half_pos hε)), mPowered P.run z P.large P.law p zR hv hw ha (ε/2) (by positivity),P.pulse_road j z A v v₀ Q' h0 u h,Y0] with s hc h X T
 let T':ℂ:= (ρ s:ℂ)^8; have ht: ‖T'‖= t s:=by unfold T' t; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (hd s).le]
 -- R/ψ etc
 let μ0:= P.pillars j; let S':= P.mistake j z s (ρ s) (x s) (y s) Z; let f:=P.pulseQ j z s (x s) (y s); let e:= P.idealQ z s A (x s) (y s); let z':= P.wagerQ z s Z; have hx:‖T'*e-z'‖≤ ε/2:=by unfold Horo at h; push_cast at h; exact h
 have hI(t:P.Spectrum0 j→ℝ)(h:Continuous t):Integrable t μ0:=h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hg: (∫ i,S' i ∂ μ0) ≤ ∫ i,t s*‖f i-e‖+‖T'*e-z'‖∂ μ0:=by
     refine integral_mono (hI _ (P.mistake_live j z s _ _ _ _)) (hI _ ((continuous_const.mul (((P.pulseq_live j z s _ _).sub (show Continuous (fun _:(P.Spectrum0 j)=> e) from continuous_const)).norm)).add continuous_const)) fun i=> ?_
     change ‖T'*f i-_‖≤_; refine (norm_sub_le_norm_sub_add_norm_sub _ (T'*e) _).trans_eq ?_; rw [←mul_sub,norm_mul,ht]
 simp only [Real.dist_eq,sub_zero]; change |∫ i, S' i ∂ μ0| < ε; rw [abs_of_nonneg (integral_nonneg (fun i=> norm_nonneg _))]; rw [integral_add (f:=fun i=> t s*‖f i-e‖) (hI _ (continuous_const.mul (((P.pulseq_live j z s _ _).sub continuous_const).norm))) (integrable_const _), integral_const_mul,integral_const,show μ0.real Set.univ=1 from probReal_univ,one_smul] at hg; linarith only [hg,mul_le_mul_of_nonneg_left (X _ _ T) ((norm_nonneg _).trans_eq ht),hc,hx] -- norm ht syntax
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.mistake_go
