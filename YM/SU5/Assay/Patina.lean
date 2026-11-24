import SatinFixedContrastNovember4
import YM.SU5.Assay.FloorService
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
local notation "B" M:max=> bay K M true
variable {k:ℤ}{Z U D:Finset Cover}{x:P.Spectrum0 j}{a n r l:ℕ}{d δ:ℝ}
local notation "Q"=> P.viewFrom j a n w k f
local notation "E"=> P.E s
local notation "W"=> P.singleState j s x
local notation "m₀"=> P.period
local notation "h₀"=> P.cutoff
local notation "A"=>P.sterling s
open Aria Six Germ Alliance Set
local notation "J"=> P.Test→ℂ
/-- Film of relative error on all marks charged here. Parametric in
 `j`; both orientations of the regulator calibration satisfy it. -/
def Patina (P:Spine)(j:Axis)(s:ℕ)(x:P.Spectrum0 j)(M:Set Vantage)(δ:ℝ)(X:P.Test→ℂ) : Prop:=
  ∀g:P.Test,P.asked_at s g M→∀e:ℝ,pay g.val e→ ‖X g-P.singleState j s x g‖≤δ*e
variable {M:Set Vantage}
local notation "β"=> P.Patina j s x M
variable {X:P.Test→ℂ} {h:ℕ→P.Test→ℂ} {ε:ℕ→ℝ}
lemma Patina.thicken {t:ℝ}(p:β δ X)(u:δ≤t):β t X:=
 fun m a' i y=> (p m a' i y).trans (mul_le_mul_of_nonneg_right u (pay_nonneg y))
lemma Patina.charged (p:Tendsto ε atTop (𝓝 0))(q:∀i,β (ε i) (h i))(v:P.asked_at s g M):
 Tendsto (fun i=>h i g) atTop (𝓝 (W g)):=by
 have u:=v
 obtain ⟨_,u,_⟩:=u
 obtain ⟨e,t⟩:=valuation Y H u
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 refine squeeze_zero (fun i=>norm_nonneg _) (fun i=>q i g v e t) ?_
 simpa only [zero_mul] using p.mul_const e
/-- Buy even a sequence-stable demand. No continuity assumed for the viewer! -/
lemma Patina.good {Pass:J→Prop}
 (p:∀v:ℕ→P.Test→ℂ,(∀g:P.Test,P.asked_at s g M→ Tendsto (fun i=>v i g) atTop (𝓝 (W g)))→ ∀ᶠ i in atTop,Pass (v i)):
   ∃u>0,∀X:P.Test→ℂ,β u X→Pass X:=by
 contrapose! p
 let ε :ℕ→ℝ:=fun n=>1/(n+1:ℝ)
 choose t e₁ v using fun n=>p (ε n) (by unfold ε; positivity)
 refine ⟨t,fun g y=>Patina.charged (ε:=ε) tendsto_one_div_add_atTop_nhds_zero_nat e₁ y,?_⟩
 intro r;obtain ⟨i,z⟩:=r.exists;exact z (v i)
-- Special case: pointwise price purchase on the whole shelf.
lemma Patina.wishes {I:Type*}(t:I→P.Test)(u:∀i,P.asked_at s (t i) M){D₀:Set (I→ℂ)}(y:D₀∈ 𝓝 (fun i=>W (t i))):
   ∃u>0,∀X:P.Test→ℂ,β u X→ (fun i=>X (t i))∈D₀:=Patina.good (Pass:=fun X=>(fun i=>X (t i))∈D₀) (fun v p=>
   (show Tendsto (fun i z=>v i (t z)) atTop _ from tendsto_pi_nhds.mpr fun j=> p _ (u j)).eventually y)
variable(p:P.FloorService j s x M k w Z n δ a f U D d)(e:P.Flight j s x k w Z n δ a f U D r l)
include p e in
/-- Film even when using the *original* regulator normalization,
 viewer included on all marks (unit as well). -/
lemma FloorService.film: β δ (fun g=>A r l (Q g)) ∧ β δ e.pressing:=
 ⟨fun _ t _ u=>(p.earned e t u).1, fun _ t _ u=>(p.earned e t u).2⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
