import YM.SU5.Assay.Sampler
import YM.SU5.Assay.Stirred
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
open MacroGrid
/-!
 MacroRiemann test (on each axis and arbitrary x; comes with Register).
-/
def Gridded :Prop:=∀f:Vantage→H,HasCompactSupport f→ Continuous f→
 Tendsto (fun i=>poseApprox (H) f (P.truck j x ∘ P.vtile i) (P.macroStep i)) atTop
   (𝓝 (E (∫a,W a (R (f a)))))
lemma advocate_roundtrip (k:Axis): P.advocate k (P.advocate j x k) j=x:=by
 ext b
 change P.chi j (P.otherSpectrum k j (P.otherSpectrum j k x)) b=P.chi j x b
 rw [P.translates,P.translates,P.migrate_reverse]
lemma metered (r:P.Register) :P.Gridded j x:=by
 rw [←P.advocate_roundtrip j x 3]
 exact P.macroRiemann _ _ (P.ellisP 3 (P.advocate j x 3) r).some

/- Proof for fixed unaligned sampler. -/
local notation "σ"=>P.sampler j x
local notation "κ"=>P.stirred j x
local notation "M"=>P.stirring j x
variable (t:ℕ)(F:SampleDose)(u:Vantage→(P.ColorHil j x).Op)(b:(P.ManyF j x).space)
private abbrev ray (y:Vantage):H:=u y (E (W (-y) b))
private abbrev rayon (y:Vantage):H:= Pan F.val u y (E (W (-y) b))
local notation "D"=> ray P j x u b
local notation "ξ"=> rayon P j x F u b
lemma sampler_rehearsing:
 σ t F u (E b)=poseApprox (H) (ξ) (P.truck j x ∘ P.vtile t) (P.macroStep t):=by
 have h:=P.activates F t (H) D (P.truck j x ∘ P.vtile t)
 refine Eq.trans ?_ h.symm
 unfold sampler
 rw [_root_.sum_apply]
 refine Finset.sum_congr rfl fun i w=>?_
 simp only [_root_.smul_apply,Function.comp_apply,charter,ContinuousLinearMap.comp_apply,P.cart_and,P.lays_neg]
 rfl
lemma sampler_shows {C:ℝ}(q:P.Gridded j x)(h:AtPan F.val u)(v:PanC F.val u C):
 Tendsto (fun i=> σ i F u (E b)) atTop (𝓝 (E (κ F u b))):=by
 have a:HasCompactSupport (ξ):= F.budget.mono (by
    intro i t e; apply t
    change Pan F.val u i (E (W (-i) b))=0 -- should be Pan applied. change explicitly
    rw [pan_dry _ e]; rfl)
 have z:Continuous (ξ):= by
    refine continuous_iff_continuousAt.mpr fun y=> (AtPan.contour F.smooth.continuous h y).apply' ?_
    exact ((E).continuous.tendsto _).comp ((P.cart_pin' j x (continuous_neg.tendsto y)).showAt b)
 have g:κ F u b=∫y,W y (R (ξ y)):=by
    rw [P.stirred_read _ _ h v b]
    refine integral_congr_ae (Eventually.of_forall fun y=>?_)
    simp only [rayon,Pan,_root_.smul_apply,map_smul]
    rfl
 rw [g];simp only [P.sampler_rehearsing]
 exact q _ a z
lemma sampler_rehearses {C:ℝ}(q:P.Gridded j x)(h:AtPan F.val u)(v:PanC F.val u C)(w:0≤C):
 P.Rehearses j x (fun i=>σ i F u) atTop (κ F u):=by
 refine ⟨P.sampler_cap _ _ _ _ w v,(fun b=>P.sampler_shows _ _ _ _ b q h v),?_⟩ -- eta tune
 simp only [P.sampler_star,P.stirred_turn _ _ h v]
 exact fun b=>P.sampler_shows _ _ _ _ b q (P.stirring_turn _ _ h) (P.stirring_turnC _ _ v)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
