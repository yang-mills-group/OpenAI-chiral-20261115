import SatinThinSyllabus
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
private lemma universal_cost (t:ℝ) {μ0 :Measure (P.Spectrum0 j)} [IsProbabilityMeasure μ0]
    {X Y Z:P.Spectrum0 j→ℂ}{x y z':ℂ}{S:ℝ}(g:0<t)(h:Continuous X)(p:Continuous Y)(q:Continuous Z)
    (f:‖x‖≤ S)(f':‖y‖≤ S)
    (v:(∫ i, ‖X i-x‖^2∂μ0)≤ t^2)(u:(∫ i, ‖Y i-y‖^2∂μ0)≤ t^2)(u':(∫ i, ‖Z i-z'‖^2∂μ0) ≤ t^2) :
    (∫ i, ‖(Z i-X i *Y i)-(z'-x*y)‖∂μ0) ≤ (1+2*S)*t+t^2:= by
    have hs:0≤S:=(norm_nonneg _).trans f
    let B':=P.Spectrum0 j
    let F(A:B'→ℂ)(a:ℂ)(x:B'):= ‖A x - a‖
    let A:= F X x; let B:= F Y y; let C:=F Z z'
    have pS (A:B'→ℝ)(h:Continuous A): Integrable A μ0:= h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have ph(V:B'→ℂ)(v:ℂ)(q:Continuous V):Continuous (F V v):= (q.sub continuous_const).norm; -- period case
    have hp(V:B'→ℂ)(z:ℂ)(p:Continuous V)(X:(∫ i,(F V z i)^2∂μ0)≤t^2): (∫ i,F V z i∂μ0)≤ t:= by
       let Ay:= F V z; have he: (∫ i: B',2*t*Ay i∂μ0) ≤∫ i: B', (Ay i)^2+t^2∂μ0:=integral_mono (pS _ (continuous_const.mul (ph _ _ p))) (pS _ (((ph _ _ p).pow 2).add continuous_const)) fun i=> show 2*t*_≤ _ by nlinarith only [sq_nonneg (Ay i-t)] -- syntactic
       rw [integral_const_mul,integral_add (f:=fun i=> (Ay i)^2) (g:=fun _=>t^2) (pS _ ((ph _ _ p).pow 2)) (integrable_const _),integral_const,probReal_univ,one_smul] at he
       change (∫ i, (Ay i)^2∂μ0)≤_ at X; refine le_of_mul_le_mul_left (?_ : 2*t* (∫ i,Ay i∂μ0) ≤ 2*t*t) (by positivity : 0<2*t); linarith only [he,X]
    let K':= fun i=> ‖(Z i-X i*Y i)-(z'-x*y)‖; refine (integral_mono (pS K' (by unfold K'; fun_prop)) (pS (fun i=> C i+(A i+B i)*S+((A i)^2+(B i)^2)/2) ((((ph _ _ q).add (((ph _ _ h).add (ph _ _ p)).mul continuous_const))).add (((((ph _ _ h).pow 2).add ((ph _ _ p).pow 2))).div_const _))) (fun i=>?_)).trans (?_)
    · change ‖(Z i-X i*Y i)-(z'-x*y)‖≤_; rw [show (Z i-X i*Y i)-_= (Z i-z')- ((X i-x)*y+(Y i-y)*x) - (X i-x)*(Y i-y) from (by ring)]; refine (norm_sub_le ..).trans ((add_le_add (norm_sub_le ..) le_rfl).trans ?_); refine (add_le_add_left (add_le_add_right (norm_add_le ((X i-x)*y) ((Y i-y)*x)) _) _).trans (?_); simp only [norm_mul]; change C i+(A i*_+B i*_)+A i*B i≤_; nlinarith only [mul_le_mul_of_nonneg_left f (show 0≤B i from norm_nonneg _),mul_le_mul_of_nonneg_left f' (show 0≤A i from norm_nonneg _),sq_nonneg (A i-B i)]
    rw [integral_add (f:=fun i=>C i+(A i+B i)*S) (g:=fun i=> (A i^2+B i^2)/2) (pS _ ((ph _ _ q).add (((ph _ _ h).add (ph _ _ p)).mul continuous_const))) (pS _ ((((ph _ _ h).pow 2).add ((ph _ _ p).pow 2)).div_const _)), integral_add (f:=C) (g:=fun i=> (A i+B i)*S) (pS _ (ph _ _ q)) (pS _ (((ph _ _ h).add (ph _ _ p)).mul continuous_const)), integral_mul_const, integral_add (f:=A) (g:=B) (pS _ (ph _ _ h)) (pS _ (ph _ _ p)), integral_div,integral_add (f:=fun i=> (A i)^2) (g:=fun i=> (B i)^2) (pS _ ((ph _ _ h).pow 2)) (pS _ ((ph _ _ p).pow 2))]
    have he: (∫ i,A i∂μ0)+(∫ i,B i∂μ0)≤ t+t:= add_le_add (hp X _ h v) (hp _ _ p u)
    change _≤_; change (∫ i,(A i)^2∂μ0)≤_ at v; change (∫ i,(B i)^2∂μ0) ≤ _ at u; have hu:(∫ i,C i∂μ0)≤t:= hp _ _ q u'; linarith only [mul_le_mul_of_nonneg_right he hs,v,u,hu] -- name collision μ0
abbrev tariffQ (x:Cover):= P.visitLedger z (loneTrip x) s
abbrev tariffM (x y: Cover):= P.visitLedger z (twinTrip x y) s
-- normalized at witness. all on this character, not asserting separation at any s in this lemma.
abbrev pulseQ (x y: Cover)(u:P.Spectrum0 j):= P.singleState j s u (P.tariffM z s x y)-P.singleState j s u (P.tariffQ z s x)*P.singleState j s u (P.tariffQ z s y)
noncomputable abbrev idealQ (x y:Cover):ℂ:=(P.parish z (twinTrip x y) s A:ℂ)-(P.parish z (loneTrip x) s A:ℂ)*(P.parish z (loneTrip y) s A:ℂ)
theorem panel_live (x:P.Test) : Continuous (fun u:P.Spectrum0 j=> P.singleState j s u x):= P.chi_joint j (P.reading j s x)
lemma pulseq_live (x y: Cover): Continuous (P.pulseQ j z s x y):= (P.panel_live j s _).sub ((P.panel_live j s _).mul (P.panel_live j s _))
local notation "p₀"=> Yoke.paperN (P:=P.par) z
variable {Cε:ℝ}(Q':∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost Cε P.run s i k)
include Q'
theorem pulse_road (h0:13+2*v < A) (u:0< v) (h:v₀> 6*A+2*v) :∀ᶠ s:ℕ in atTop, ∀ (x y:Cover),CoversT (twinTrip x y) (scout P.par v₀ s) →
   (∫ i, ‖P.pulseQ j z s x y i-P.idealQ z s A x y‖∂P.pillars j) ≤ (2+2*p₀)*trailℓ (-v) (hat P.par.R.L P.par.x s):=by
 let t(s:ℕ):= trailℓ (-v) (hat P.par.R.L P.par.x s); have ht(s):0<t s:= trainℓ ..
 let X:= P.Spectrum0 j
 filter_upwards [P.variance_cost_at (I:=Bool) j z A (2*v) v₀ Q' (by norm_num; linarith only [h0]) (by positivity) (by norm_num; linarith only [h]) (pairedN (P:=P.par) z),P.variance_cost_at (I:=Unit) j z A (2*v) v₀ Q' (by norm_num; linarith only [h0]) (by positivity) (by norm_num; linarith only [h,h0,u]) p₀, (shrinkT (P:=P.par) u).eventually (ge_mem_nhds zero_lt_one)] with s h u v' x y f
 have he(w k:Cover):= lift_priceΩ P.run z P.large A P.law s w k; have hc(w):= lift_priceZ P.run z P.large A P.law s w; let a:=t s; have hz0:a^2=trailℓ (-(2*v)) (hat P.par.R.L P.par.x s):=by unfold a t; rw [sq,shore_mul]; ring_nf
 have hx0(x:Cover):= show ‖(P.parish z (loneTrip x) s A:ℂ)‖≤ p₀ from (by rw [Complex.norm_real,Real.norm_eq_abs]; exact hc x)
 have h1(x:Cover)(z':CoversT (loneTrip x) (scout P.par v₀ s)): P.stipend j s (P.tariffQ z s x) (P.parish z (loneTrip x) s A:ℂ)≤ a^2 := (u _ z' (hc x)).trans_eq hz0.symm
 refine (universal_cost P j a (μ0:=P.pillars j) (ht s) (P.panel_live j s _) (P.panel_live j s _) (P.panel_live j s _) (hx0 x) (hx0 y) (h1 x (fun _ v=> f true v)) (h1 y fun _ v=> f false v) ((h _ f (he x y)).trans_eq hz0.symm)).trans (?_)
 have h:v^2≥0:=sq_nonneg _; change _≤_*a; have h:a≤1:=v'; nlinarith only [mul_le_mul_of_nonneg_left h (ht s|>.le)] -- invocation
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pulse_road
