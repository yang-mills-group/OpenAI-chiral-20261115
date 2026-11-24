import YM.SU5.Regis.Ardent
import YM.SU5.Circuit.Concert
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
variable (P:Spine)
abbrev artist := Papal.Aster P.run P.period P.cutoff
def connPower (s:ℕ)(g:P.Test→ℂ)(f j:P.Test)(R:ℝ):ℂ:= (P.artist s:ℂ)^(-4:ℤ) *((R:ℂ)^8*(g (f*j)-g f*g j))
lemma artRange (s:ℕ): P.artist s∈Set.Icc (1/2:ℝ) 2:= (Papal.astral ..).1
-- polynomial estimate on repetitions using same tested values, normalize by one shared projected program price.
variable (F D:PlaqAxes){R t:ℕ→ℝ}{U W:ℕ→ Cover}{X:Gaia}
variable (u:∀ i,0<R i)(w:Tendsto R atTop atTop)(Z:Tendsto (fun i=>riseX (R i) (U i-W i)) atTop (𝓝 X))(j:X≠0)(f:∀ i,0<t i)(p:Tendsto (fun i=>R i^8/t i) atTop (𝓝 0))
def standardGauge(F:PlaqAxes)(U:ℕ→ Cover){t:ℕ→ℝ}(f:∀ i,0<t i)(i:ℕ): Etch SU.group Unit:=blazing SU.group F (U i) (t i) (f i)
local notation "φ" i:max=> standardGauge F U f i
local notation "χ" i:max=> standardGauge D W f i
local notation "δ"=>spectrumColor F D SU.group X
variable {β γ:ℝ}
def ballotK(R t:ℕ→ℝ)(i:ℕ) :ℝ:=min 1 (keyV i / (R i^8*(2*t i+2))) -- keyV
include u f in
lemma ballot_pos(i:ℕ) :0<ballotK R t i:=by unfold ballotK; have he:=u i; have hz:=f i; exact lt_min zero_lt_one (div_pos (keyV_positive i) (by positivity))
-- notations
variable {c:ℕ→ℕ}
local notation "ξ"=>ballotK R t
local notation "pα" i:max=> P.view (φ i) (c i)
local notation "pβ" i:max=> P.view (χ i) (c i)
local notation "qq" i:max=> (P.artist (c i):ℂ)
variable {V:ℕ→P.Test→ℂ}
private lemma ropeCost (a b c A B C:ℂ)(u t:ℝ)(v:0≤u)(k:u≤1)(p:‖a-A‖≤u)(p':‖b-B‖≤u)(pA:‖c-C‖≤u)(kA:‖A‖≤t)(kB:‖B‖≤t): ‖(c-a*b)-(C-A*B)‖≤ u*(2*t+2):=by
 have ht:‖a‖≤t+1:= (norm_le_norm_sub_add ..).trans ((add_le_add (p.trans k) kA).trans_eq (add_comm 1 t))
 have he: ‖a*b-A*B‖≤u*(2*t+1):=by
    rw [show a*b-A*B=a*(b-B)+(a-A)*B from (by ring)]
    exact (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul ht p' (norm_nonneg _) ((norm_nonneg _).trans ht))) ((norm_mul_le ..).trans (mul_le_mul p kB (norm_nonneg _) v))).trans_eq (by ring))
 exact (le_trans (by rw [show _-(C-A*B)=c-C-(a*b-A*B) from (by ring)]; exact norm_sub_le (c-C) (a*b-A*B)) ((add_le_add pA he).trans_eq (by ring)))
local notation "Fx" i:max=>P.tapestryRate (φ i) (c i)
local notation "Gx" i:max=>P.tapestryRate (χ i) (c i)
local notation "Tx" i:max=> P.tapestryRate ((φ i).radial (χ i)) (c i)
def imageGauge (c:ℕ→ℕ)(F D:PlaqAxes)(R:ℕ→ℝ){t:ℕ→ℝ}(U W:ℕ→ Cover)(f:∀ i,0<t i)(J:ℕ→P.Test→ℂ):Prop:= ∀ᶠ i in atTop, ‖J i ((P.view (standardGauge F U f i) (c i)))-(P.tapestryRate (standardGauge F U f i) (c i):ℂ)‖ ≤ ballotK R t i ∧ ‖J i ((P.view (standardGauge D W f i) (c i)))-(P.tapestryRate (standardGauge D W f i) (c i):ℂ)‖ ≤ ballotK R t i ∧ ‖J i ((P.view (standardGauge F U f i) (c i)) * (P.view (standardGauge D W f i) (c i)))-(P.tapestryRate ((standardGauge F U f i).radial (standardGauge D W f i)) (c i):ℂ)‖ ≤ ballotK R t i -- hygiene notation local binds f F etc? check
include u w Z f j p
lemma poet (tome:imageGauge P c F D R U W f V): Tendsto (fun i=>P.connPower (c i) (V i) (pα i) (pβ i) (R i)) atTop (𝓝 (δ)):=by
 let K(i:ℕ):=(R i:ℂ)^8; let I(i):= V i (pα i * pβ i) - V i (pα i)*V i (pβ i); let O(i):= (Tx i:ℂ)-(Fx i:ℂ)*(Gx i:ℂ)
 have ht(i): ‖K i‖= R i^8:=by unfold K; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (u i).le]
 let Dn(i):= qq i; have hx(i): (1/2:ℝ)≤‖Dn i‖:= (P.artRange (c i)).1.trans (by unfold Dn; rw [Complex.norm_real]; exact le_abs_self _) -- norm coe
 have hy(i):0<‖Dn i‖:=by specialize hx i; linarith
 have hz(i): ‖(Dn i)^(-4:ℤ)‖≤ 16:=by rw [norm_zpow,_root_.zpow_neg,zpow_ofNat,inv_le_comm₀]; exacts [by have h:=hx i; apply le_trans _ (pow_le_pow_left₀ (by positivity) h 4); norm_num,by have hp:=hy i; positivity,by have hp:=hy i; positivity] -- tune
 refine Metric.tendsto_nhds.mpr fun e he=>?_
 filter_upwards [tome,Papal.imagery P.run P.large P.law F D u w Z j f p (e/64) (by positivity), keyV_go.eventually (gt_mem_nhds (show 0<e/32 by positivity))] with i h p h' -- tune gt_mem? 
 change dist ((Dn i)^(-4:ℤ)*(K i*I i)) δ < _; have b:0<(ξ) i:=ballot_pos u f i
 have hw: ‖I i-O i‖ ≤ (ξ) i*(2*t i+2):= ropeCost _ _ _ _ _ _ _ _ b.le (min_le_left ..) h.1 h.2.1 h.2.2 ((Complex.norm_real _).trans_le (show |P.tapestryRate _ _| ≤ _ from P.budgetMark (φ i) (c i))) ((Complex.norm_real _).trans_le (P.budgetMark (χ i) _))
 have h₁ : ‖K i*(I i-O i)‖ ≤ keyV i:=by
    rw [norm_mul,ht]; refine (mul_le_mul_of_nonneg_left hw (by positivity)).trans ?_; rw [show R i^8*(ballotK R t i*(2*t i+2))= ballotK R t i*(R i^8*(2*t i+2)) from (by ring)]
    refine (le_div_iff₀ ?_).mp (min_le_right ..); have _p:=f i; have _v:=u i; positivity
 have h₂: ‖K i*O i-(Dn i)^4*δ‖ ≤ e/64:=by specialize p (c i); unfold Papal.Horo at p; push_cast at p; exact p
 have hh: ‖K i*I i-(Dn i)^4*δ‖ ≤ keyV i+e/64:=by
    rw [show K i*I i-(Dn i)^4*δ=K i*(I i-O i)+(K i*O i-(Dn i)^4*δ) from (by ring)]; exact (norm_add_le ..).trans (add_le_add h₁ h₂)
 rw [dist_eq_norm, show _-δ=(Dn i)^(-4:ℤ)*(K i*I i-(Dn i)^4*δ) from (by rw [_root_.zpow_neg,zpow_ofNat,mul_sub _ (K i*I i) ((Dn i)^4*δ),inv_mul_cancel_left₀ (pow_ne_zero _ (norm_pos_iff.mp (hy i)))])]
 apply lt_of_le_of_lt ((norm_mul_le ..).trans (mul_le_mul (hz i) hh (norm_nonneg _) (by norm_num))); have hv:keyV i< e/32:= h'; linarith
where de(X:ℝ):X=X:=rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.poet
