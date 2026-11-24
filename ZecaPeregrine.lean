import ZecaWindhover
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
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
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster





open _root_.YM.ZecaSky


-- Copy prices. All poses here allow Corner/half. Taking b-variable β list.
variable {b:Axis} (hb:b≠3) (p:Plume_LocalFieldBounds){a c e:ℝ}
local notation "O"=>Option (brig a c)
variable {Y:ℕ→P.Apron}{seq:ℕ→ℕ}
 {F:P.Nib 3 (P.advocate 3 x 3)}
 {sc:ℕ→ℂ}
 (m:P.Mach x F sc seq)
 (W₀:5∣ P.par.R.L.val)
 (T:P.Nepenthe seq x)

-- abbreviations, one ε price
def culls {H:Hilbert}(e:ℝ) (D:Finset (brig a c)) (g:brig a c→ℝ)
 (z:ℕ→ℝ) (v:ℕ→Option (brig a c)→H):Prop:=
 ∀ᶠ n:ℕ in atTop,‖v n none - ∑ k∈D,
    ((g k:ℂ)*drift (z n) (beam5 a c k)) • v n (.some k)‖< e



include m W₀ T
theorem aloft (f:ℕ) (h:P.aboveRoof p)(s:0≤a)(v:a<c)(r₀:0<e)
 {σ:Type}[Finite σ] (β:σ→ℝ):
 ∃ (D:Finset (brig a c))(g:brig a c→ℝ),
   (∀ᶠ n:ℕ in atTop,
       P.flagging (a:=a) (c:=c) x f hb p none (seq n) ∧
       ∀i∈D,P.flagging x f hb p (.some i) (seq n)) ∧
   (∀ i:σ,∀ z:ℕ→ℝ,Tendsto z atTop (𝓝 (β i))→
      culls (H:=M) e D g z (fun n k=>P.singer x f (falling hb p k) (seq n)) ∧
      culls (H:=G) e D g z (fun n k=>P.kestrel x F sc (falling hb p k) (seq n))):=by
 have j:1≤p.tar:=by
   unfold aboveRoof at h; exact le_trans
    (show 1≤(P.roof:ℝ)+2 by linarith [Nat.cast_nonneg' (α:=ℝ) P.roof]) h
 let A:σ→ZecaSky.Spot:= fun i=>⟨b,p.tar,β i⟩
 obtain ⟨D,g,o⟩:= geminate.{0,0} z' SU.group A (fun _=>⟨j,hb⟩) s v r₀
 refine ⟨D,g, ?_, fun i z d=>⟨o i _ (P.skiffM (f:=f) x hb W₀ T p) z d,
                            o i _ (P.skiffG x hb m p h) z d⟩⟩
 apply (T.sky.eventually (P.flagged (f:=f) x hb p none W₀)).and
 exact D.eventually_all.mpr fun i _=> T.sky.eventually (P.flagged x hb p (.some i) W₀)
#check @aloft
#check @flagged

#print axioms aloft
omit m W₀ T
/-- specialization to a phase charged in physical displacement units:
take β=0 in the theorem (Sky from Nepenthe). -/
lemma aloft_phase (t:Tendsto seq atTop atTop) (u:ℝ):
 Tendsto (fun n=>u*P.jetS (seq n)) atTop (𝓝 0) ∧
 ∀ n d,drift (u*P.jetS (seq n)) d = drift u (P.jetS (seq n)*d):=by
 constructor
 · simpa only [mul_zero,Function.comp_apply] using (P.jetS_go.comp t).const_mul u
 intro n d; unfold ZecaSky.drift; congr 1; push_cast; ring
