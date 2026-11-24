import ZecaBluejaw
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


variable (F:P.Nib 3 (P.advocate 3 x 3))(sc:ℕ→ℂ)

abbrev pelican (p:Vantage) (r:ℕ):G:=
 Γ ((P.jetS r) • p) (P.kestrelSeed x F sc r (P.jetS r*(p 3)))

abbrev peck (p q:Vantage):ℂ:=
 Regis.Head.Brecht.spectrumℓ z' SU.group (collegia p q)

abbrev commRun (d:Vantage) (r:ℕ):=
 Γ ((P.jetS r) • d)
abbrev commRise (r:ℕ):=
 (Η).E (P.jetS r).toNNReal
local notation "χ" => P.pelican x F sc

lemma racing (b:P.Bottle 3 (P.advocate 3 x 3) F)
 {p d:Vantage}(u:0<p 3)(e:d 3=0):
 Race (P.commRun x d r) (P.commRise x r)
   (fun t l=> χ (reecho p d t l) r):=by
 constructor
 · intro t l
   unfold pelican
   rw [echo3,echo3,echoM _ e,smul_add,P.cart_paves]
   rfl
 intro t
 let y:=reecho p d (t+1) 0
 let z:=reecho p d t 0
 let h:=P.jetS r
 have a0:0<h:=P.jetS_pos r
 have a1:0<z 3:=by unfold z; rw [echo3]; positivity
 have a2:h*y 3-h*z 3=h:=by unfold y z; rw [echo3,echo3]; push_cast; ring
 have a3:=P.kestrel_scale (r:=r) x F sc b (h*z 3) (h*y 3)
    (by positivity) (show h*z 3≤h*y 3 from sub_nonneg.mp (le_trans a0.le a2.ge)) -- substitution h issues
 have a4:=of_slideP x 3 (h•y) (h•z)
         (fun i l=> congrArg (fun c:ℝ=>h • c) (echoT p d t l))
 rw [a2] at a3
 change (Η).E h.toNNReal (χ z r)=χ y r
 dsimp only [pelican]; rw [a4,P.warm_drive,a3]
#check @warm_drive
#check @lyric

variable (seq:ℕ→ℕ)(p d:Vantage)
def Reef : Prop :=
 ∀ t:ℕ,∀i j:ℤ,Tendsto (fun n:ℕ=>inner ℂ
    (χ (reecho p d t i) (seq n))
    (χ (reecho p d t j) (seq n)))
 atTop (𝓝 (peck (reecho p d t i) (reecho p d t j)))

/-- asymptotic spectrum estimate along displacement d. -/
def RV:Prop:= ∀ E q:ℝ,0≤E→E<q→
 ∀ e:ℝ,0<e→ ∀ᶠ i in atTop, ∀ m:G→ℝ,
 Bask (heartscale d) q E (P.commRun x d (seq i)) (P.commRise x (seq i)) m →
    m (χ p (seq i))<e

theorem reef_rv (b:P.Bottle 3 (P.advocate 3 x 3) F)
 (u:1≤2*p 3)(e:d 3=0)(h:d≠0)
 (m:P.Reef x F sc seq p d):
 P.RV x F sc seq p d:=by
 let w:=fun i t l=>χ (reecho p d t l) (seq i)
 have coast: fishing w (heartscale d)
   :=blenny («G»:=SU.group) (colA:=Yoke.witnessZ) (hunit h) (hflip e) u (hpos h)
    (fun t i j=> by dsimp only; rw [← rewakes p h t i j]; exact m t i j)
 intro E q y v η a
 have z:=eaglefin (U:=fun n=>P.commRun x d (seq n)) (V:=fun n=>P.commRise x (seq n))
    coast (fun n=>P.racing x F sc b (by linarith only [u]) e) y v a
 simpa only [w,echoZero] using z
#print axioms reef_rv
