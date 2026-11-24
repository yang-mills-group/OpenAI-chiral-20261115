import ZecaPuddle
import ZecaWebfoot
import ZecaWren
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





open SatinNucleus Germ Alliance
variable
 (F:P.Nib 3 (P.advocate 3 x 3)){A C:ℝ}
 {u:ℕ→ℕ}(uf: StrictMono u) (y:ℕ→ℕ×ℕ→ℝ)(z:ℕ→ Coalition)
local notation "c"=>P.rewardK f k
local notation "Y"=> P.cinema x f k u y z uf
local notation "ρ" i:max=> (↑(P.rewardK f k * y i (f,k)):ℂ)
local notation "Lsky"=> Skyways P f k A C c u y


local notation "m" r:max=>P.pointEra r
lemma tileLess
    (h:NibLine P 3 ξ F Y 1) (k1:Lsky) (e:P.NightCop)
    (j0:P.MyJet x F):
 ∃ c₁:ℕ→ℂ,
 (∀ᶠ r:ℕ in atTop,c₁ r ≠ 0) ∧
 P.Nick f x F c₁ (P.inkLoss A):=by
 choose rent hr using k1.sold
 let R:=fun r=>rent (m r,r)
 have wr(r:ℕ):0<P.rosePad 3 (m r):=mul_pos
     (Nat.cast_pos.mpr (by unfold roseWide roseFlat; omega))
     (P.macroStep_pos _)
 let d:=fun r=>(P.plumeK r:ℂ)/(R r:ℂ)
 suffices t: ∀ᶠ r:ℕ in atTop, d r≠ 0 ∧ ∀a b,P.rosePad 3 (m r)≤a→P.rosePad 3 (m r)≤b→
   ‖d r • F a b - (P.plumeK r:ℂ) • P.crop 3 x f r [] a b‖≤P.inkLoss A r from
      ⟨d,t.mono fun _=>And.left,t.mono fun _=>And.right⟩
 filter_upwards [
   P.future_payment.eventually (eventually_ge_atTop k),
   P.future_payment.eventually (P.rose_license 3),P.payment_late,P.plume_pos]
   with r ke le gr pos
 let pad:=P.rosePad 3 (m r)

 have v(a b:ℝ)(pa:pad≤a)(pb:pad≤b): dist (F a b) ((R r:ℂ) • P.crop 3 x f r [] a b)
       ≤ ‖(R r:ℂ)‖ * (4 * violet P.par (m r) A) / zoomM P.par.R.L^(r-(m r)):=
   P.downRipple x F uf y z h k1 e ((wr r).trans_le pa) ((wr r).trans_le pb) pa pb
      (le f []) ke gr.2.1 (hr (m r,r))

 have q:R r≠0:=by
   intro b
   have t:=v pad pad le_rfl le_rfl
   rw [b,Complex.ofReal_zero,norm_zero,zero_mul,zero_div,
        zero_smul,dist_zero_right] at t
   apply j0 pad pad (wr r) (wr r)
   rw [norm_le_zero_iff.mp t];rfl

 have u:(R r:ℂ) ≠ 0:=by exact_mod_cast q
 exact ⟨div_ne_zero (show (P.plumeK r:ℂ)≠0 from by exact_mod_cast pos.ne') u,
    fun a b p t=>rescaleNick (v a b p t) q pos.le⟩
#print axioms tileLess

