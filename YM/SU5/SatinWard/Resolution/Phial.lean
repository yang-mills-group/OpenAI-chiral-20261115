import YM.SU5.SatinWard.Resolution.WalletW
import YM.SU5.SatinWard.Resolution.TopazLap
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open MezzoBill
namespace Dovetail

/-! Same regulator convergence including external-lag powers before claiming WP. want uniform-li bound in v for both.T.Ages.Future. This module first finances reflection at stages used. -/
variable {v m:ℕ}(q:Cover)(p:ResidualPermit q)(M:P.par.R.L.val%16=1)(z:Soul)(i:Axis)(x:P.Spectrum0 i)(mu:Axis)
local notation "σ" v:max=> P.macroStep v
local notation "ℛ"=> P.locate i x
local notation "π"=> P.reprise i x
local notation "ℜ"=> P.charter i x
local notation "fee" i:max => home P q i
variable {s f0:ℕ}{Z:ℕ→ℕ}{C H A d c dσ:ℝ}{η:Type}[Fintype η](ρ:Piano P f0 C H A η Z) (q₂:payable P v 2)
local notation "q'"=> flipline i q
local notation "p'" => makesColor q p i
local notation "JV" u:max=> JpriceApp P q M p u mu v
local notation "Ju" u:max=> JpriceApp P (flipline i q) M (makesColor q p i) u mu v
local notation "K$"=> soloV P v q₂ q p pseV
local notation "K'"=> soloV P v q₂ (flipline i q) (makesColor q p i) pseV
local notation "φ♠"=> (↑(colorPay i mu):ℂ)
local notation "Uw"=> (kinWidth P:ℝ)*P.macroStep v
local notation "Uf"=> (choirWidth P:ℝ)*P.macroStep v
local notation "δ₀" v:max=> moonClock P v
variable (p₁:f0 ≤ v)(pHw:Tendsto Z atTop atTop)(W:HeartClock P f0 H A d c dσ P.jump128 M Z η)(e:Melodic P η A f0 Z)(K:P.NightCop)[Nonempty η]{l r:ℝ}
local notation "hℓ"=> home P q v
local notation "PS"=> pricedPSE P M i x p ρ
local notation "Px"=> pricedPSE P M i x (makesColor q p i) ρ
local notation "Tμ" v:max => psScale P ρ v
local notation "Cℓ" F:max => annoFace P i x v (home P q v) F
local notation "Ζℓ" F:max => annoFace P i x v (home P (flipline i q) v) F
local notation "v★" s:max=> trueKey P pHw e K s

local notation "Φ" x:max=> priceX P pHw e mu q M K p i x
local notation "Q"=> (P.Known) -- faux
local notation "εK" v:max=> (↑(psScale P ρ v):ℂ)
local notation "Ν" n:max=> (v★ n)
variable (k7:f0 ≤ s)
include W k7 e pHw K
local notation "cap" t:max v:max=> (realFreshF P pHw e mu q M K p i t z v)
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ColorHil i x).Op:=opRn (P.ColorHil i x)
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ManyF i x).Op:=opRn (P.ManyF i x)
open Rotunda
lemma nail : ∀ᶠ v:ℕ in atTop, ∀(q:Cover)(p:ResidualPermit q) (x:P.Spectrum0 i) (l r:ℝ),moonClock P s ≤ l→moonClock P s ≤ r→
 ‖realFreshF P pHw e mu q M K p i x z v l r-priceX P pHw e mu q M K p i x z l r‖ ≤ 1:=by
 obtain ⟨C,h,F⟩:=wrack_time P η M W k7; have hv:Tendsto (fun v:ℕ=> (P.macroStep v)^(15/8:ℝ)) atTop (𝓝 0):=by
    have i:= Tendsto.rpow P.macroStep_zero (tendsto_const_nhds (x:=(15/8:ℝ))) (Or.inr (by norm_num)); rwa [Real.zero_rpow (by norm_num)] at i
 let t:= ((hv.const_mul C).mul_const ‖z‖); rw [mul_zero, zero_mul] at t; filter_upwards [t.eventually (ge_mem_nhds zero_lt_one),eventually_gt_atTop s] with v b p'v q p x l r hl hr
 let g:= freshF P i (-home P q f0) x; let A':= cantabile P pHw e mu q M K p i x z l r; let X:= capitalize P pHw e mu q M K p i x z v l r; unfold realFreshF; rw [←eu_x P pHw e mu q M K p i x z (k7.trans p'v.le)]; change ‖g X-g A'‖≤ _; rw [← map_sub]; refine (stintR P i x _ _).trans (?_:‖X-A'‖≤1) -- wrong namespace?
 exact le_trans (spareL P η q p M z mu i x W k7 pHw e K p'v hl hr) ((mul_le_mul_of_nonneg_right (F _ p'v.le) (norm_nonneg z)).trans b)
lemma less_pose : ∃ C:ℝ,0<C ∧ ∀ (x:P.Spectrum0 i)(l r:ℝ),moonClock P s ≤ l→moonClock P s ≤ r→ ‖(Φ x) z l r‖≤ C:=by
 obtain ⟨B,h,u⟩:= tileRenew P η M W pHw e K; let C:=B*(unitX P)^s*‖z‖; have ht:0≤C:=by unfold C; have h0:1≤unitX P:=unit_live P; positivity
 refine ⟨1+C,by positivity,fun x l r a b=>?_⟩; unfold priceX; rw [P.locate_cost]; exact (P.reprise_pay ..).trans ((u s k7 q p i x mu z l r a b).trans (by exact le_add_of_nonneg_left zero_le_one)) -- infer
-- universal upper for both Phi and kappa pose.Teasible horizon.J γ input level.Nest. provide all peers and t x.
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
