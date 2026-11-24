import YM.SU5.SatinWard.Resolution.WalletW
import YM.SU5.SatinWard.Resolution.TopazLap
import YM.SU5.SatinWard.Resolution.SageTicket
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
local instance (priority:=high) iAmiceColorHil(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ColorHil i x).Op:=opRn (P.ColorHil i x)
local instance (priority:=high) iAmiceManyF(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ManyF i x).Op:=opRn (P.ManyF i x)
open Rotunda
omit k7
local notation "ℓ" v:max=> moonClock P v
local notation "p☾" => sprintCost P.par.R.L
local notation "h☾" => unitX P
local notation "F☾"=> capitalize P pHw e mu q M K p i x z
lemma tariff₁ (v:ℕ)(u:f0<v): ‖(v★ v) z‖ ≤ (h☾)^v * ‖z‖:= κgrow P _ pHw e K z u
lemma studioJ (hv:f0≤ v) (u:ℓ (v+1) ≤ l)(w:ℓ (v+1)≤r): ‖F☾ (v+1) l r‖ ≤ (|birthBudget η| *‖z‖)*(h☾)^(v+1) := by
 have e' := hv.trans (Nat.le_succ _); rw [capPay P pHw e mu q M K p i x z e']; apply le_trans (can_fee P pHw e mu q M K p i x ((v★ (v+1)) z) W hv u w e'); rw [mul_right_comm _ _ ((h☾)^_)]; exact (mul_le_mul (le_abs_self _) (tariff₁ P M z pHw W e K _ (by omega)) (norm_nonneg _) (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm -- tariff args maybe
#check @tariff₁
lemma staircaseJ : ∃ C:ℝ,0≤ C∧UnpadTicket.Climbed (moonClock P) (f0+1) (F☾) (h☾) C:=by
 obtain ⟨d,c,h,ppc,f⟩:= gauges P η M mu W
 apply UnpadTicket.climbing (sprint_pos _) (unit_live _) (stampLoss P M W) (|birthBudget η| *‖z‖) (c*‖z‖) (by positivity) (by positivity) (fun _ _ u v=>loans_le P W.tally ((Nat.le_succ f0).trans u) v)
 · rintro (_|v) hi l r hl hr; · omega
   exact studioJ P q p M z i x mu pHw W e K (Nat.le_of_succ_le_succ hi) hl hr
 · intro s v hs hv l r hl hr
   refine (linkNext P pHw e mu q M K p i x z W ((Nat.le_succ _).trans hs) hl hr hv).trans ?_; let u':= tariff₁ P M z pHw W e K v (by omega)
   rw [(f s v).2]; have ht:0≤lapQ P.run s:= (W.tally.date.stock s (by omega)).1.1.le; have hx:lapQ P.run s≤1:= (W.tally.date.stock s (by omega)).1.2
   refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right ppc.le hx) (inv_nonneg.mpr (pow_nonneg (sprint_pos _).le _))) (norm_nonneg _)) ((mul_le_mul_of_nonneg_right u' (mul_nonneg ppc.le (inv_nonneg.mpr (pow_nonneg (sprint_pos _).le _)))).trans_eq ?_); ring
local notation "A◇"=> freshF P i (-home P q f0) x
lemma paid_origin (u:f0 ≤ v): (cap x v) l r= A◇ (F☾ v l r):= (eu_x P pHw e mu q M K p i x z u).symm
lemma primJ (u:f0 ≤ v):(P.seasons i x).Credits (ℓ v) (cap x v):=by intro a b c d y zz f g; rw [paid_origin P q p M z i x mu pHw W e K u, paid_origin P q p M z i x mu pHw W e K u, capPay P pHw e mu q M K p i x z u, capPay P pHw e mu q M K p i x z u,charm_lag P mu q M p i x u _ W u y zz f g, freshCutt,P.reprise_sand,P.locate_sand]; rfl
lemma summitJ : ∃ C:ℝ,0≤ C∧UnpadTicket.Climbed (moonClock P) (f0+1) (realFreshF P pHw e mu q M K p i x z) (unitX P) C:=by -- partial notation
 obtain ⟨c,h,p₂⟩:= staircaseJ P q p M z i x mu pHw W e K; refine ⟨c,h,fun s v hv hs l r hl hr=>?_⟩; rw [paid_origin P q p M z i x mu pHw W e K (by omega), freshCutt,P.locate_cost]; exact (P.reprise_pay ..).trans (p₂ s v hv hs l r hl hr)
#print axioms summitJ
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
