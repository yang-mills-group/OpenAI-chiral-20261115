import YM.SU5.SatinWard.Resolution.WalletW
import YM.SU5.SatinWard.Resolution.ScaleW
import YM.SU5.SatinWard.Resolution.Corydalis
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


local notation "Tκ" v:max=> (↑(psScale P ρ v):ℂ)
local notation "Θκ" x:max=> pricedPSE P M i x p ρ
-- estimate use norm raw.cost base at some level, all widths, not v-dependent estimator later. keep for any fixed s.P. later temper.
-- uniform all n near claim. use metric stamp
local notation "Fξ" x:max=> heyC P q p i x ρ
variable (ht7:f0 ≤ s)
local instance (priority:=high) iSolanoColorHil(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ColorHil i x).Op:=opRn (P.ColorHil i x)
local instance (priority:=high) iSolanoManyF(P:Spine)(i:Axis)(x:P.Spectrum0 i):NormedSpace ℝ (P.ManyF i x).Op:=opRn (P.ManyF i x)
local notation "ℓ" v:max=> moonClock P v
local notation "p☾" => sprintCost P.par.R.L
local notation "h☾" => cloverFrame.pulseBase P.par.R.L
local notation "F☾"=>complect P M i x p ρ
local notation "ζ" v:max=> (↑(Tμ v):ℂ)
include ρ pHw K
lemma pfathy (hv:f0 ≤ v): |Tμ (v+1)| ≤ (h☾)^(v+1):=by
 have h:1≤(h☾):=by
    refine (unit_live P).trans ?_; unfold unitX; simp_rw [pulse_power]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ)≤ rota P.par.R.L from Nat.one_le_cast.mpr P.par.R.L.property) (show (3:ℕ)≤4 by decide)) receipt_pos.le
 have ht:psScale P ρ (f0+1)=1:=by simp [psScale]
 refine (scale_le P ρ (Nat.lt_succ_self _) (Nat.succ_le_succ hv)).trans ?_; rw [ht,abs_one,one_mul]; exact pow_le_pow_right₀ h (by omega)
lemma studioK (hv:f0≤ v) (u:ℓ (v+1) ≤ l)(w:ℓ (v+1)≤r): ‖F☾ (v+1) l r‖ ≤ (2*Real.exp 1)*(h☾)^(v+1) := by
 have e' := hv.trans (Nat.le_succ _); rw [cast_chime P M i x p ρ e',norm_smul,Complex.norm_real,Real.norm_eq_abs]; obtain ⟨a,d,h⟩:= (ρ.date.enough v hv).choose_spec -- structure check
 obtain ⟨Q,g⟩:= ρ.poses (v+1) e' q p; let B:=raw_fee P pHw ρ.date h M K i x p f0 Q g (ρ.pays (v+1) e') u w (ρ.date.stock (v+1) e').2 hv e'; exact (mul_le_mul (pfathy P ρ pHw K hv) B (norm_nonneg _) ((abs_nonneg _).trans (pfathy P ρ pHw K hv))).trans_eq (mul_comm _ _)
#check @raw_fee
lemma staircaseK : ∃ C:ℝ,0≤ C∧UnpadTicket.Climbed (moonClock P) (f0+1) (F☾) (h☾) C:=by
 obtain ⟨a,h,f⟩:=rhoUnit P ρ
 have ht:1≤(h☾):=by
    refine (unit_live P).trans ?_; unfold unitX; simp_rw [pulse_power]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ)≤ rota P.par.R.L from Nat.one_le_cast.mpr P.par.R.L.property) (show (3:ℕ)≤4 by decide)) receipt_pos.le
 apply UnpadTicket.climbing (sprint_pos _) ht ρ.date.fiscal.2.2.2.loss (2*Real.exp 1) a (by positivity) h.le (fun _ _ u v=>loans_le P ρ ((Nat.le_succ f0).trans u) v)
 · rintro (_|v) hi l r hl hr; · omega
   exact studioK P q p M i x ρ pHw K (Nat.le_of_succ_le_succ hi) hl hr
 · rintro s (_|v) hs hv l r hl hr; · omega
   have h' := heading P pHw M K i x p ρ ((Nat.le_succ f0).trans hs) hv hl hr; refine h'.trans ?_
   generalize_proofs; let u':= pfathy P ρ pHw K (v:=v) (by omega)
   rw [f]; have ht:0≤lapQ P.run s:= (ρ.date.stock s (by omega)).1.1.le; have hx:lapQ P.run s≤1:= (ρ.date.stock s (by omega)).1.2
   refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right h.le hx) (inv_nonneg.mpr (pow_nonneg (sprint_pos _).le _))) (abs_nonneg _)) ((mul_le_mul_of_nonneg_right u' (mul_nonneg h.le (inv_nonneg.mpr (pow_nonneg (sprint_pos _).le _)))).trans_eq ?_); ring
-- clip/compress
local notation "A◇"=> freshF P i (-home P q f0) x
include M
lemma hey_told (v:ℕ)(u:f0 ≤ v) (l r:ℝ): (Fξ x) v l r= A◇ (F☾ v l r):=by rw [hey_info P q p i x ρ (ρ.date.stock v u).2 u]; rw [cast_chime P M i x p ρ u]; rw [freshCutt,P.reprise_smul,P.locate_smul,pricing_p P M i x p ρ v pseV u]
lemma hey_meter (u:f0 ≤ v):(P.seasons i x).Credits (ℓ v) ((Fξ x) v):=by intro a b c d y z f g; rw [hey_told P q p M i x ρ pHw K _ u, hey_told P q p M i x ρ pHw K _ u,pse_cap P M i x p ρ u y z f g,freshCutt,P.reprise_sand,P.locate_sand]; rfl
lemma summitK : ∃ (D C:ℝ), 1≤D∧0≤ C∧UnpadTicket.Climbed (moonClock P) (f0+1) (Fξ x) D C:=by
 obtain ⟨c,h,p₂⟩:= staircaseK P q p M i x ρ pHw K; have ht:1≤(h☾):=by
    refine (unit_live P).trans ?_; unfold unitX; simp_rw [pulse_power]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ)≤ rota P.par.R.L from Nat.one_le_cast.mpr P.par.R.L.property) (show (3:ℕ)≤4 by decide)) receipt_pos.le
 refine ⟨h☾,c,ht,h,fun s v hv hs l r hl hr=>?_⟩; rw [hey_told P q p M i x ρ pHw K _ (by omega), freshCutt,P.locate_cost]; exact (P.reprise_pay ..).trans (p₂ s v hv hs l r hl hr)
#print axioms summitK
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
