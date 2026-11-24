import YM.SU5.SatinWard.Resolution.ColorVoice
import YM.SU5.SatinWard.Resolution.Awning
import YM.SU5.SatinWard.Resolution.Cue
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
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
open SatinWard
local notation "R"=> Option Tilted.Ramp
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "K"=> P.run
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
local notation "Q" => P.calibration.ℓ
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
open Selected
local notation "ζ"=>P.sidesPerTick
open Real (exp log)
-- entrance as manuscript. Replace estimate C/R after point scaling with C/P.
local notation "T'" i:max=>stride P i
local notation "λ∗"=> T' v -- risky
local notation "ℓ" i:max=> moonClock P i
local notation "Ω" i:max=> hat P.par.R.L P.par.x i
local notation "f" i:max=> corridorHeight P i
local notation "Xᵤ" i:max=> polishQ P i
local notation "R▶" i:max=> corridorR P i
local notation "β₄" i:max=> (ageBudget P η A C H i)
local notation "p₀" => billX P.par.R.L
local notation "P'" => P.par.x
local notation "t" i:max=> gaugeMesh P.par i
local notation "ν" => (↑P.par.R.L.val:ℝ)
local notation "μ"=> sprintCost P.par.R.L
variable (ρ: Piano P f0 C H A η Z) -- edit
variable {β wp} {b C':ℝ}{e:ℕ→ℝ}{T₀:P.Register}(T₁: CouncilGrant P T₀ b C' e Z wp β)
local notation "q'" s:max=> lapQ P.run s
local notation "h₀" s:max=> tollηw P β s
local notation "ρ₀" s:max=> (4*ageBudget P η A C H (f s))
local notation "b₀" v:max=> (β v:ℝ)
local notation "b₁" s:max=> (Pressure.temp (Ω s))
private lemma quiet_price (k:ℕ): ((Xᵤ k)^10:ℝ) ≤ (32:ℝ)^(T' k):=by
 let p:= Xᵤ k; let n:= T' k; have hv:1≤p:=faderP P k
 have he: log (32:ℝ) ≥ 2:=by
    rw [ge_iff_le,←Real.exp_le_exp,Real.exp_log (by norm_num),show (2:ℝ)=1+1 by norm_num,Real.exp_add]; refine (mul_le_mul (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286:ℝ)<3)).le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286:ℝ)<3)).le (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
 have hn:5*log p ≤ n:= Nat.le_ceil _; change p^10 ≤ (32:ℝ)^n; rw [←Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; nlinarith

namespace MezzoBill
open Internal Verdance SoulField
lemma quotaUnit : ∃ a:ℝ,0<a∧∀ k,2*soulQuote P η A k=a*q' k:=by
 refine ⟨2*Real.exp (4*totalBudget A (Announcement Wage3 η)+1)*quoteX η, by have hv:=quote_live η; positivity,fun k=>?_⟩; rw [soulQuote, owedP,mul_assoc (_* exp _), mul_assoc]; ring
local notation "bL" k:max=>2*soulQuote P η A k
local notation "h♭" k:max=>vigorΩ P.par k
include ρ
lemma spendS₁ : ∀ᶠ v:ℕ in atTop,(bL (f v))*2*((Yt)^(v-f v))⁻¹*(h♭ v)⁻¹*(R▶ v)^4*(Xᵤ v) ≤ 1:=by
 obtain ⟨r,u,w⟩:= quotaUnit (η:=η) (A:=A) P; have hν:0<ν:=Nat.cast_pos.mpr P.par.R.L.property
 filter_upwards [ (polish_late P).eventually_ge_atTop (4*r), roomρια P, (cue_infinite P).eventually (shift_late P), f_still P, (polish_late P).eventually_ge_atTop P.par.h,eventually_ge_atTop f0] with v h p z q x₁ k
 let a:=f v; let n:= v-f v; have e:n=stride P v:= q.2; let σ:= Xᵤ v; have hv: 1≤σ:= faderP P v; have hb: 0< (h♭ v):= charge P ρ k; have hz: (lapQ P.run a)*(h♭ v)⁻¹ ≤ (2:ℝ)^n*(2*σ^2):=by
    rw [← div_eq_mul_inv,div_le_iff₀ hb, mul_assoc ((2:ℝ)^n)]; refine (z v q.1.le).trans (mul_le_mul_of_nonneg_left (?_) (by positivity))
    rw [show lapQ P.run v=(h♭ v)*P.par.h^2 from (div_mul_cancel₀ _ (sq_pos_of_pos (zero_lt_one.trans_le P.par.height)).ne').symm]; rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ hb.le; let hX: P.par.h^2 ≤ σ^2:=pow_le_pow_left₀ (zero_le_one.trans P.par.height) x₁ _; nlinarith only [hX,sq_nonneg σ]
 have hR: R▶ v ≤ σ*ν^n:=by rw [corridorValue]; exact mul_le_mul_of_nonneg_right p (pow_pos hν _).le
 have hn: (Xᵤ v)^8 ≤(32:ℝ)^n:=(pow_le_pow_right₀ hv (by norm_num : (8:ℕ) ≤ 10)).trans (e.symm ▸ quiet_price P v) -- power conversion
 rw [w]; let y:= μ; have hy:0<y:=sprint_pos _; let M:=moonClock P a; have hV:0 < R▶ v:= div_pos (clockP P a) (gaugeMesh_pos _ _)
 calc
    _ = 2*r*(lapQ P.run a*(h♭ v)⁻¹)*(R▶ v)^4*σ / y^n :=by unfold a n σ y; rw [div_eq_mul_inv]; ring
    _ ≤ 2*r*((2:ℝ)^n*(2*σ^2))*(σ*ν^n)^4*σ / y^n:=by 
         apply div_le_div_of_nonneg_right _ (pow_pos hy _).le; have he:0≤2*r*((2:ℝ)^n*(2*σ^2)):=by positivity
         apply mul_le_mul_of_nonneg_right _ (by positivity); exact mul_le_mul (mul_le_mul_of_nonneg_left hz (by positivity)) (pow_le_pow_left₀ hV.le hR _) (by positivity) he
    _ ≤ 1:=by
         rw [div_le_one (pow_pos hy _), mul_pow,←pow_mul, Nat.mul_comm n 4, pow_mul]; have hτ: ((2:ℝ)^n* (ν^4)^n)*(32:ℝ)^n ≤ y^n:=by
            rw [←mul_pow,←mul_pow]; apply pow_le_pow_left₀ (by positivity) _; exact le_trans (le_of_eq (by ring)) (ratio_u P ρ)
         refine le_trans (?_: _ ≤ ((2:ℝ)^n*(ν^4)^n)* ((32:ℝ)^n)) hτ; refine le_trans ?_ (mul_le_mul_of_nonneg_left hn (by positivity)); change 4*r ≤ σ at h; linarith only [mul_le_mul_of_nonneg_right h (show 0≤ ((2:ℝ)^n * (ν^4)^n)*σ^7 by positivity)]
end MezzoBill
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
