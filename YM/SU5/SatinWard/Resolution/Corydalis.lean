import YM.SU5.SatinWard.Resolution.RunLens
import YM.SU5.SatinWard.Resolution.Diva
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
open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
local notation "Y"=> P.run
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} {Z:Visit→ Cover → Family P.calibration} {χ:Division}{d:PitchZ}
variable (E:Ceremo P η v P.jump128 f0 a b φ H A χ D Z d)(q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)
local notation "Ξ" u:max=> cloakF P M p (E.earnedZ P η u) v
local notation "Δ"=> cloakF P M p (logStarCore P η E) v
local notation "X" v:max=> hat P.par.R.L P.par.x v
local notation "Yw" v:max=> (hueW P.par.R.L (X v))
local notation "h★" v:max=> (↑(Yw v):ℂ)
local notation "h△" v:max=>(↑(qHull P.par.R.L (X v)):ℂ)
local notation "h❖" v:max=>(↑(jHull P.par.R.L (X v)):ℂ)
open Motet SoulField Verdance Mezzo SatinWard.Installment
variable (W:HeartClock P f0 H A a b φ P.jump128 M D η)
variable {f:ℕ} (h:f0 ≤ f)(hv:f<v)
local notation "dH" v:max=> Motet.dewy P.par v
local notation "L" => P.par.R.L
noncomputable abbrev unitX := (spinFrame 3).pulseBase P.par.R.L
local notation "μ" => sprintCost P.par.R.L
local notation "DX" => unitX P
local notation "a✲" => rota P.par.R.L
local notation "Xᵤ" i:max=>polishQ P i
-- reusable relative powers. Exactly m3 and m4 growth (not m thresholds), exponent buy with precision4 factor (L ratio). no dependence on lap class dimensions. uniform f. `χ=P` history.
noncomputable abbrev julyP :ℝ:= Real.rpow (rota P.par.R.L) (15/8:ℝ)
private lemma day_pos : 0< rota P.par.R.L:= Nat.cast_pos.mpr P.par.R.L.property
include W
lemma warmπ : 4*DX *a✲^(15/8:ℝ) ≤ μ :=by
 have h:= day_pos P; rw [unitX,pulse_power]; have hξ: a✲^(15/8:ℝ)= a✲ * (a✲)^(7/8:ℝ):=by rw [show (15/8:ℝ)=1+7/8 by norm_num, Real.rpow_add h,Real.rpow_one];
 rw [hξ]; let F:=(spinFrame 3).deg; have he:F=3:=rfl
 change 4*(receiptCost*a✲^3)*(a✲*(a✲)^(7/8:ℝ)) ≤ _ ; exact le_trans (le_of_eq (by ring)) W.tally.date.fiscal.2.2.2.growth -- include W
-- below combine all v uniformly. wants `arr* μ^s * (a^(-15/8))^v` for decay
omit W
lemma july_pos : 0<julyP P:=Real.rpow_pos_of_pos (day_pos P) _
lemma unit_live : 1≤ unitX P:=by
 unfold unitX; rw [pulse_power]; have h:1≤rota P.par.R.L:=Nat.one_le_cast.mpr P.par.R.L.property
 have hp :1 ≤ receiptCost :=by unfold receiptCost; apply (le_div_iff₀ headPos).mpr; unfold headFine; linarith only [Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num)]
 exact hp.trans (le_mul_of_one_le_right receipt_pos.le (one_le_pow₀ h))
lemma dewyT : (dH v)⁻¹=(polishQ P v)^4:=by unfold Motet.dewy chillInt; rw [inv_inv]; unfold polishQ; rw [BPress.drift_eq,coin_scale]
lemma turquoise : 1 ≤ (dH v)⁻¹:=by rw [dewyT]; exact one_le_pow₀ (faderP ..)
include W
local notation "t_v" d:max=> (julyP P)⁻¹^d
open Real
lemma on_path : ∀ᶠ v in atTop,(DX/μ)^v*((dH v)⁻¹) ≤ ((julyP P)⁻¹)^v:=by
 let u:= DX / μ*julyP P; have h₁:0< unitX P:= zero_lt_one.trans_le (unit_live P); have h₂:0<μ:= sprint_pos _; have he:0 ≤ u:=mul_nonneg (by positivity) (july_pos P).le; have p:u ≤ 1/2:=by unfold u; rw [div_mul_eq_mul_div,div_le_iff₀ h₂]; have ht:4*DX*julyP P ≤ μ:=warmπ P η M W; linarith only [ht,(sprint_pos L)] -- θ weight order tuning
 let D:= |P.par.x| + |billX L| ; let H(v:ℕ):= hat P.par.R.L P.par.x v
 let q:=fun i:ℕ=> (i:ℝ)^4*(1/2:ℝ)^i; have hu:Tendsto q atTop (𝓝 0):= tendsto_pow_const_mul_const_pow_of_lt_one _ (by norm_num) (by norm_num)
 have hu':∀ᶠ i in atTop,D^4*q i≤1:= (hu.const_mul (D^4)).eventually (ge_mem_nhds (by rw [mul_zero]; exact zero_lt_one : D^4*0<1))
 filter_upwards [tempTrip P,hu',eventually_ge_atTop 1] with i s t hv
 have hx:0≤ D:=add_nonneg (abs_nonneg _) (abs_nonneg _); have hh: 1 ≤ (i:ℝ) :=Nat.one_le_cast.mpr hv; let Q:= s _ rfl
 have h:H i ≤ D * (i:ℝ):=by unfold H hat D; nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg P.par.x),le_abs_self P.par.x,mul_le_mul_of_nonneg_left (le_abs_self (billX L)) (Nat.cast_nonneg (α:=ℝ) i)]
 have hb:(0:ℝ)< Xᵤ i:=zero_lt_one.trans_le (faderP ..)
 have ht:(DX/μ)^i *(julyP P)^i *(dH i)⁻¹≤1:=by
    rw [←mul_pow,dewyT]; apply le_trans (mul_le_mul (pow_le_pow_left₀ he p _) (pow_le_pow_left₀ hb.le (Q.2.2.2.2.trans h) _) (by positivity) (by positivity)) _; rw [mul_pow D]; change (1/2:ℝ)^i *(D^4*(i:ℝ)^4)≤1; unfold q at t; linarith only [t]
 change (DX/μ)^i * (dH i)⁻¹ ≤ _; rw [inv_pow,←one_div ((julyP P)^i),le_div_iff₀ (pow_pos (july_pos P) _), mul_right_comm]; exact ht
-- can extend to all v by monotone L factor κ. need remains with arbitrary f neighborhood of δ. constants depend tuning.
omit W in
private theorem for_all_ages (f g:ℕ→ℝ)(p:∀ᶠ i in atTop,f i≤g i)(h:∀ i,0 < g i): ∃ C:ℝ,1 ≤ C ∧ ∀ i,f i ≤ C*g i:=by
 obtain ⟨n,u⟩:=eventually_atTop.mp p 
 let K:ℝ:=∑ i∈ Finset.range n, |f i/g i|
 refine ⟨1+K,le_add_of_nonneg_right (sum_nonneg fun _ _ =>abs_nonneg _),fun i=>?_⟩; by_cases x:i<n; · apply (div_le_iff₀ (h i)).mp; exact (le_abs_self _).trans ((single_le_sum (fun (j:ℕ) (_:j∈ Finset.range n)=>abs_nonneg (f j/g j)) (mem_range.mpr x)).trans (le_add_of_nonneg_left zero_le_one))
 exact (u _ (by omega)).trans (le_mul_of_one_le_left (h i).le (le_add_of_nonneg_right (sum_nonneg fun _ _=>abs_nonneg _)))
lemma fiscal_meter : ∃ C:ℝ,1≤C∧∀ (v s:ℕ),s≤v→DX^v*(dH v)⁻¹*((μ^(v-s))⁻¹)≤ C*μ^s*((julyP P)⁻¹)^v:=by
 obtain ⟨c,p,h⟩:= for_all_ages _ _ (on_path P η M W) (fun i=>pow_pos (inv_pos.mpr (july_pos _)) i)
 refine ⟨c,p,fun v s u=>?_⟩; specialize h v; have he:0<μ:= sprint_pos _
 calc
    _ = ((DX/μ)^v*(dH v)⁻¹)*μ^s:=by rw [div_pow (DX) μ, pow_sub₀ μ (by positivity) u]; rw [mul_inv_rev (μ^v),inv_inv (μ^s), div_eq_mul_inv (DX^v) (μ^v)]; ac_rfl
    _ ≤ _:= le_trans (mul_le_mul_of_nonneg_right h (by positivity)) (le_of_eq (by ring))
omit W
lemma daysT (s:ℕ):σ s= σ 0/a✲^s:=by
 have h:0<a✲:= day_pos P; apply (eq_div_iff (pow_pos h _).ne').mpr; have hp:=P.daysF s 0 (by omega); rw [mul_comm]; -- maybe daysF gives nsmul
 simpa only [Nat.sub_zero,Nat.cast_pow,rota] using hp
lemma monad_eq (s:ℕ) (r:ℝ): (σ s)^r=(σ 0)^r*((a✲^r)⁻¹)^s:=by rw [daysT,Real.div_rpow (P.macroStep_pos _).le (pow_pos (day_pos P) _).le, inv_pow, ←Real.rpow_natCast_mul (day_pos P).le, mul_comm (s:ℝ) r, Real.rpow_mul_natCast (day_pos P).le,div_eq_mul_inv] -- lemma names
#print axioms fiscal_meter
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
