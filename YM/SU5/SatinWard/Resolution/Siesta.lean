import YM.SU5.SatinWard.Resolution.Kinshasa
import YM.SU5.SatinWard.Resolution.VoucherJ
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
open Quire Internal
namespace LampRead
local notation "Jγ" v:max=> jHull P.par.R.L (Ω v)
local notation "ιc" v:max=> canonLease P.run v
local notation "V0" v:max=> (Jγ v:ℂ)
noncomputable abbrev canyon(P:Spine)(v:ℕ):ℝ:= (jHull P.par.R.L (hat P.par.R.L P.par.x v))⁻¹
lemma equated (v:ℕ): canonLease P.run v=(↑(canyon P v):ℂ):=by unfold canyon canonLease; push_cast; rfl
include ρ
lemma creek (h:f0 ≤ v): 0< canyon P v:= inv_pos.mpr (mul_pos (ρ.date.stock _ h).1.1 (intLive ..))
include T₁
lemma hero_use (v:ℕ): (1:ℝ)/2 ≤ b₁ v^2 * β v:=by
 let x:= Ω v; have hx:0< x:= ((Real.exp_pos _).trans_le P.large).trans_le (Vale.crown ..); let e:=Pressure.temp x; let Tt :=Picker.range P.run P.law P.history T₁.order.tendsto_atTop T₁.path_permanent v; have h:x/2 ≤ β v:=Tt.1; have hp: x*e^2=(Xᵤ v)^2:=by unfold e Pressure.temp; rw [mul_pow]; have hp:=Real.sqrt_pos.mpr hx; unfold polishQ scaleY BProof.coin; field_simp; rw [Real.sq_sqrt hx.le]; simp only [mul_zero,zero_add,zero_mul,x,add_zero]
 change _ ≤ e^2 * _; nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg e),one_le_pow₀ (faderP P v) (n:=2),hp]
lemma canyon_use (h:f0 ≤ v): ‖ιc v‖ ≤ 2*(Xᵤ v)^4*( (h₀ v)⁻¹):=by
 rw [equated, Complex.norm_real,Real.norm_of_nonneg (creek P ρ h).le]; let p:= h₀ v; let a:= b₁ v; let b:= β v; let q:= q' v; let x:= Xᵤ v; have hp:0<x:=zero_lt_one.trans_le (faderP P v); have hx:0<a^2*b:= (by norm_num :(0:ℝ)<1/2).trans_le (hero_use P ρ T₁ v); have hq:0<q:= (ρ.date.stock _ h).1.1; have hv:canyon P v=(q:ℝ)⁻¹*x^4:=by unfold canyon jHull chillInt; rw [BPress.drift_eq, mul_inv_rev,inv_inv]; unfold x polishQ; rw [coin_scale, mul_comm]
 rw [hv]; change _ ≤ 2*x^4*((q*(a^2*b)⁻¹)⁻¹); rw [mul_inv_rev,inv_inv]; nlinarith only [mul_le_mul_of_nonneg_left (hero_use P ρ T₁ v) (show 0 ≤ q⁻¹*x^4 by positivity)] -- aligns sq etc
lemma curator (U:ℝ)(u:0<U): ∀ᶠ v:ℕ in atTop, 1 ≤ R▶ v → U*(R▶ v)^3* ‖ ιc v ‖*(Xᵤ v)*|pulseMonth P η A H (f v) v|≤1:=by
 let C:=2* Real.exp (4*totalBudget A (Announcement Wage3 η)+1) * (Tabletop.Harmonic.rentP L A (yardF (spinFrame 3)) H (spinFrame 3)); let r':=U*(|C|+1)
 have hr:0<r':=mul_pos u (by positivity)
 filter_upwards [book_credit P ρ T₁ r' hr,(cue_infinite P).eventually_ge_atTop f0,f_still P] with v h t₀ g; intro hv
 let s:= f v; let q:= (q' s); let z:= (Yt)^(v-s); let Xv:= ‖ιc v‖; have hq:0<q:=(ρ.date.stock _ t₀).1.1; have hy:0 ≤ z⁻¹:=inv_nonneg.mpr (pow_nonneg (sprint_pos L).le _); have hp:0<h₀ v:=tollηw_p P ρ T₁ (t₀.trans g.1.le); have he:0 < Xᵤ v:=zero_lt_one.trans_le (faderP P v); have hV: pulseMonth P η A H (f v) v=C*q*z⁻¹:=by unfold pulseMonth monthlyRent headrent owedP C q z s; ring
 rw [hV,abs_mul,abs_mul,abs_of_pos hq,abs_of_nonneg hy]; let y:=|C| *q*z⁻¹; have H0:0≤y:=by unfold y; positivity
 let w:=(R▶ v)^4; let x':=(Xᵤ v); have hm: Xv≤2*x'^4*(h₀ v)⁻¹:=canyon_use P ρ T₁ (t₀.trans g.1.le)
 change U*_ *Xv*x'*y ≤1
 apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv (show (3:ℕ)≤4 by decide)) u.le) hm (show 0≤Xv from norm_nonneg _) (show 0≤ U*w from by unfold w; positivity)) he.le) H0) _; apply le_trans _ h; unfold y; change U*w*(2*x'^4*(h₀ v)⁻¹)*_*_ ≤ r'*q*2*z⁻¹*(h₀ v)⁻¹*w*x'^5; have hw:0≤w:=by unfold w; positivity
 suffices p: U*|C| ≤ r' by linarith only [mul_le_mul_of_nonneg_right p (show 0≤ q*z⁻¹*(h₀ v)⁻¹*w*x'^5 from by positivity)]
 unfold r'; nlinarith only [u]
#print axioms curator
end LampRead
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
