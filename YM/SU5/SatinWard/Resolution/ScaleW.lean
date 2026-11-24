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
include ρ
lemma ratio_u : 64*ν^4≤ μ:=by
 have hν:1≤ν:=by exact_mod_cast Nat.succ_le_of_lt P.par.R.L.property
 calc
    _ ≤ 4*receiptCost*ν^4:=by
         gcongr; have ht:= Real.exp_le_one_iff.mpr (show (-1:ℝ)≤ 0 by norm_num); have hp: 16 ≤ receiptCost:= by apply (le_div_iff₀ headPos).mpr; unfold headFine; linarith
         linarith
    _ ≤4*receiptCost*ν^4*ν^(7/8:ℝ):=le_mul_of_one_le_right (by have hp:=ShapeLab.receipt_pos; positivity) (Real.one_le_rpow hν (by norm_num))
    _ ≤_:= ρ.date.fiscal.2.2.2.growth
lemma rentPos : 0< rentalW P.par.R.L A C H:= (pos_of_mul_pos_left (rentalP P ρ.date (s:=f0) le_rfl) (ρ.date.stock _ le_rfl).1.1.le) -- `_left`
lemma rhoUnit : ∃ a:ℝ,0<a∧∀ k,4 *ageBudget P η A C H k=a*q' k:=by
 refine ⟨4*Real.exp (4*totalBudget A (Announcement Wage4 η)+1)*rentalW L A C H, by have he:=rentPos P ρ; positivity,fun k=>?_⟩; rw [mul_assoc (_ * exp _), mul_assoc]
omit ρ
private lemma ratio_price (k:ℕ): ((Xᵤ k)^10:ℝ) ≤ (32:ℝ)^(T' k):=by
 let p:= Xᵤ k; let n:= T' k; have hv:1≤p:=faderP P k
 have he: log (32:ℝ) ≥ 2:=by
    rw [ge_iff_le,←Real.exp_le_exp,Real.exp_log (by norm_num),show (2:ℝ)=1+1 by norm_num,Real.exp_add]; refine (mul_le_mul (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286:ℝ)<3)).le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286:ℝ)<3)).le (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
 have hn:5*log p ≤ n:= Nat.le_ceil _; change p^10 ≤ (32:ℝ)^n; rw [←Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; nlinarith
include T₁
lemma beta_quarter : 0< b₀ v ∧ b₀ v ≤ 2*Ω v:=by
 let Tw:=Picker.range P.run P.law P.history T₁.order.tendsto_atTop T₁.path_permanent v
 have p:0< hat P.par.R.L P.par.x v:=((Real.exp_pos _).trans_le P.large).trans_le (Vale.crown ..)
 exact ⟨(half_pos p).trans_le Tw.1,Tw.2⟩
lemma beta_ri : b₀ v * b₁ v^2 ≤ 2*(Xᵤ v)^2:=by
 let x:= Ω v; have hx:0< x:= ((Real.exp_pos _).trans_le P.large).trans_le (Vale.crown ..); let e:=Pressure.temp x; have hb:= (beta_quarter P (v:=v) T₁).2; refine (mul_le_mul_of_nonneg_right hb (sq_nonneg e)).trans (le_of_eq ?_); rw [mul_assoc]; apply congrArg; change x*e^2=_; unfold e Pressure.temp; rw [mul_pow]; have hp:=Real.sqrt_pos.mpr hx; unfold polishQ scaleY BProof.coin; field_simp; rw [Real.sq_sqrt hx.le]; simp only [mul_zero,zero_add,zero_mul,x,add_zero]
include ρ
lemma tollηw_p (u:f0 ≤ v):0<h₀ v:=mul_pos (ρ.date.stock v u).1.1 (inv_pos.mpr (mul_pos (pow_pos ((P.run.meter.a v).threshold_pos.trans_eq (P.run.meter.boot v).1) _) (beta_quarter P T₁).1))
lemma toll_shift (v:ℕ)(p:f0 ≤ v): q' v ≤ 2*(Xᵤ v)^2 * (h₀ v):=by
 let q(u:ℕ):=q' u; let σ:= Xᵤ v; let z:=h₀ v; have p0:0<z:= tollηw_p P ρ T₁ p
 have x:0< b₁ v:=((P.run.meter.a v).threshold_pos.trans_eq (P.run.meter.boot v).1)
 have y: 0< b₁ v^2 * b₀ v:=mul_pos (by positivity) (beta_quarter P T₁).1
 refine le_trans (b:=z*(β v * b₁ v^2)) (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (beta_ri P T₁) p0.le).trans_eq (mul_comm _ _))
 rw [mul_comm (β v),show z=q' v * (_*β v)⁻¹ from rfl]; rw [mul_assoc, inv_mul_cancel₀ y.ne',mul_one]
-- universal entrance costs Pad and remainder and character stamps. κρRankLimit. BE careful algebra with β in Estimate.
lemma stamp_credit : ∀ᶠ v:ℕ in atTop,(ρ₀ v)*2*((Yt)^(v-f v))⁻¹*(h₀ v)⁻¹*(R▶ v)^4*(Xᵤ v) ≤ 1:=by
 obtain ⟨r,u,w⟩:= rhoUnit P ρ; have hν:0<ν:=Nat.cast_pos.mpr P.par.R.L.property
 filter_upwards [ (polish_late P).eventually_ge_atTop (4*r), roomρια P, (cue_infinite P).eventually (shift_late P), f_still P, eventually_ge_atTop f0] with v h p z q k
 let a:=f v; let n:= v-f v; have e:n=stride P v:= q.2; let σ:= Xᵤ v; have hv: 1≤σ:= faderP P v; have hb: 0< (h₀ v):= tollηw_p P ρ T₁ k; have hz: (lapQ P.run a)*(h₀ v)⁻¹ ≤ (2:ℝ)^n*(2*σ^2):=by
    rw [← div_eq_mul_inv,div_le_iff₀ hb, mul_assoc ((2:ℝ)^n)]; exact (z v q.1.le).trans (mul_le_mul_of_nonneg_left (toll_shift P ρ T₁ v k) (by positivity))
 have hR: R▶ v ≤ σ*ν^n:=by rw [corridorValue]; exact mul_le_mul_of_nonneg_right p (pow_pos hν _).le
 have hn: (Xᵤ v)^8 ≤(32:ℝ)^n:=(pow_le_pow_right₀ hv (by norm_num : (8:ℕ) ≤ 10)).trans (e.symm ▸ ratio_price P v) -- power conversion
 rw [w]; let y:= μ; have hy:0<y:=sprint_pos _; let M:=moonClock P a; have hV:0 < R▶ v:= div_pos (clockP P a) (gaugeMesh_pos _ _)
 calc
    _ = 2*r*(lapQ P.run a*(h₀ v)⁻¹)*(R▶ v)^4*σ / y^n :=by unfold a n σ y; rw [div_eq_mul_inv]; ring
    _ ≤ 2*r*((2:ℝ)^n*(2*σ^2))*(σ*ν^n)^4*σ / y^n:=by 
         apply div_le_div_of_nonneg_right _ (pow_pos hy _).le; have he:0≤2*r*((2:ℝ)^n*(2*σ^2)):=by positivity
         apply mul_le_mul_of_nonneg_right _ (by positivity); exact mul_le_mul (mul_le_mul_of_nonneg_left hz (by positivity)) (pow_le_pow_left₀ hV.le hR _) (by positivity) he
    _ ≤ 1:=by
         rw [div_le_one (pow_pos hy _), mul_pow,←pow_mul, Nat.mul_comm n 4, pow_mul]; have hτ: ((2:ℝ)^n* (ν^4)^n)*(32:ℝ)^n ≤ y^n:=by
            rw [←mul_pow,←mul_pow]; apply pow_le_pow_left₀ (by positivity) _; exact le_trans (le_of_eq (by ring)) (ratio_u P ρ)
         refine le_trans (?_: _ ≤ ((2:ℝ)^n*(ν^4)^n)* ((32:ℝ)^n)) hτ; refine le_trans ?_ (mul_le_mul_of_nonneg_left hn (by positivity)); change 4*r ≤ σ at h; linarith only [mul_le_mul_of_nonneg_right h (show 0≤ ((2:ℝ)^n * (ν^4)^n)*σ^7 by positivity)]
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
