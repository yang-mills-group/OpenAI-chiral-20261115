import YM.SU5.SatinWard.Resolution.Meetup
import YM.SU5.SatinWard.Resolution.ScaleW
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
namespace Internal
-- every polynomial power won. working on fixed s budget. constants may depend on that s not calibration iteration limits.
local notation "δ" v:max=>psScale P ρ v
local notation "c"=>cloverFrame.pulseBase P.par.R.L
local notation "T◎" n:max=> |psScale P ρ n|
local notation "Play" d:max=> stemS (Ω d)
local notation "Jγ" v:max=> (temp (Ω v))⁻¹^2 * (polishQ P v)^4
variable {i:ℕ} (s₁:f0 ≤ s)
include ρ s₁
lemma subsidy (E:ℝ) (e:0≤ E)(m:ℕ) :∀ᶠ i:ℕ in atTop,E*(Ω i)^m * T◎ i *((μ^(i-s))⁻¹) ≤ 1:=by
 let Z(k):= |psScale P ρ k|
 let y:= μ; let k:=s+1; let Y:=Z k; have hk:0< y:= sprint_pos _; have v: Z k ≥ 0:=abs_nonneg _
 let D:= |P.par.x|+ (billX P.par.R.L)*(k+1)+1; let A:=P.par.x; let r:= billX L; have ht:0≤ r:=Vale.pitch _; have hv:0<D:=by unfold D; have hv:0≤ billX L:=ht; positivity; -- D ambiguous $k nat coerces k+1$
 let U:= E*D^m*Y*y⁻¹; let q:=fun i:ℕ=> (i:ℝ)^m*(1/2:ℝ)^i; have hu:Tendsto q atTop (𝓝 0):= tendsto_pow_const_mul_const_pow_of_lt_one _ (by norm_num) (by norm_num); have hu':∀ᶠ i in atTop,U*q i≤1:=by simpa using (hu.const_mul U).eventually (ge_mem_nhds (show U*0<1 by simp))
 filter_upwards [(turnover P.par).eventually_ge_atTop 0,eventually_gt_atTop k,(show Tendsto (fun i:ℕ=> i-k) atTop atTop from tendsto_atTop.mpr (fun i=> by filter_upwards [eventually_ge_atTop (i+k)] with y v using (by omega))).eventually hu'] with i h p hz
 let j:=i-k; let H0:=i-s; have t':0< (j:ℝ):=by exact_mod_cast (show 0 < j by omega)
 have J0:0≤ c:= (div_pos receipt_pos (cloverFrame.chi_pos _)).le
 have hu: i=j+k:=by unfold j; omega
 have he: Z i * y⁻¹^H0 ≤ (1/2:ℝ)^j* Y*y⁻¹:= by
    have h₁:= scale_le P ρ (lt_of_le_of_lt s₁ (Nat.lt_succ_self _)) p.le
    have h₂:(c/μ)^j ≤ (1/2:ℝ)^j:=pow_le_pow_left₀ (div_nonneg J0 hk.le) ρ.date.fiscal.2.2.2.loss _
    calc Z i * _ ≤ (Y*c^j) * (y⁻¹^j*y⁻¹):=by rw [show H0=j+1 from (by omega),pow_succ]; exact mul_le_mul_of_nonneg_right h₁ (by positivity)
         _ = (c/μ)^j *Y*y⁻¹:=by rw [div_eq_mul_inv,mul_pow]; ring
         _ ≤ _:=by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ v) (inv_nonneg.mpr hk.le)
 have hp: Ω i ≤ D*(j:ℝ):=by unfold D; rw [show Ω i=A+i*r from (by unfold hat A r; ring),hu]; push_cast; have hℓ:1≤(j:ℝ):=(by exact_mod_cast Nat.add_one_le_of_lt (show 0< j by omega)); change A+((j:ℝ)+k)*r ≤ (|A|+r*((k:ℝ)+1)+1)*j; nlinarith [mul_le_mul_of_nonneg_left hℓ (abs_nonneg A), mul_nonneg ht (show 0≤(k:ℝ) by positivity),mul_le_mul_of_nonneg_left hℓ (mul_nonneg ht (show 0≤(k:ℝ) by positivity)),le_abs_self A]
 rw [←inv_pow]; change E*(Ω i)^m* Z i* _ ≤_; rw [mul_assoc (E*_)]; calc
    _ ≤ E * (D * (j:ℝ))^m * ((1/2:ℝ)^j*Y*y⁻¹):=by have hy:0≤ Y:=v; exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h hp _) e) he (by unfold Z; positivity) (by positivity)
    _ = U*q j:= by unfold U q; rw [mul_pow]; ring -- expand mul^m
    _ ≤ _:=hz
omit ρ s₁
lemma tempTrip :∀ᶠ i:ℕ in atTop, ∀ (V':ℝ), V'=Ω i→ (1≤V') ∧ (temp (Ω i))⁻¹^2≤ V'∧ 1 ≤ Play i ∧ Play i ≤ Xᵤ i ∧ Xᵤ i≤ Ω i:=by
 filter_upwards [(turnover P.par).eventually_ge_atTop 1,(turnover P.par).eventually ((Grade.stock 0 1).cost_p zero_lt_one)] with i h e y rfl
 let a:= temp (Ω i); let p:=Xᵤ i; have hp:1≤p:= faderP P i; let f':=Ω i; have he:0<f':=zero_lt_one.trans_le h; have hP:BPress.drift f'=p:=by unfold p polishQ; rw [BPress.drift_eq,coin_scale]
 have hd:0<Real.sqrt f':= Real.sqrt_pos.mpr he; have hm:0≤ Play i:= Real.rpow_nonneg (by rw [show BPress.drift (Ω i)=p from hP]; linarith) _; refine ⟨h,?_,?_,?_,(le_abs_self _).trans (e.trans_eq (Real.rpow_one _))⟩
 · unfold temp; rw [show Real.exp ((Real.log (Real.log (Ω i)))^2)=p from (BPress.drift_eq _).symm.trans hP]; refine le_trans (pow_le_pow_left₀ (by positivity) (show ((Real.sqrt (Ω i))⁻¹*p)⁻¹ ≤ Real.sqrt (Ω i) from ?_) _) (Real.sq_sqrt he.le).le
   rw [mul_inv_rev,inv_inv,mul_comm]; exact mul_le_of_le_one_right hd.le (inv_le_one_of_one_le₀ hp)
 · unfold stemS; rw [show BPress.drift (Ω i)=p from hP]; apply Real.one_le_rpow hp (by norm_num)
 unfold stemS; rw [show BPress.drift (Ω i)=p from hP]; exact (Real.rpow_le_rpow_of_exponent_le hp (by norm_num: (1:ℝ)/4≤1)).trans_eq (Real.rpow_one _)
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
