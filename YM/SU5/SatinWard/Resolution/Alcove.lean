import YM.SU5.SatinWard.Resolution.Clime
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
open Harmonic
variable (s₁:f0 ≤ s)
local notation "Pμ" v:max=> (μ^(v-s))⁻¹
local notation "W‼" v:max=> wageMonth P η A H s v
local notation "J‼" v:max=> pulseMonth P η A H s v
variable (L₀:64≤ P.par.R.L.val)
include ρ s₁ L₀
lemma windowSettle (u:ℕ):∀ᶠ v:ℕ in atTop,16*(deltaWing P (rentWidth P u v):ℝ)*P.macroStep v≤ moonClock P s ∧ 3*P.macroStep v≤ moonClock P s:=by
 obtain ⟨j,y,v⟩:= ((wing_room P L₀ u).and (eventually_ge_atTop s)).exists
 filter_upwards [eventually_ge_atTop j] with v' u'
 have he:= (y v' u' (rentWidth P u v') le_rfl).trans (loans_le P ρ s₁ v); refine ⟨he,?_⟩; apply le_trans _ he
 have h: (1:ℝ)≤ (deltaWing P (rentWidth P u v'):ℝ):= by exact_mod_cast (Nat.succ_le_of_lt (wing_pos ..))
 refine mul_le_mul_of_nonneg_right ?_ (P.macroStep_pos _).le; linarith
omit L₀
lemma tabulatedEra : ∀ᶠ v:ℕ in atTop,
    1 ≤ Play v ∧ Play v ≤ Xᵤ v ∧ ‖(δ v:ℂ)‖*(Xᵤ v)^5 * wageMonth P η A H s v ≤ 1 ∧ (Xᵤ v)*(2*|δ v| *(4*ageBudget P η A C H s * Pμ v)) ≤ 1 ∧ ‖(δ v:ℂ)* ((Jγ v):ℝ)‖*(8*|pulseMonth P η A H s v|)* Play v ≤ 1:=by
 let D:=2*owedP (totalBudget A (Announcement Wage4 η)) (Tabletop.Harmonic.rentP L A (yardF cloverFrame) H cloverFrame*lapQ P.run s); let B:= 2*owedP (totalBudget A (Announcement Wage3 η)) (headrent P A H s); let N:=ageBudget P η A C H s; let χ:= sprintCost P.par.R.L
 have hv:= scale_dawn P ρ s₁; have hm:0≤ N:=hv.le; have hy:0<χ:=sprint_pos L
 filter_upwards [subsidy P ρ s₁ |D| (abs_nonneg _) 5, subsidy P ρ s₁ (8*N) (by positivity) 1, subsidy P ρ s₁ (8*|B|) (by positivity) 6,tempTrip P] with v u w bS p
 obtain ⟨hu,tV,hm',ht,pR⟩:=p _ rfl; let U:=Play v; let F:= Xᵤ v; let X:=Ω v; have he:‖(δ v:ℂ)‖= |δ v|:=by rw [Complex.norm_real,Real.norm_eq_abs]
 let q:= Pμ v; have hq:0 ≤ q:=by unfold q; exact inv_nonneg.mpr (pow_nonneg hy.le _); -- hy unfolded?
 have hU:0≤F:=by exact zero_le_one.trans (hm'.trans ht)
 have hV:F^5 ≤ X^5:=pow_le_pow_left₀ hU pR 5; let O:= |δ v|; let Vq:= pulseMonth P η A H s v; have hZ:0≤O:= by unfold O; positivity
 have hHp:1≤X:=hu; let Xv:=Jγ v; refine ⟨hm',ht,?_,?_,?_⟩
 · rw [he]; change O*F^5*(D*q) ≤ _; change |D| *X^5*O*q≤_ at u; apply le_trans _ u
   calc
      _ ≤ O*F^5*(|D| *q):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hq) (mul_nonneg hZ (pow_nonneg hU _))
      _ ≤ _:=by linarith only [mul_le_mul_of_nonneg_right hV (show 0 ≤ |D| *O*q by positivity)]
 · rw [pow_one] at w; change 8*N*X*O*q≤ 1 at w; change F*(2*O * (4*N*q))≤_; apply le_trans _ w; exact (mul_le_mul_of_nonneg_right pR (by positivity)).trans_eq (by unfold O; change _= _; ring)
 rw [norm_mul,he,Complex.norm_real,Real.norm_eq_abs]; have h0:0 ≤ Xv:=by unfold Xv; have hz':0 ≤ polishQ P v:=hU; positivity
 have hx:Xv ≤ X^5:=calc
    Xv ≤ X*X^4:=mul_le_mul tV (pow_le_pow_left₀ hU pR _) (by positivity) (zero_le_one.trans hu)
    _ = _:=by ring
 change 8*|B| * X^6*O*q ≤ 1 at bS; change O * |Xv| * (8*|B*q|) * Play v ≤ _; rw [abs_of_nonneg h0, abs_mul,abs_of_nonneg hq]
 have hx':0 ≤ Play v:=zero_le_one.trans hm'
 have hv:(Xv* (Play v)) ≤ X^5*X:= mul_le_mul hx (ht.trans pR) hx' (by positivity)
 nlinarith only [mul_le_mul_of_nonneg_right hv (show 0≤ O*(8*|B|)*q by positivity),bS] -- fix tokens
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
