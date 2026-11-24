import YM.SU5.SatinWard.Resolution.Muff
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
-- Annotated center. translate with the REAL home clock (not simplified half). Pose Hc later.
variable (M:P.par.R.L.val %16 =1) (k:P.NightCop) (j:Axis)(x:P.Spectrum0 j)
variable {a: Cover} (qa:ResidualPermit a) (y:Coords Wage4) (q:payable P v 2) {u d:ℝ}
variable (f:ℕ)(g₀:f ≤ v)
local notation "τ" i:max=> P.macroStep i
local notation "W₀" => choirWidth P
/-- One anchor/order, all Norma. Include a physical allowance for slower width. -/
structure Piano (P:Spine)(f0:ℕ) (C H A:ℝ)(η:Type)[Fintype η](Z:ℕ→ℕ):Prop where
 date : Calendrical P C H A f0 η Z
 pays : ∀ s≥f0,(2*((choirWidth P):ℝ)+4)* P.macroStep s≤ moonClock P s
 poses : ∀ s≥f0,∀ a,ResidualPermit a→∃ p,ShowField P s (homeTag P a) p
 loans : ∀ s≥ f0,∀ k≥s, moonClock P k ≤ ((1/2:ℝ)^(k-s))*moonClock P s
variable (ρ: Piano P f0 C H A η Z)
local notation "Mₛ" k:max=> if h:f0 ≤ k then (portGain ((ρ.date.enough k h).choose)) else 1 -- sigma at k+1 increases
noncomputable def psIndex (g:ℕ):ℝ:= Mₛ g
-- set Σ_s=1 until AND AT f0+1. Default constants before.
noncomputable def psScale : ℕ→ℝ
| 0=>1
| g+1=> if f0 < g then psScale g * psIndex P ρ g else 1
local notation "θ"=>psIndex P ρ
local notation "δ"=>psScale P ρ
local notation "μ"=>sprintCost P.par.R.L
local notation "ℓ" i:max=> moonClock P i
local notation "β₃" i:max=> (ageBudget P η A C H i)*(μ^(i-s))⁻¹
lemma psIndex_boost (u:f0≤g): mBooster P.par.R.L (θ g):=by unfold psIndex; rw [dif_pos u]; exact ((ρ.date.enough _ u).choose_spec.choose_spec.choose_spec).growth -- type
lemma psIndex_X (u:f0≤g): θ g ≠0:=by
 obtain ⟨h,-⟩:=psIndex_boost P ρ u; have e:0< mtorque L:= mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (cloverFrame.chi_pos P.par.R.L); exact abs_pos.mp ((mul_pos (by norm_num) (inv_pos.mpr e)).trans_le h)
include ρ
lemma scale_dawn (u:f0≤ s):0 < ageBudget P η A C H s:=mul_pos (Real.exp_pos _) (rentalP P ρ.date u)
lemma scale_psX (v:ℕ): δ v ≠0:=by induction v with
| zero=>exact one_ne_zero
| succ v u=> rw [psScale]; split_ifs with h; exact mul_ne_zero u (psIndex_X P ρ h.le); exact one_ne_zero
lemma scale_le (p:f0<v) (h:v ≤ g) : |δ g|≤ |δ v| * (cloverFrame.pulseBase L)^(g-v):=by
 induction h with
 | refl=> rw [Nat.sub_self,pow_zero,mul_one]
 | step w ih=> rw [psScale, if_pos (p.trans_le w),abs_mul,Nat.succ_sub w, pow_succ,←mul_assoc]; exact mul_le_mul ih (psIndex_boost P ρ (p.le.trans w)).2 (abs_nonneg _) ((abs_nonneg _).trans ih)
lemma loans_le (q:f0 ≤ s)(h:s≤v): ℓ v ≤ ℓ s:= (ρ.loans s q v h).trans (mul_le_of_le_one_left (clockP P s).le (pow_le_one₀ (by norm_num) (by norm_num)))
/-- Apply to define thermal operator at any apron; if v<f0 choose zero. Does not clip time grid base. -/
noncomputable def complect (v:ℕ)(l r:ℝ): (P.ColorHil j x).Op := if h:f0 ≤ v then ((psScale P ρ v:ℝ):ℂ) • rawSolo P M j x qa pseV (ρ.date.stock _ h).2 f0 h l r else 0
local notation "Π₁"=> complect P M j x qa ρ
lemma cast_chime (h:f0 ≤ v): Π₁ v u d=(↑(δ v):ℂ) • rawSolo P M j x qa pseV (ρ.date.stock _ h).2 f0 h u d:=by unfold complect; rw [dif_pos h]
local notation "β₄" i:max=> (4*ageBudget P η A C H s)*(μ^(i-s))⁻¹
local notation "ξ"=> P.physicalEnergy j x
variable (h₀:f0 ≤ s)
include pZ k ρ qa h₀
lemma heading (h:s<g)(y:ℓ s ≤ u)(z:ℓ s ≤d) : dist (Π₁ g u d) (Π₁ (g+1) u d) ≤ |δ g| * (β₄ g):=by
 let m:= (θ g); have hv:f0 < g:=h₀.trans_lt h; have t:= ((ρ.date.enough g hv.le).choose_spec.choose_spec.choose_spec); obtain ⟨l,e⟩:=ρ.poses s h₀ a qa; have he:= rewed P l h.le pZ ρ.date t M k j x qa f0 e h (ρ.pays s h₀) y z (ρ.date.stock _ hv.le).2 (ρ.date.stock _ (hv.trans_le g.le_succ).le).2 h₀ hv.le -- order
 rw [dist_comm,dist_eq_norm,cast_chime P M j x qa ρ (hv.le.trans (Nat.le_succ _)),cast_chime P M j x qa ρ hv.le, psScale,if_pos hv, Complex.ofReal_mul, mul_smul,← smul_sub,norm_smul, Complex.norm_real,Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); simpa only [psIndex,dif_pos hv.le] using he -- `simp using` maybe goal
lemma brush (y:ℓ s≤u)(z:ℓ s≤d)(r:s<v): Tendsto (fun i=> Π₁ i u d) atTop (𝓝 (limUnder atTop (fun i=> Π₁ i u d)))∧
    dist (Π₁ v u d) (limUnder atTop (fun i=> Π₁ i u d)) ≤ 2*|δ v| * (β₄ v):=by
 let c:= |δ v| * (β₄ v); let e:= cloverFrame.pulseBase L; have he:0<e:= div_pos receipt_pos (cloverFrame.chi_pos _); have hb:= sprint_pos L
 have hC:0≤ c:= by unfold c; have ht:= scale_dawn P ρ h₀; positivity
 let F(i:ℕ):=Π₁ i u d; let B(i:ℕ):= F (i+v)
 have h(i:ℕ):dist (B i) (B (i+1)) ≤ c*(1/2:ℝ)^i:=by
    unfold B F; rw [Nat.add_right_comm i 1 v]; apply (heading P pZ M k j x qa ρ h₀ (r.trans_le (Nat.le_add_left v i)) y z).trans
    have hk: i+v-s=i+(v-s):=by omega
    have hh:= scale_le P ρ (h₀.trans_lt r) (Nat.le_add_left v i)
    have hp:0 ≤ β₄ (i+v):= mul_nonneg (by have h:=scale_dawn P ρ h₀; positivity) (by positivity)
    refine (mul_le_mul_of_nonneg_right hh hp).trans ?_
    rw [show _ * e ^ (i+v-v)*(β₄ (i+v)) = c*(e/μ)^i from ?_]
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ρ.date.fiscal.2.2.2.loss _) hC
    unfold c; rw [hk,Nat.add_sub_cancel,pow_add,mul_inv_rev,div_pow e μ i,div_eq_mul_inv (e^i) (μ^i)]; ring
 obtain ⟨x,t⟩:= cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ c (by norm_num : (1/2:ℝ)<1) h)
 have h' := dist_le_of_le_geometric_of_tendsto₀ _ c (by norm_num) h t
 have h'':dist (F v) x ≤ c / (1 - 1 / 2):=by simpa only [B, Nat.zero_add] using h'
 have hA:Tendsto F atTop (𝓝 x):= (tendsto_add_atTop_iff_nat v).mp t -- x shadow again
 change Tendsto F _ _ ∧ dist (F v) (limUnder atTop F)≤ _; rw [hA.limUnder_eq]; refine ⟨hA,h''.trans (le_of_eq ?_)⟩ -- reduction 0+v not definally equal
 unfold c; ring
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
