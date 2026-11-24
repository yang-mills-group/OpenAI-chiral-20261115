import YM.SU5.SatinWard.Resolution.Apside
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
lemma restTick (u:s≤v):τ v≤τ s:=by
 rw [←P.daysF v s u]; apply le_mul_of_one_le_left (P.macroStep_pos _).le; exact_mod_cast Nat.succ_le_of_lt (pow_pos P.par.R.L.property (v-s))
lemma moonday : ∀ᶠ s:ℕ in atTop,(2*(W₀:ℝ)+4)*τ s≤ moonClock P s:=by
 filter_upwards [ (wait_tends P).eventually (eventually_ge_atTop (choirWidth P+10))] with s h; unfold moonClock; rw [pay_half]; refine mul_le_mul_of_nonneg_right (?_) (P.macroStep_pos _).le; exact_mod_cast (show 2*choirWidth P+4 ≤ 2*waitZ P s from by omega)
local notation "hⓐ" i:max=>home P a i j
local notation "dⓐ" i:max=> (↑(W₀:ℕ):ℝ)*τ i
local notation "σ"=>P.physicalEnergy j x
local notation "𝒦"=> P.charter j x
local notation "ℓ"=> moonClock P s
local notation "ℒ"=> P.reachLeaf s v (moonSpan P s)
local notation "Φ"=> soloV P v q a qa y
-- notations avoid in signatures if Lean.res.pset bug (reported with P par R.L).
/-- Uncompressed single stencil, lags around specified home resolution-weighted centre. `eq:hAa`. -/
noncomputable def lined (a:Cover)(g₀:f≤ v)(Z:P.Apron) (l r:ℝ): (P.ColorHil j x).Op:= 𝒦 (chair P M a g₀) (P.rawBase j x Z (l-home P a Z.s j) (r+home P a Z.s j))
noncomputable def rawSolo (f:ℕ)(g₀:f ≤ v)(l r:ℝ): (P.ColorHil j x).Op:= lined P M j x f a g₀ Φ l r
lemma rawTicket (l r:ℝ):rawSolo P M j x qa y q f g₀ l r=𝒦 (chair P M a g₀) (P.rawBase j x Φ (l-hⓐ v) (r+hⓐ v)):=rfl
include qa
lemma raw_cap {t r:ℝ}(u₀:dⓐ v+hⓐ v≤u)(d₀:dⓐ v-hⓐ v≤d)(p:u≤t)(e:d≤r):
 rawSolo P M j x qa y q f g₀ t r=(σ).pad (t-u) (r-d) (rawSolo P M j x qa y q f g₀ u d):=by
 rw [rawTicket,rawTicket]; have e:P.rawBase j x Φ (t-hⓐ v) (r+hⓐ v)= (σ).sand (P.rawBase j x Φ (u-hⓐ v) (d+hⓐ v)) (t-u) (r-d):=by
    rw [P.rawBase_step j x Φ (a:=u-hⓐ v) (b:=d+hⓐ v),sub_sub_sub_cancel_right, add_sub_add_right_eq_sub]
    all_goals try rw [solo_width]
    all_goals linarith
 rw [e,P.charter_sand]; rfl
lemma anchor_move (i:P.VMark)(U:P.VMark)(h:P.laysM i=P.laysM U-P.laysM (chair P M a g₀))(l r:ℝ):
 𝒦 i (rawSolo P M j x qa y q f g₀ l r)= 𝒦 U ((Φ).dye P j x (l-hⓐ v) (r+hⓐ v)):=by
 rw [rawTicket,P.charter_sum, show i+chair P M a g₀=U from lays_uniq _ (by rw [P.lays_add,h,sub_add_cancel])]; rfl
variable (U:ShowField P s (homeTag P a) p)
local notation "Y₁" => geoAt P s (nodeC p)
local notation "timeⓅ" => (geoAt P s (nodeC p)) j
omit qa in
lemma extending_clock (P:Spine){s v n:ℕ}(h:s≤ v):P.tock v (P.reachLeaf s v n)=P.tock s n:=by rw [P.tock_price,P.tock_price,reachLeaf]; push_cast; rw [mul_comm _ (n:ℝ),mul_assoc,P.daysF v s h]
-- omit qa
include U
lemma time_pose : timeⓅ=hⓐ s+ℓ/2:=by
 rw [U.reach,geo_tick,P.tock_price]
 unfold moonClock; rw [pay_half]; change (hⓐ s)+_=(hⓐ s)+_; push_cast; ring
private theorem time_law (l:s≤v)(e:(2*(W₀:ℝ)+4)*τ s≤ ℓ) : (dⓐ v)+hⓐ v≤ timeⓅ ∧ dⓐ v-hⓐ v ≤ ℓ-timeⓅ ∧ timeⓅ ≤ ℓ ∧ ℓ-timeⓅ ≤ ℓ:=by
 have u:=restTick P l; have v₁:= home_room P qa v j; have s₁:=home_room P qa s j; have w:(dⓐ v)≤(dⓐ s):=mul_le_mul_of_nonneg_left u (by positivity); have t':0≤ (dⓐ s):=mul_nonneg (by positivity) (P.macroStep_pos s).le
 rw [time_pose P p j qa U]; rw [abs_le] at v₁ s₁; refine ⟨?_,?_,?_,?_⟩ <;> linarith
lemma time_receiptOp (l:s≤v)(e:(2*(W₀:ℝ)+4)* τ s≤ ℓ) (i:P.VMark)(z:P.laysM i=Y₁-home P a f):
 𝒦 i (rawSolo P M j x qa y q f g₀ timeⓅ (ℓ-timeⓅ))= mineV P p U.cost j x y q:=by
 let tp:=timeⓅ; obtain ⟨t,r⟩:=position_ticks P p M a l U; have ht:=position_p P p M a l U t r; have h:= (time_law P p j qa U l e); have h':tp-hⓐ v=P.tock v (t j):=(congrFun ht j).symm; let S:=ℓ-timeⓅ
 have pL:(Φ).realWidth P j≤tp-hⓐ v:=by rw [solo_width]; exact le_sub_iff_add_le.mpr h.1
 have pR:(Φ).realWidth P j≤S+hⓐ v:=by rw [solo_width]; exact (sub_le_iff_le_add).mp h.2.1
 rw [anchor_move P M j x qa y q f g₀ _ (P.vtile v t) (by rw [z,ht,seated]; abel)]
 let w₀:=moonSpan P s; let W:= P.reachLeaf s v w₀
 have he : (P.vtile (Φ).s t)=P.vtile v t:=rfl
 have hh:= ((Φ).dyedHere P j x (w:=W) (t j) (tp-hⓐ v) (S+hⓐ v) h'.symm (by
    change P.tock v (P.reachLeaf s v w₀) - (tp - hⓐ v)= S+hⓐ v; rw [extending_clock P l,P.tock_price]; push_cast; unfold S tp moonClock; unfold w₀; abel) pL pR).shiftCap t
 -- Thread resulting equality: shifts -tj (chartAll t(shifts tj F))→chartAll t F
 rw [he] at hh; refine (mineValue P p U.cost j x y q _).1 (hh.mono rfl ?_)
 rw [chartAll,P.cruise_mesh, P.shifts_sum,neg_add_cancel,P.shifts_zero]; change P.chartAll t (τEnd P v (homeTag P a) y q)= _; rw [r,temple_sweep]
-- extend s/g at ANY anchor f0 in common cover
include pZ W WX k h
local notation "g¹" => g+1
local notation "c★" => (ageBudget P η A C H s)
local notation "m★" => (↑(portGain Wq):ℂ)
local notation "s★" => sprintCost P.par.R.L
lemma rewed (l:s<g)(e:(2*(W₀:ℝ)+4)* τ s≤ ℓ) (u':ℓ≤u)(d':ℓ≤d) (p₁:payable P g 2)(p₂:payable P (g+1) 2)(f₁:f0 ≤ s) (g₁:f ≤ g):
 ‖m★ • rawSolo P M j x qa pseV p₂ f (g₁.trans (Nat.le_succ _)) u d-rawSolo P M j x qa pseV p₁ f g₁ u d‖≤ 4*c★*(s★ ^(g-s))⁻¹:=by
 let hw:g+0 ≤ g+1:= Nat.le_succ g; let w:= mineV P p U.cost j x pseV p₁; let hp:=winning P p U.cost h pZ W WX k j x l f₁; let m:= chair P M a g₁
 obtain ⟨t,r⟩:=position_ticks P p M a h U; let i:P.VMark:= P.vtile g t - m; have he:P.laysM i=Y₁-home P a f:=by unfold i m; rw [laysDiff,position_p P p M a h U t r,seated]; abel
 let W' := time_law P p j qa U (v:=g) h e; let W₁:= time_law P p j qa U (v:=g+1) (h.trans (Nat.le_succ _)) e; have hg:= (W'.2.2.1.trans u'); have hm:= (W'.2.2.2.trans d')
 rw [raw_cap P M j x qa pseV p₂ f _ W₁.1 W₁.2.1 hg hm, raw_cap P M j x qa pseV p₁ f _ W'.1 W'.2.1 hg hm, ← map_smul, ←map_sub]; refine ((σ).pad_le ..).trans ?_
 rw [←P.charter_cost j x i,P.charter_sub,P.charter_smul, time_receiptOp P p M j x qa _ p₂ f _ U (h.trans (Nat.le_succ _)) e i he,time_receiptOp P p M j x qa _ p₁ f g₁ U h e i he]; exact hp -- order side goals tough. edit
omit h
omit U
variable (p':Cover)(B: ShowField P (g+1) (homeTag P a) p')
include B in
lemma raw_fee (β: (2*(W₀:ℝ)+4)* τ (g+1)≤ moonClock P (g+1)) (u':moonClock P (g+1)≤u)(d':moonClock P (g+1)≤d)(p₂:payable P (g+1) 2)(f₁:f0 ≤ g)(g₁:f ≤ g+1):
 ‖rawSolo P M j x qa pseV p₂ f g₁ u d‖≤2*Real.exp 1:=by
 obtain ⟨t,r⟩:=position_ticks P p' M a le_rfl B; let i:P.VMark:= P.vtile (g+1) t - chair P M a g₁; have he:P.laysM i=geoAt P (g+1) (nodeC p')-home P a f:=by unfold i; rw [laysDiff,position_p P p' M a (by rfl) B t r,seated]; abel -- le_rfl
 let W₁:= time_law P p' j qa B (v:=g+1) le_rfl β
 rw [raw_cap P M j x qa pseV p₂ f _ W₁.1 W₁.2.1 (W₁.2.2.1.trans u') (W₁.2.2.2.trans d')]; refine ((σ).pad_le ..).trans ?_
 rw [←P.charter_cost j x i,time_receiptOp P p' M j x qa pseV p₂ f g₁ B le_rfl β i he]; exact capEntry P p' pZ W WX k j x f₁ B.cost p₂
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
