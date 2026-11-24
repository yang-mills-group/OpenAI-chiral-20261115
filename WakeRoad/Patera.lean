import WakeRoad.Valencia
import WakeRoad.Tallow
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
open CF.Onyx
open CF.Gingham.Ruff Spine.Gingham.VoyageB
open UVNext.FreeStress
variable (P:Spine)(r:ℕ→ℕ)
local notation "iₛ" i:max=>P.period (P.projection.rows (r i))
local notation "kₛ" i:max=>P.cutoff (P.projection.columns (r i))
local notation "nDoc" s:max i:max=>side P.run (iₛ i) s
local notation "Mₛ" s:max i:max=>P.par.V.L.H ((P.run).uv (kₛ i)-s)
local notation "R*" s:max=> ((↑(2*ArborJet.moment P s:ℕ):ℂ))
local notation "ff"=> (4* Maxwell.normal)
variable {m:ℕ}
lemma holy_hint (i j: Postcard m): normalKernel (takeIn i) (takeIn j)=((ff:ℝ):ℂ)* ((ArborJet.stamp true j:ℝ):ℂ) * pattern takeIn i j:=by
 rw [radiance]; unfold ArborJet.stamp takeIn pattern; simp [anis]
variable (s n:ℕ)
local notation "K"=>RootBook P.run (iₛ n) (kₛ n) s
local notation "ι"=>Postcard ((K).p.B/10)
variable {a c μ:ℝ}{l:ℕ}{δ C:ℝ}(B:Scene P a c μ l s (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))))(X:Rialto 6 P.par.d δ C)
local notation "A*" b:max=> grove P s (iₛ n) (kₛ n) b
local notation "w*"=> cocoa P s (iₛ n) (kₛ n) B X
local notation "G*" b:max=>combo P s (iₛ n) (kₛ n) B X b
abbrev salute (i j:Postcard ((RootBook P.run (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))) s).p.B/10)):ℂ:= (R* s)^4 * chipbook (M:=Mₛ s n) (A* false) (A* true) i j
-- Numerical sale :) use inequality only at activated s.
variable (κ:ℕ→ℝ)
abbrev braid_st {m:ℕ}:WakeRoad.Press (Postcard m) := fun i j=>normalKernel (takeIn i) (takeIn j)
lemma shield_st {m:ℕ}(i j:Postcard m) : ‖braid_st i j‖ ≤ ff:=by rw [braid_st,holy_hint,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<ff from by have :=Maxwell.normal_pos; positivity),Complex.norm_real,Real.norm_eq_abs,stamp_abs]; simp [pattern]; split <;> simp; have:=Maxwell.normal_pos; positivity
lemma affinity_charge {m:ℕ}{U:WakeRoad.Press (Postcard m)}(h:∀i j,U i j=U j i):
 affinity braid_st (portrait true U) (portrait false U)=
 (ff^2:ℝ) • ((2:ℂ)* (↑(∑i:oxygen,∑j:oxygen,‖WakeRoad.compact takeIn U i j‖^2:ℝ):ℂ)):=by
 have t:portrait true U=(fun i j=> (ArborJet.stamp true i * ArborJet.stamp true j) • star (U i j)):=by funext i j; simp [portrait,medley]
 have v:portrait false U=U:=by funext i j; simp [portrait,medley,ArborJet.stamp]
 rw [t,v, show (braid_st (m:=m))=(fun i j=>((ff:ℝ):ℂ)* (ArborJet.stamp true j:ℝ)*pattern takeIn i j) from funext fun i => funext fun j=> holy_hint ..,mirror_pay U takeIn (ArborJet.stamp true) (fun i=>stamp_abs i true),favor U takeIn h]

-- fix convergence with quant constants. Use ε=... and lower p.d etc.
lemma income_delta (h:StrictMono r)(A:ℝ)(t:0<A)(ε:ℝ)(v:0<ε) :
 ∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,
  (RootBook P.run (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))) s).p.B=Pressure.radiusB (hat P.par.R.L P.par.x s) →
  ∀ (U:WakeRoad.Press (Postcard ((RootBook P.run (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))) s).p.B/10))), WakeRoad.coin U≤ A →
    ‖affinity (salute P r s n) (portrait true U) (portrait false U) - affinity braid_st (portrait true U) (portrait false U)‖≤ε:=by
 -- use valencia and cast via generalization changing m
 let Q':ℝ:=ff + 1
 have q:0<Q':=by unfold Q'; have := Maxwell.normal_pos; positivity
 let v₀:=min 1 (ε / (A * A * (4*Q'))); have hδ:0 < v₀:=lt_min one_pos (by positivity)
 filter_upwards [p_score P r v₀ hδ h] with s l
 filter_upwards [l] with n l z U t₁
 have he:∀ i j:Postcard ((RootBook P.run (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))) s).p.B/10), ‖salute P r s n i j-braid_st i j‖ ≤ v₀:=by
    unfold salute grove; -- general rewrite card binder s EQ
    rw [z]; intro i j
    specialize l i j; rw [delta_b,dist_eq_norm] at l; push_cast at l ⊢; exact l.le
 have hs(i j:Postcard ((RootBook P.run (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))) s).p.B/10)): ‖salute P r s n i j‖ ≤ Q':= by have v':=he i j; have t:=norm_sub_norm_le (salute P r s n i j) (braid_st i j); have j': v₀≤1:=min_le_left ..; have hz:= shield_st i j; unfold Q'; linarith
 refine (lateral (portrait false U) (portrait true U) _ _ Q' v₀ he hs (fun i j=> (shield_st i j).trans (by unfold Q';linarith))).trans ?_
 rw [portrait_coin,portrait_coin]; have v': v₀*(A * A * (4*Q'))≤ε:=(le_div_iff₀ (by positivity)).mp (min_le_right 1 _)
 have u: (WakeRoad.coin U* WakeRoad.coin U)*(4*Q'*v₀) ≤ (A * A)*(4*Q'*v₀):= by have := WakeRoad.coin0 U; gcongr
 exact u.trans (v'.trans' (le_of_eq (by ring)))
