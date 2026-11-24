import WakeRoad.Croton
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
variable (s n:ℕ)
local notation "K"=>RootBook P.run (iₛ n) (kₛ n) s
local notation "ι"=>Postcard ((K).p.B/10)
variable {a c μ:ℝ}{l:ℕ}{δ C:ℝ}(B:Scene P a c μ l s (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))))(X:Rialto 6 P.par.d δ C)
local notation "A*" b:max=> grove P s (iₛ n) (kₛ n) b
local notation "w*"=> cocoa P s (iₛ n) (kₛ n) B X
local notation "G*" b:max=>combo P s (iₛ n) (kₛ n) B X b
open Regis.Wake
abbrev seedVolume(x:ℝ):ℝ:= Fintype.card (Postcard (Pressure.radiusB x/10))
private lemma price_chart: Pressure.Worth.Pays 0 16 0 seedVolume:=by -- duplicate
 open Pressure.Worth in
 let v:= Pays.rising
 let f(x:ℝ):=2*(Pressure.radiusB x:ℝ)+1
 open Pressure.Worth in
 have h : Pays 0 0 2 f := Pays.plus (Pays.scale 2 Pays.rising) (Pays.merit (Pays.constant 1) (by norm_num [Earlier]))
 let K' :ℝ:=Fintype.card PlaqAxes * (Fintype.card SU.group.ColorIndex:ℝ)
 have p:Pressure.Worth.Pays 0 16 0 (fun x=> f x^4 * K'):= Pressure.Worth.Pays.merit (Pressure.Worth.Pays.right K' (Pressure.Worth.Pays.pot h 4)) (by norm_num [Pressure.Worth.Earlier])
 refine Asymptotics.IsBigO.trans ?_ p; apply Asymptotics.isBigO_iff.mpr
 refine ⟨1, Eventually.of_forall fun x=>?_⟩
 have hc:f x≥0:=by unfold f; positivity
 have hz:K'≥0:=by unfold K'; exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
 unfold seedVolume Postcard; rw [one_mul,Real.norm_eq_abs, Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg hc _) hz),Fintype.card_prod,Fintype.card_prod,Fintype.card_coe,Corona.box_size]; rw [abs_of_nonneg (by positivity)]
 push_cast; rw [mul_assoc]; apply mul_le_mul_of_nonneg_right _ hz; apply pow_le_pow_left₀ (by positivity)
 unfold f; have ht : (↑(radiusB x/10):ℝ) ≤ ↑(radiusB x):= Nat.cast_le.mpr (Nat.div_le_self ..); linarith
#print axioms price_chart
abbrev sage (P:Spine)(d:ℝ)(x:ℝ) := 2*|d| * Regis.Wake.assay 2 (leaseR P.par.K.top.clip) (seedVolume x)
private lemma stale (d:ℝ):Pressure.Worth.Pays 0 16 0 (sage P d):= by
 let Y:=leaseR P.par.K.top.clip
 open Pressure.Worth in
 let t:= Pays.merit (Pays.constant 1) (show Earlier 0 0 0 0 16 0 by norm_num [Earlier])
 unfold sage assay
 exact Pressure.Worth.Pays.scale (2*|d|) (Pressure.Worth.Pays.scale _ (Pressure.Worth.Pays.plus t (Pressure.Worth.Pays.right _ price_chart)))

abbrev fuzzy (x:ℝ):ℝ := chip x (-3)
abbrev waste (P:Spine)(d:ℝ)(x:ℝ):ℝ:=fuzzy x+(fuzzy x*sage P d x + (sage P d x+fuzzy x)*fuzzy x)
lemma fuel_split (A B C X Y Z:ℂ)(d s t:ℝ)(h:0≤d)(s':0≤ s)(p:0≤t) (v:‖X‖≤ s)(w:‖Y‖≤ s)(t₁:‖A-X‖≤t)(t₂:‖B-Y‖ ≤ t)(q:‖C-Z‖ ≤t)(ε:ℝ)
 (u:ε ≤ ((d:ℂ)*(Z-X*Y)).re): ε - d*(t+(t*s+(s+t)*t)) ≤ ((d:ℂ)*(C-A * B)).re :=by
 have t₃:‖A‖≤ s+t:= by have ht:=norm_sub_norm_le A X; linarith
 have hv:‖A * B-X*Y‖≤t*s+(s+t)*t:=by rw [show A * B-X*Y=(A-X)*Y+A * (B-Y) from by ring]; exact (norm_add_le ..).trans (add_le_add (norm_mul_le ..|>.trans (mul_le_mul t₁ w (norm_nonneg _) p)) ((norm_mul_le ..).trans (mul_le_mul t₃ t₂ (norm_nonneg _) (add_nonneg s' p))))
 have Hz:= (Complex.re_le_norm (((d:ℂ)*(Z-X*Y))-(d:ℂ)*(C-A * B)))
 rw [Complex.sub_re,←mul_sub,show Z-X*Y -(C-A * B)=(A * B-X*Y)-(C-Z) by ring,norm_mul,Complex.norm_real,Real.norm_of_nonneg h] at Hz
 have hG := mul_le_mul_of_nonneg_left (norm_sub_le .. |>.trans (add_le_add hv q)) h
 linarith
open Pressure.Worth
lemma master (d:ℝ): Tendsto (fun s:ℕ=> (((2*ArborJet.moment P s:ℕ):ℝ))^8*waste P d (hat P.par.R.L P.par.x s)) atTop (𝓝 0):=by
 let q(x):ℝ:=2*BProof.coin x 0 13 0
 have h :Pays 0 13 0 q:= Pays.scale 2 (Pays.whole ..)
 have hp:Pays (-3/400000) 0 0 fuzzy:= Pays.whole ..
 have hr:= (Pays.times hp (stale P d)); have he:= (Pays.times (Pays.plus (stale P d) (Pays.merit hp (Or.inl (by norm_num)))) hp)
 have HX: Pays (-3/400000) 16 0 (waste P d):=by simp only [zero_add,add_zero] at hr he; unfold waste; apply Pays.plus (Pays.merit hp (by norm_num [Earlier])); exact Pays.plus hr he
 have ht: Tendsto (fun s=>q s^8*waste P d s) atTop (𝓝 0) := Pays.limit (Pays.times (Pays.pot h 8) HX) (Or.inl (by norm_num))
 have hv(x):0≤waste P d x:= by unfold waste fuzzy sage; have ht:= (chip_pos x (-3)); have hi:0≤ seedVolume x:=Nat.cast_nonneg _; unfold assay; positivity
 refine squeeze_zero' (Eventually.of_forall (fun s=>by have := hv (hat P.par.R.L P.par.x s); positivity)) ?_ (ht.comp (turnover P.par))
 filter_upwards [zoom_pays (P:=P) 12 (by norm_num)] with s p
 change ((↑(_* _ :ℕ):ℝ)^8*waste P d _ ≤ q (hat P.par.R.L P.par.x s)^8*waste P d _)
 push_cast; apply mul_le_mul_of_nonneg_right _ (hv _); apply pow_le_pow_left₀ (by positivity); norm_num at p; exact mul_le_mul_of_nonneg_left p (by norm_num)
#print axioms master
