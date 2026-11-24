import YM.SU5.Six.Aprons
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
-- The error from the actual front at EVERY sufficiently large r, any desired ε>0.
-- Inspired by written Feather (uses a normalized stock; here use P.frontMat).
variable (P:Spine)(Z:Lead.Clan)
local notation "K"=>P.calibration
local notation "μ"=> (purePrice Z : ℂ)
open Papal Lamour Lamour.Bridge CF.Velvet CF.Pannier.Chancel
abbrev dewGauge (n:ℕ) : Weaver:= meanF ((P.flash n).groundWord Z) (purePrice Z:ℂ)
lemma dew_admits (n:ℕ): Lamour.Bridge.Celeste.Voice (P.dewGauge Z n) (insert 0 (P.flash n).patio):= (has_booth (Lamour.Bridge.Celeste.flourish (P.flash n) Z) μ).mono (subset_insert ..)
lemma dewEquals (n:ℕ): P.tuneK (P.dew_admits Z n)=P.frontMat Z n - μ • 1:=rfl
local notation "E"=> YM.basis (3:Axis)
private def spyBirth(n:ℕ) := riseX n (P.flash n).birth
private def spyText(n:ℕ) := riseX n (P.flash n).death
private lemma born_full {n:ℕ} (h:0<n) : P.spyBirth n=((P.calibration.ℓ:ℝ)/(n:ℝ)) • E + E:=by
 unfold spyBirth flash; ext i; by_cases p:i=3
 · subst i; simp [riseX,moor,kernel0,add_div,h.ne']
 simp [riseX,moor,kernel0,p]
private lemma birth_spell {n:ℕ}(h:0<n): P.spyText n=P.spyBirth n+ E:=by
 unfold spyBirth spyText flash; ext i; by_cases p:i=3
 · subst i; simp [riseX,moor,kernel0,add_div,h.ne']
 simp [riseX,moor,kernel0,p]

private def look_text (n:ℕ)(_i:Fin 1):Twah:= liftS (P.flash n)
local notation "D" n:max=> nearPoints n (P.look_text n)
private lemma fresh_pages : ∀ᶠ n:ℕ in atTop, Spill (P.look_text n) 4 1 n := by
 filter_upwards [eventually_gt_atTop 0,eventually_ge_atTop (K).ℓ] with n v h
 let B:= P.spyBirth n; have hb:P.spyText n=B+E:=P.birth_spell v
 have he:‖B‖≤2:=by
    unfold B; rw [P.born_full v]
    refine (norm_add_le ..).trans ?_; rw [norm_smul, YM.basis_norm,mul_one,Real.norm_of_nonneg (by positivity)]
    have ht:((K).ℓ:ℝ)/(n:ℝ)≤1:= (div_le_one (by exact_mod_cast v : (0:ℝ)< n)).mpr (by exact_mod_cast h); linarith only [ht]
 have hx:dist (P.spyText n) (P.spyBirth n)=1:=by rw [hb,dist_eq_norm,show B+E-P.spyBirth n=E from _root_.add_sub_cancel_left ..,YM.basis_norm]
 constructor
 · rintro ⟨k,_|_⟩; refine dist_zero_right (P.spyBirth n) |>.trans_le (he.trans (by norm_num)); refine (dist_zero_right (P.spyText n)).trans_le ?_; rw [hb]; exact (norm_add_le B E).trans (by rw [YM.basis_norm]; linarith only [he])
 rintro ⟨u,_|_⟩ ⟨y,_|_⟩ h; exact (h rfl).elim; exact Eq.ge ((dist_comm _ _).trans hx); exact hx.ge; exact (h rfl).elim

local notation "Γ" => (fun _:Fin 1=> Z)
local notation "B" n:max=> plait (P.look_text n) Γ [0] n
local notation "ν" n:max=> Twah.witness Γ [0] (D n) (fun _=>(0,0))
local notation "α"=> Lead.cash false
private lemma page_price {n:ℕ}(h:0<n) : α * (ν n)=μ := by
 rw [Cordial.chorus2,Cordial.lyric,Cordial.billX]; change α*(Cordial.numberX Z*Onyx.pencil (P.spyText n-P.spyBirth n) (dnSpin 0) (upSpin 0))= μ
 rw [birth_spell P h, _root_.add_sub_cancel_left,show Onyx.pencil E _ _= P20 from k_birth]; rw [price_as]; unfold Cordial.numberX; rw [show α=(1/5:ℂ) by simp [Lead.cash,phaseF]]; ring
private lemma bench_principal {n:ℕ}(h:0<n) : P.dewGauge Z n= α • meanF (B n) (ν n):=by
 let y₀:= P.flash n; change meanF (y₀.groundWord Z) μ=_; rw [Designs.transferMark, show y₀.wave=false from rfl]; let p:= P.look_text n (0:Fin 1); rw [show B n= (liftS y₀).groundWord n Z from mul_one _]; unfold meanF; rw [smul_sub,smul_smul,P.page_price Z h] -- rewrite ν not reduced?
lemma front_fresh (ε:ℝ)(u:0<ε): ∀ᶠ n:ℕ in atTop, Clarity (P.dewGauge Z n) P.par.K.j ε :=by
 rw [P.par.kJ]; filter_upwards [aroma 4 Γ [0] (fun _=>(0,0)) (by decide) ε (u:=1) zero_lt_one 4 u,eventually_gt_atTop 0,P.fresh_pages] with i k h e
 rw [P.bench_principal Z h]; filter_upwards [k (P.look_text i) e rfl] with N x t M y g; change ‖alleyR (CF.Dial.mateK N) y (α • _)‖ ≤ ε
 rw [map_smul,norm_smul]; refine (mul_le_mul_of_nonneg_left (x t M y g) (norm_nonneg _)).trans ?_; rw [show α=(1/5:ℂ) by simp [Lead.cash,phaseF]]; norm_num; linarith -- tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.dew_admits
#print axioms Spine.dewEquals
#print axioms Spine.front_fresh
