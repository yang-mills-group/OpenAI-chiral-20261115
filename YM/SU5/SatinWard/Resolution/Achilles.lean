import YM.SU5.SatinWard.Resolution.Staircase
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
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
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
variable {s:ℕ}(P:Spine) (a b' c d:ℝ) -- rebind unsafe? use P implicit for later. gauge R aliasOf.
open BProof Pressure
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
local notation "K'"=> P.calibration
local notation "x'" u:max=> P.par.x u -- not use
local notation "τ" s:max=> Pressure.temp (hat P.par.R.L P.par.x s)
local notation "B'"=> sampleP a b'
local notation "V"=> sampleP c d
open _root_.YM.Gleam.Luster.Almanac Grade
abbrev payable (P:Spine)(s:ℕ)(x:ℝ):Prop:= x ≤ Moon.voucher (hat P.par.R.L P.par.x s)
lemma eventuallyPay (P:Spine)(w:ℝ):∀ᶠ s:ℕ in atTop, payable P s w:= ((tendsto_rpow_atTop (by norm_num [micr] :0 < (0.1:ℝ)*micr)).comp (turnover P.par)).eventually_ge_atTop w
-- annulus.App.Scope sorts. `permittedHeight p w/ C'^{u}` caller. width estimate derived automatically.
abbrev polishQ (P:Spine)(s:ℕ):=scaleY (hat P.par.R.L P.par.x s)
lemma polish_late : Tendsto (polishQ P) atTop atTop:=by
 let f:=fun x:ℝ=> scaleY x; have T:Tendsto f atTop atTop:=by unfold f; simp_rw [coin_scale]; exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by decide:(2:ℕ)≠0)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))
 exact T.comp (LocalLimit.turnover P.par)
lemma phaseRent (n:ℕ): ∀ᶠ s:ℕ in atTop,0≤ wane (Ω s)∧ wane (Ω s) ≤ 1∧∀ R:ℝ, 1 ≤ R→ R ≤ (polishQ P s)^n→ R^9* wane (Ω s)≤1:=by
 let β(x:ℝ):=(scaleY x)^n; let q:= -(2.5*micr); have t:Grade q wane:=Grade.pitch _; have hx: Grade 0 (fun x=> (β x)^9):=by simpa only [zero_mul] using ( (Grade.stock 0 1).pwr n|>.pwr 9)
 filter_upwards [(turnover P.par).eventually (((hx.mul t).roots (by norm_num [q,micr])).eventually (ge_mem_nhds zero_lt_one)), (turnover P.par).eventually ((t.roots (by norm_num [q,micr])).eventually (ge_mem_nhds zero_lt_one)), (turnover P.par).eventually_gt_atTop 0] with s i h z
 let Q:= Ω s; have he:0≤wane Q:= (Real.rpow_pos_of_pos z _).le; refine ⟨he,h,fun R e p=> (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans e) p 9) he).trans i⟩
lemma footprintA {x y:Cover}{A k:ℕ}(p:∀ i:Axis,(x i-y i).natAbs≤ k) : WidthBudget (pavilion x A∪pavilion y A) (2*A+k):=by
 let u(i:Axis):= min (x i) (y i) - A; refine ⟨u,fun z a i=>?_⟩; specialize p i; dsimp only [u]; cases le_total (x i) (y i) with
 | inl h=> rw [min_eq_left h]; rcases mem_union.mp a with v|v <;> (have ht:=(pav_v ..).mp v i; omega)
 | inr h=> rw [min_eq_right h]; rcases mem_union.mp a with v|v <;> (have ht:=(pav_v ..).mp v i; omega)
lemma widenWidth {S Z:Finset Cover}{a b:ℕ}(p: S ⊆ Z)(q:a≤b)(c:WidthBudget Z a):WidthBudget S b:=by obtain ⟨z,u⟩:= c; exact ⟨z,fun i v j=> ⟨(u i (p v) j).1,(u i (p v) j).2.trans (add_le_add_right (Nat.cast_le.mpr q) _)⟩⟩
lemma rootPermit (Q μ:ℝ)(hq:0≤ Q) (n:ℕ) (A:ℕ) : ∀ᶠ s:ℕ in atTop,∀(x y:Cover)(d:Gaia)(R:ℝ), R≤ polishQ P s ^ n → Addressing x y d μ R Q→ WidthBudget (pavilion x A∪pavilion y A) (budgetWidth (Ω s) (n+1)):=by
 filter_upwards [(polish_late P).eventually_ge_atTop (Q+2*A+4),(polish_late P).eventually_ge_atTop 1] with s h h' x y d R e y0
 let u:=polishQ P s; let N:=pavilion y A; let F:=patchF (x-y) R; let g:= ‖F‖; let K:=(Q+1)*R; have w:= y0.pLease; have hd:0<K:=by unfold K; positivity
 let T := Nat.ceil K; have hv: g ≤ Q+1:=by have hx:μ/R≤ 1:= (div_le_one (by positivity)).2 (by linarith only [y0.lap]); exact (norm_le_norm_sub_add F d).trans ((add_le_add (y0.meters.trans hx) y0.sizes).trans_eq (add_comm ..))
 apply widenWidth (Finset.Subset.refl _) _ (footprintA (k:=T) ?_)
 all_goals rotate_left 0 -- order
 · apply (Nat.cast_le (α:=ℝ)).mp; apply le_trans _ (Nat.le_ceil (R:=ℝ) _); push_cast; rw [pow_succ]; change 2*(A:ℝ)+ ↑T≤ u^n*u; have hx:(T:ℝ)<K+1:=Nat.ceil_lt_add_one hd.le; unfold K at hx; nlinarith only [mul_le_mul_of_nonneg_left e (show 0≤Q+1 by positivity),hx,mul_le_mul_of_nonneg_left (show Q+2*A+4≤u from h) (pow_nonneg (zero_le_one.trans (show 1≤u from h')) n), show 1≤u^n from one_le_pow₀ h', mul_le_mul_of_nonneg_right (show 1≤u^n from one_le_pow₀ h') (Nat.cast_nonneg (α:=ℝ) A)] -- tune
 intro i; apply (Nat.cast_le (α:=ℝ)).mp; apply le_trans _ (Nat.le_ceil K); let Vc:=x-y; have hμ:‖scape Vc‖=R*g:=by rw [show scape Vc=R • F from (smul_inv_smul₀ (show R ≠ 0 from (zero_lt_one.trans_le w).ne') _).symm,norm_smul,Real.norm_of_nonneg (zero_le_one.trans w)]
 have hc: |((x i-y i:ℤ):ℝ)| ≤ _ := show |(shaftX Vc) i| ≤ ‖scape Vc‖ from le_trans (norm_le_pi_norm (shaftX Vc) i) (YM.Stationary.orbit_at ..); rw [hμ] at hc; apply le_trans _ ((hc.trans (mul_le_mul_of_nonneg_left hv (zero_le_one.trans w))).trans_eq (mul_comm ..)); apply le_of_eq; rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
