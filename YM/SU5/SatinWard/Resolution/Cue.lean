import YM.SU5.SatinWard.Resolution.Rhombus
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
noncomputable def stride (P:Spine)(v:ℕ):ℕ:=Nat.ceil (5*log (polishQ P v))
noncomputable def corridorHeight(P:Spine)(v:ℕ):ℕ:= v-stride P v
noncomputable def corridorR (P:Spine)(v:ℕ):ℝ:= moonClock P (corridorHeight P v)/Selected.gaugeMesh P.par v
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
local notation "x" i:max=> (moonSpan P i:ℝ)
lemma faderP (i:ℕ): (1:ℝ) ≤ Xᵤ i:= by unfold polishQ; rw [coin_scale]; exact Real.one_le_exp (sq_nonneg _)
lemma cue_drift : ∀ᶠ k:ℕ in atTop, 2*stride P k+1 ≤ k:=by
 have hv:0≤p₀:=Vale.pitch _; have hw:0<1+p₀:=by linarith
 filter_upwards [(turnover P.par).eventually (coin_budget (show 0< (1:ℝ)∨ _ from Or.inl zero_lt_one) 1 (1/(20*(1+p₀))) (by positivity) (b:=1) (c:=0) (e:=0) («f»:=0)), (turnover P.par).eventually_gt_atTop 0, (tendsto_natCast_atTop_atTop («R»:=ℝ)).eventually_ge_atTop (P'+12)] with i q h ht
 rw [one_mul,coinY h] at q; let x₀:=Ω i; let y:= Xᵤ i; change y < 1/(20*(1+p₀))*(Ω i) at q; have hy:1≤y:=faderP ..; have hr: (stride P i:ℝ) ≤5*log y+1:= (Nat.ceil_lt_add_one (show 0≤5*log y by exact mul_nonneg (by norm_num) (Real.log_nonneg hy))).le
 have he:20*y ≤ x₀/(1+p₀):=by
    unfold x₀; refine le_trans (b:=20*(1/(20*(1+p₀))*_)) (mul_le_mul_of_nonneg_left q.le (by norm_num)) (le_of_eq ?_); field_simp
 have hs:x₀=P'+i*p₀:=by unfold x₀ hat; ring
 have hb:20*y ≤ i:= he.trans ((div_le_iff₀ hw).mpr (by change (i:ℝ) ≥_ at ht; rw [hs]; linarith))
 have hg:(0:ℝ) < P':=(Real.exp_pos _).trans_le P.large; have hh:=Real.log_le_self (zero_le_one.trans hy); change (i:ℝ) ≥_ at ht; exact_mod_cast (show 2*(stride P i:ℝ)+1 ≤ i by linarith)
lemma cue_p : ∀ᶠ k:ℕ in atTop, 0<T' k:=by filter_upwards [(polish_late P).eventually_gt_atTop 1] with k p; exact Nat.ceil_pos.mpr (mul_pos (by norm_num) (Real.log_pos p))
lemma f_still : ∀ᶠ k:ℕ in atTop, f k < k∧ k-f k=stride P k:=by filter_upwards [cue_p P,cue_drift P] with k u p; unfold corridorHeight; omega
lemma cue_infinite:Tendsto (corridorHeight P) atTop atTop:=tendsto_atTop.mpr fun i=>by filter_upwards [cue_drift P,eventually_ge_atTop (2*i)] with k u p; unfold corridorHeight; omega
lemma shift_late : ∀ᶠ s:ℕ in atTop,∀ k:ℕ,s≤ k → lapQ P.run s≤ (2:ℝ)^(k-s)*lapQ P.run k:=by
 filter_upwards [eventually_forall_ge_atTop.mpr ((turnover P.par).eventually (pal_U L p₀ (Vale.pitch _)) )] with s h k u
 induction u with
 | refl=> rw [Nat.sub_self,pow_zero,one_mul]
 | @step v w ih=> let t':= (h _ w).2.2; rw [Nat.succ_sub w,pow_succ,mul_assoc]; exact ih.trans (mul_le_mul_of_nonneg_left (by rw [show lapQ P.run (v+1)= allotΨ L (Ω v+p₀) from by rw [←paceEq]]; exact t') (by positivity))
lemma corridorValue (s:ℕ) : R▶ s= ζ * (x (f s))* ν^(s-f s):=by unfold corridorR moonClock; rw [←P.daysF s (f s) (Nat.sub_le ..), ←macroUnit]; have he:=gaugeMesh_pos P.par s; field_simp
lemma roomρια : ∀ᶠ s:ℕ in atTop, (ζ:ℝ) * (x (f s))≤ Xᵤ s:=by
 have hr(s:ℕ):1 ≤ Ω s:=(le_trans (Real.one_le_exp (by norm_num: (0:ℝ)≤1)) P.large).trans (Vale.crown ..)
 have hu(i j:ℕ)(p:i≤j): Ω i ≤ Ω j:=by unfold hat; gcongr; exact Vale.pitch _ -- goal order
 filter_upwards [(turnover P.par).eventually (leap (w:=0) (p:=1) (q:=0) (Pays.scale (ζ:ℝ) forest_rental) (Or.inr (Or.inl ⟨rfl,zero_lt_one⟩)))] with s t'
 have hm:radiusB (Ω (f s)) ≤ radiusB (Ω s):= Nat.ceil_mono (pow_le_pow_left₀ (Real.log_nonneg (hr _)) (Real.log_le_log (zero_lt_one.trans_le (hr _)) (hu _ _ (Nat.sub_le ..))) _)
 refine le_trans (mul_le_mul_of_nonneg_left (?_ : x (f s) ≤ ((plateMeter (radiusB (Ω s))):ℕ)) (by positivity : 0≤(ζ:ℝ))) t'; unfold moonSpan ; rw [show P.thresholdF (f s) = radiusB (Ω (f s)) from (P.run.meter.boot _).2.1]; apply Nat.cast_le.mpr; unfold plateMeter; gcongr
variable (G:64 ≤ P.par.R.L.val)
include G
lemma polish_Rscope :∃ n:ℕ,∀ᶠ s:ℕ in atTop,Xᵤ s ≤ R▶ s ∧ R▶ s ≤ (Xᵤ s)^n:=by
 let C:ℝ:= log ν; obtain ⟨n,h⟩:= exists_nat_gt (6*C);
 have hu:(64:ℝ)≤ν:=by exact_mod_cast G
 have hv:1≤C:=by
    unfold C; rw [← Real.exp_le_exp, Real.exp_log (by linarith)]; linarith only [hu,Real.exp_one_lt_d9]
 refine ⟨n+1,?_⟩
 filter_upwards [roomρια P,f_still P,(Real.tendsto_log_atTop.comp (polish_late P)).eventually_ge_atTop 1] with s z q e
 let p:= Xᵤ s; change 1≤log p at e; let k:=stride P s; let i:= f s; have hx:0 < p:= (zero_lt_one.trans_le (faderP P s)); have hν: 0<ν:=by linarith
 have ht:5* log p ≤ k:=Nat.le_ceil _; have hk:(k:ℝ)≤ 6*log p:=(Nat.ceil_lt_add_one (show 0≤5*log p by linarith)).le.trans (by linarith);
 have h₁: p≤ ν^k:=by rw [←Real.log_le_log_iff hx (by positivity),Real.log_pow]; change _ ≤ (k:ℝ)*C; nlinarith
 have h₂:ν^k ≤ p^n:=by rw [←Real.log_le_log_iff (by positivity) (pow_pos hx n),Real.log_pow,Real.log_pow]; change (k:ℝ)*C ≤ n*log p; nlinarith only [mul_le_mul_of_nonneg_right hk (by linarith:0≤C),mul_le_mul_of_nonneg_right h.le (show 0≤log p by linarith)]
 rw [corridorValue,q.2]; exact ⟨h₁.trans (le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.succ_le_of_lt P.sides_pos) (by exact_mod_cast Nat.succ_le_of_lt (reachM P (f s))))),(mul_le_mul z h₂ (by positivity) hx.le).trans_eq (pow_succ' p n).symm⟩
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
