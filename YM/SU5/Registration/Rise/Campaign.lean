import YM.SU5.Registration.Rise.PitPrices
import YM.SU5.Registration.Rise.EntireCanvas
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
open Worth Pays CF.BProof

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)

/-! # Operator at ANY heated presentation

Maps from fields at a fixed anchor into a taller stage (ruler-overlap fixed) are
in H and are contractive; can pass to ALL matter-free clock leaves in one
norm estimate. When the allowance is spent at both ends the opening line is
operator-norm priced; the screenings at nonaligned points depend on mesh, but
transfer out of mesh on MANY-F via its spatial continuity. Then get Strong Star Cauchy
on the sequence of managed granules.
-/
open Germ Alliance
open _root_.YM.SatinRegistration
variable (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x j
local notation "X'"=> P.ColorHil j ξ
local notation "G"=> P.ManyF j ξ
local notation "U"=> P.truck j ξ
local notation "E"=> (P.physicalEnergy j ξ).E
local notation "S"=> P.seasons j ξ

/-! # Keep account through width-closing

Use `entire` weight average in H for every going kernel allowance. Absolute
price in H. Strong* after compression in G. Does NOT write `CapPrice` by changing
e.g. to vacuum G vectors or introduce a fictitious aligned frame in G; these are
stages on each actual stamp via `stageH` **from this character**. These theorems
can be invoked on any co-purchased estimates in this election.
-/
open SatinNucleus
local notation "π"=>P.toStageG j ξ
variable (g h:ℕ)(l:List Axis)(v':ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(p:StrictMono v')(δ:ℕ→ Coalition)
local notation "J"=> P.cinema x g h v' a δ p
local notation "vβ" v:max=> ((J v).pivot P l)
local notation "Nα" s:max=>whenly (timeMesh P.par) s P.roomy
local notation "ζ" t:max i:max=> P.subsidizedH j x g h l a v' t i
local notation "λκ" t:max i:max=> (P.rewardK g h:ℂ) • (ζ t i)

structure Funding (P:Spine)(x:P.Spectrum0 3)(B:ℕ→P.Apron) : Prop where
 ft : ∀ j:Axis, Tendsto (fun i=> (B i).allowance P j) atTop (𝓝 0)
 price : ∀ j l, RisePrice (fun t i=>P.stageH j (P.advocate 3 x j) ((B i).pivot P l) t t)
 travels : ∀ j l, ∀ t:ℝ≥0, 0<t→ Travels (H:=P.ManyF j (P.advocate 3 x j)) (fun i=> P.stageG j (P.advocate 3 x j) ((B i).pivot P l) t t)

lemma legislations (t:ℝ≥0)(u:Nα (v' i) ≤ t): P.stageH j ξ (((J) i).pivot P l) t t= ∑ k∈(δ i).voters, (((δ i).w k):ℂ) • ( (P.rewardK g h:ℂ) • (P.subsidizedH j x g h l a v' t (i+k))):= P.stage_pledges j v' p _ (δ i) g h i x l t u

section voting
variable {H:Type*}[NormedAddCommGroup H][NormedSpace ℂ H] (X:ℕ→H)
private lemma coalition_prices {B:ℝ}(h:∀ᶠ i:ℕ in atTop, ‖X i‖ ≤ B) : ∀ᶠ i:ℕ in atTop, ‖∑ k∈(δ i).voters,(((δ i).w k):ℂ) • (X (i+k))‖ ≤ B := by
 obtain ⟨N,t⟩:=eventually_atTop.mp h
 filter_upwards [eventually_ge_atTop N] with i p
 let s:=(δ i).voters; let f:=(δ i).w
 apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun k:ℕ=> f k*B) _).trans
 · rw [←sum_mul, (δ i).pledges]; exact (one_mul _).le
 intro k q; let h:= (δ i).signed k q; rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h]; exact mul_le_mul_of_nonneg_left (t (i+k) (by omega)) h
private lemma votes_resolve (x:H) (p:Tendsto X atTop (𝓝 x)) : Tendsto (fun i=>∑ k∈(δ i).voters,(((δ i).w k):ℂ) • X (i+k)) atTop (𝓝 x):=by
 apply Metric.tendsto_nhds.mpr; intro ε t
 let Y'(i):= X i-x
 filter_upwards [coalition_prices δ Y' ( (p.eventually (Metric.ball_mem_nhds x (half_pos t))).mono fun i p=> (show ‖X i-x‖ < ε/2 from dist_eq_norm (X i) x ▸ (show dist (X i) x < _ from p)).le)] with i he
 rw [dist_eq_norm, show ∑ k∈(δ i).voters,(((δ i).w k):ℂ) • X (i+k)-x=∑ k∈(δ i).voters,(((δ i).w k):ℂ) • Y' (i+k) from ?_]; exact he.trans_lt (half_lt_self t)
 -- sum notation parsed without parentheses uses broad? explicit
 unfold Y'; simp only [smul_sub]; rw [sum_sub_distrib,←sum_smul]; congr 1; rw [← Complex.ofReal_sum,(δ i).pledges, Complex.ofReal_one,one_smul]

private lemma votes_fly {H:Hilbert}(F:ℕ→ H.Op)(b:H.Op)(h:Flying F b) : Flying (fun i=>∑ k∈(δ i).voters,(((δ i).w k):ℂ) • F (i+k)) b:=by
 intro x; refine ⟨(votes_resolve δ _ _ (h x).1).congr fun i=> ?_,(votes_resolve δ _ _ (h x).2).congr fun i=> ?_⟩
 · dsimp only; rw [_root_.sum_apply]; rfl
 dsimp only; rw [map_sum]; simp_rw [_root_.sum_apply]; refine sum_congr rfl fun k v=>?_ ; rw [ContinuousLinearMap.adjoint.map_smulₛₗ]; simp
end voting

-- use exact weight from ordered calibration (issued before selection of M4 smears). No need for rate of convex combinations.
include p
lemma width_floor : Tendsto (fun i=> whenly (timeMesh P.par) (v' i) P.roomy) atTop (𝓝 0):=by
 unfold whenly; simpa only [mul_zero,Function.comp_def] using ((vanishes (timeMesh P.par)).comp p.tendsto_atTop|>.const_mul (P.roomy:ℝ≥0))
lemma legislative_shelf : Tendsto (fun i=> ((P.cinema x g h v' a δ p) i).allowance P j) atTop (𝓝 0):=by
 apply (P.width_floor v' p).congr fun i=>?_; apply NNReal.eq; change ((Nα (v' i)):ℝ) = ((((J) i).allowance P j):ℝ); rw [← Apron.width_real]; refine Eq.trans ?_ ( (show ((J) i).realWidth P j=P.roomy*P.macroStep (v' i) from P.pleading_w ..).symm); unfold whenly; rw [NNReal.coe_mul,NNReal.coe_natCast]; rfl

variable (S₁:P.NightCop)(L':Odd P.par.R.L.val) (u:Earnings P A C g h v' a) (tq:∀ᶠ s:ℕ in atTop,treasury A C P s (s+1) (s+1))
local notation "tH" t:max i:max=> P.stageH j ξ ((((J) i).pivot P l)) t t
local notation "q₁" => ((P.rewardK g h:ℝ):ℂ)
include S₁ L' u
lemma legislative_vote (h0:PaidSubsidy g h a) (t:ℝ≥0)(w:0<t): Travels (H:=G) (fun i=> P.stageG j ξ (((P.cinema x g h v' a δ p) i).pivot P l) t t):=by
 obtain ⟨V,v⟩:= Flying.settles (P.site_travels j x g h l a v' S₁ L' u h0 t w)
 let F(i:ℕ): (G).Op:= q₁ • π (ζ t i)
 have ht:Flying F (q₁ • V):= v.scaled tendsto_const_nhds
 refine Flying.Cauchy (Flying.late (votes_fly δ F _ ht) ?_)
 filter_upwards [(P.width_floor v' p).eventually (gt_mem_nhds w)] with i e; change _ = P.toStageG j ξ (tH t i); rw [P.legislations j x g h -- shadow h rename below
   l v' a p δ t (show (Nα (v' i)) ≤ t from (show _<_ from e).le),map_sum]; exact sum_congr rfl fun i e=>by rw [map_smul,map_smul]

include tq
lemma legislative_price : RisePrice (fun t i=> P.stageH j ξ (((P.cinema x g h v' a δ p) i).pivot P l) t t):=by
 let r:ℂ:= P.rewardK g h; obtain ⟨k,C,v,h0⟩:= P.granule_rise_price j x g h l a v' S₁ L' u tq
 refine ⟨k,‖r‖*C,mul_nonneg (norm_nonneg _) v, fun t p₀ tq=>?_⟩
 let W':= (t:ℝ)^k; have hw':0<W':=pow_pos (show 0<(t:ℝ) from p₀) _
 have hx:∀ᶠ i:ℕ in atTop, ‖r • ζ t i‖≤‖r‖*(C/W') :=(h0 t p₀ tq).mono fun i w=>by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hw').mpr ((mul_comm _ W').le.trans w)) (norm_nonneg _)
 filter_upwards [(P.width_floor v' p).eventually (gt_mem_nhds p₀),coalition_prices δ _ hx] with i Y' he
 rw [P.legislations j x g h l v' a p δ t (show (Nα (v' i)) ≤ t from (show _<_ from Y').le)]
 exact (mul_comm W' _).le.trans ((le_div_iff₀ hw').mp ((show _≤ ‖r‖*(C/W') from he).trans_eq (mul_div_assoc ..).symm))

lemma fiscal_camera (e:PaidSubsidy g h a): Funding P x (P.cinema x g h v' a δ p):= ⟨fun j=> P.legislative_shelf j x g h v' a p δ, fun j l=> P.legislative_price j x g h l v' a p δ S₁ L' u tq,fun j l=> P.legislative_vote j x g h l v' a p δ S₁ L' u e⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.fiscal_camera
