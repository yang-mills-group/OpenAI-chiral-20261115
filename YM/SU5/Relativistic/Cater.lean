import YM.SU5.Relativistic.Lord
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots Precision RG Work.F03
open Next.SectorChange
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable (G : Gauge){W : Side}
local notation "X"=> Config G W
local notation "H"=> Face (Per W)
local notation "ι"=> livelies W
local notation "F"=> Lo W
local notation "Y"=> F→ G.El
open GaugeFlux Pageant
open SectorNext.Vacuum Metric
open scoped Classical
-- W tile
local notation "δ"=> Fintype.card (Fresco G W)
local notation "Z"=> Prices G (Lo W)
variable (p:Clip) {σ C Λ:ℝ}(a:ChartRatio G) (D:ℕ)(hy:LocalRatio a)
include hy
def plainH (W:Side)(x:ℝ) (a: ChartRatio G)(V:Matrix (Fresco G W) (Fresco G W) ℝ): Prices G (Lo W) →ℝ:= fun z=>a.scale^Fintype.card (Lo W)*coldFee (x • V) z
lemma host_meas {d x b:ℝ}(V:PathData G)(B: V.Bounds p σ C Λ): Measurable (hostP (W:=W) G p a D d x V b):=by
 let p':=lay_c G (W:=W); have pf:= box_c G V D B (W:=W); let A:=(1:Y)
 have he:Continuous (fun y=> wealthy G p D x V b (release A y)):=by have hp:=p'; unfold wealthy; fun_prop
 exact (((pay_meas hy).mul he.measurable).indicator ((isCompact_univ_pi (fun _=>ProperSpace.isCompact_closedBall ..) : IsCompact (chamber G W d)).measurableSet)).comp (tape.measurable.comp (show Measurable (fun z:Z=> coupling x • z) by fun_prop))
lemma plane_meas (η:ℝ)(V: Matrix (Fresco G W) (Fresco G W) ℝ) : Measurable (plainH G W η a V):=by unfold plainH coldFee Matrix.mulVec dotProduct; fun_prop
lemma scaleH (x θ:ℝ)(q:0<x)(t:0<θ)(U:PathData G)(B:U.Bounds p σ C Λ):
 Integrable (plainH G W θ a (DueQ G U D B W)) ∧ ∫ i:Z, plainH G W θ a (DueQ G U D B W) i=(Real.sqrt x)^δ * fee G W x a θ (DueQ G U D B W).det:=by
 obtain ⟨u,v⟩:= gram_p ((screenP G U D B W).1.smul t); refine ⟨u.const_mul _,?_⟩; unfold plainH; rw [integral_const_mul,v,Matrix.det_smul]; unfold fee Next.SectorChange.spare Gaussian.dome coupling; rw [Real.sqrt_mul (by positivity : 0≤2*Real.pi) ((Real.sqrt x)⁻¹^2),Real.sqrt_sq (by positivity)]; unfold Fresco; rw [Fintype.card_prod]; simp only [mul_pow,inv_pow,div_eq_mul_inv]; rw [pow_mul',pow_mul']; -- tune rearrange
 have hx:=Real.sqrt_pos.mpr q; have ht:0<Real.sqrt (θ^(Fintype.card F*Fintype.card G.ColorIndex)*(DueQ G U D B W).det):=Real.sqrt_pos.mpr (mul_pos (pow_pos t _) (screenP G U D B W|>.1.det_pos)); field_simp; rw [pow_mul'] -- tune

variable (x:ℕ→ℝ)(hx:Tendsto x atTop atTop)(U:ℕ→PathData G)(B:∀ i,(U i).Bounds p σ C Λ)
include hx B
lemma reign {η d:ℝ}(v:0<η)(u:0<d)(z:Z) : Tendsto (fun i=> hostP G p a D d (x i) (U i) η z-plainH G W η a (DueQ G (U i) D (B i) W) z) atTop (𝓝 0):=by
 let g(i:ℕ):= coupling (x i); have ht:Tendsto g atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hx)
 have he:= hx.eventually_gt_atTop 0; have hf:Tendsto g atTop (𝓝[≠] 0):= tendsto_nhdsWithin_iff.mpr ⟨ht, he.mono fun i t=>(coupling_pos t).ne'⟩ -- tune membership
 let V:= brightQ G W z; let y(i:ℕ):=(g i)⁻¹^2*boxE G (U i) D p (represent (g i • V)); let Y'(i:ℕ):= -(η*y i)/2
 let P(i:ℕ):= η • (DueQ G (U i) D (B i) W)
 let Q(i:ℕ):= -(dotProduct z (P i *ᵥ z))/2
 have hq(i:ℕ): Q i ≤ 0:=by unfold Q; apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num); rw [neg_nonpos]; simpa using ((screenP G (U i) D (B i) W).1.smul v).posSemidef.dotProduct_mulVec_nonneg z
 have hX:Tendsto (fun i=> Y' i-Q i) atTop (𝓝 0):=by
    have he' := (slips G p D U g B hf z).const_mul (-(η/2)); rw [mul_zero] at he'; refine he'.congr' (Eventually.of_forall ?_); intro i; unfold Y' Q y P V; dsimp only; rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]; ring
 let c(i:ℕ):= tape (G:=G) (g i • z); let B':= a.scale^Fintype.card F
 have hh:Tendsto c atTop (𝓝 0):=by
    have hx':Tendsto (fun i=>g i • z) atTop (𝓝 0):= by simpa using ht.smul_const z
    exact (show Tendsto (gaugeCount (G:=G) («ι»:=Lo W)) (𝓝 0) (𝓝 0) from (by simpa using ((gaugeCount (G:=G)).continuous.tendsto (0:Z)))).comp hx' -- tune ▸
 have hp:Tendsto (fun i=> pay a (c i)) atTop (𝓝 B'):=by
    rw [show B'=∏ _i:F, a.scale*a.J 0 from by rw [hy.anchored,mul_one,prod_const,card_univ]]; refine tendsto_finsetProd _ (fun i _=>?_) -- reduction pay
    exact Tendsto.const_mul _ (((hy.germ 0 (mem_ball_self hy.patch)).continuousAt.tendsto).comp ((tendsto_pi_nhds.mp hh) i))
 let y' (i:ℕ):= pay a (c i)*Real.exp (Y' i-Q i)- B'
 have hv:Tendsto y' atTop (𝓝 0):=by simpa only [zero_add,Real.exp_zero,mul_one,sub_self,y',Function.comp_apply] using! ((hp.mul ((Real.continuous_exp.tendsto 0).comp hX)).sub_const B')
 have hl: Tendsto (fun i=>Real.exp (Q i)*y' i) atTop (𝓝 0):=by
    rw [tendsto_iff_norm_sub_tendsto_zero]; simp only [sub_zero,norm_mul]; apply squeeze_zero (fun i=>by positivity) (fun i=>mul_le_of_le_one_left (norm_nonneg (y' i)) (show ‖Real.exp (Q i)‖≤1 from (by rw [Real.norm_of_nonneg (Real.exp_pos _|>.le)]; exact Real.exp_le_one_iff.mpr (hq i)))) ?_
    simpa using hv.norm
 apply hl.congr'
 have hg: ∀ᶠ i in atTop,c i∈ chamber G W d:=by
    have ht : ∀ᶠ i:ℕ in atTop,∀ j:F,c i j∈ closedBall (0:G.Color) d:= eventually_all.mpr fun j=> ((tendsto_pi_nhds.mp hh) j).eventually (closedBall_mem_nhds _ u)
    exact ht.mono fun i t x _=>t x
 filter_upwards [he,hg] with i h w
 have hm: Y' i= -(η*x i)*boxE G (U i) D p (represent (g i • V))/2:=by unfold Y' y; rw [inv_pow,show (g i^2)⁻¹=x i from by_coupling h]; ring
 unfold hostP; rw [Set.indicator_of_mem (show _∈ _ from w)]; change Real.exp (Q i)*y' i= pay a (c i)*Real.exp (-(η*x i)*boxE G (U i) D p (layOut G (release (1:Y) (c i)))/2) - B'*Real.exp (Q i); rw [show layOut G (release _ (c i))= _ from tile_roll G (g i) z,←hm]; unfold y'; have ht:Real.exp (Q i)*Real.exp (Y' i-Q i)=Real.exp (Y' i):=by rw [←Real.exp_add,add_sub_cancel];
 rw [←ht]; ring
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.reign
