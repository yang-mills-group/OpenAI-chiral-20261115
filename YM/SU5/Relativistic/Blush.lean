import YM.SU5.Relativistic.Cater
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
open Pharos MinorPins
abbrev Ufee(p:Clip)(C:ℝ):=1+96*p.direct+6*C^2*96
omit hy in
lemma vogue(V:PathData G)(B:V.Bounds p σ C Λ) (η:ℝ)(v:0<η)(x:Z): dotProduct x ((η • DueQ G V D B W) *ᵥ x) ≤ η*Ufee p C*dotProduct x x:=by
 rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,show dotProduct x _= _ from ledgerQ G V D B x,mul_assoc]; apply mul_le_mul_of_nonneg_left _ v.le
 let b:=smear (crosses G W) *ᵥ x; let u:=laced G b; have ht:dotProduct b b=dotProduct x x:=grant_sq ..
 have hp:inCurl G u ≤96*dotProduct x x:= le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ (ort W)) (fun _ _ _=>sq_nonneg _)) ((hull_q G b).trans_eq (by rw [ht])) -- tune implicit
 have he: shortV G V D u≤6*C^2*96*dotProduct x x:=le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ (plumb W D)) (fun _ _ _=> sq_nonneg _)) ((combC G V D B b).trans_eq (by rw [ht]))
 change p.direct*inCurl G u+shortV G V D u≤_; unfold Ufee; linarith only [mul_le_mul_of_nonneg_left hp p.quadratic_pos.le,he,show 0≤dotProduct x x from (by rw [grit]; positivity)]
lemma fare_u (θ:ℝ)(q:0<θ)(w:Side)(σ C Λ:ℝ) : ∃ e:ℝ,0<e ∧ ∀ V:PathData G,∀ B:V.Bounds p σ C Λ, e ≤∫ i:Prices G (Lo w), plainH G w θ a (DueQ G V D B w) i:=by
 have hx:=p.quadratic_pos; let P:=(θ*Ufee p C) • (1: Matrix (Fresco G w) (Fresco G w) ℝ); have h:0<θ*Ufee p C:=by unfold Ufee; positivity
 let f:=fun i=> a.scale^Fintype.card (Lo w)*coldFee P i; obtain ⟨u,v⟩:= gram_p (show P.PosDef from Matrix.PosDef.one.smul h); have ht:0< ∫ i,f i:=by unfold f; rw [integral_const_mul,v]; exact mul_pos (pow_pos hy.scale _) (div_pos Gaussian.dome_pos (Real.sqrt_pos.mpr ((show P.PosDef from Matrix.PosDef.one.smul h).det_pos)))
 refine ⟨_,ht,fun V B=> ?_⟩; refine integral_mono (u.const_mul _) (scaleH G p a D hy 1 θ zero_lt_one q V B|>.1) ?_
 intro i; unfold f plainH; apply mul_le_mul_of_nonneg_left _ (pow_pos hy.scale _).le; apply Real.exp_le_exp.mpr; unfold P; rw [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]; exact div_le_div_of_nonneg_right (neg_le_neg (vogue G p D _ B θ q i)) zero_le_two -- tune
-- uniform for all x≫, t small condition; adapting β. Need bad branch cost for Bad lack G flags.
lemma purseH (W:Side)(σ C Λ θ:ℝ)(q:0<θ)(ε:ℝ)(e:0<ε):∃ R:ℝ,0<R∧∀ᶠ x:ℝ in atTop,∀(V:PathData G)(B:V.Bounds p σ C Λ), ∀ t∈ Set.Icc 0 R, (∫ z:Config G W,localPay G V D p t (θ*x) z ∂prior G W) ≤ (1+ε)*fee G W x a θ (DueQ G V D B W).det:=by
 -- binder notation X shadow W, avoid
 obtain ⟨d,v,c,ph,hl,pH,ht,hq,hV⟩:=kernel_ball a hy
 have he: ∃ R:ℝ,0<R∧((limit W:ℕ)*R)^2/2< v:=by
    have hx:Continuous (fun R:ℝ=>((limit W:ℕ)*R)^2/2):= by fun_prop
    have hv:= ((hx.continuousWithinAt (x:=0) (s:=Set.Ioi (0:ℝ))).tendsto.eventually (gt_mem_nhds (show ((limit W:ℕ)*(0:ℝ))^2/2 < v from by simpa using pH))); exact ((show ∀ᶠ i:ℝ in 𝓝[Set.Ioi (0:ℝ)] 0,0 < i from self_mem_nhdsWithin).and hv).exists
 obtain ⟨R,r,hR⟩:=he; refine ⟨R,r,?_⟩
 by_contra! z
 obtain ⟨P,g⟩:= host_dom (W:=W) G p a D hy θ d q (fun x h=>⟨(hq x h).1,(hq x h).2.1,(hq x h).2.2.1⟩)
 let I:=Fresco G W; let F':= Prices G (Lo W)
 have hu(n:ℕ): ∃ x:ℝ,(n+1:ℝ)≤ x ∧ ∃ (V:PathData G) (B: V.Bounds p σ C Λ),(1+ε)*(∫ i:F',plainH G W θ a (DueQ G V D B W) i)<∫ i:F',hostP G p a D d x V θ i:=by
    obtain ⟨x,t,v0⟩:= (z.and_eventually (eventually_ge_atTop ((n+1:ℝ)))).exists -- tune push_neg z
    obtain ⟨V,B,t,τ,h⟩:= t -- binder Icc
    have hx:0<x:=by linarith
    have he:= (show ((limit W:ℕ)*t)^2/2< v from lt_of_le_of_lt (by have ht:0≤t:=τ.1; gcongr; exact τ.2) hR)
    have hF:0<(Real.sqrt x)^ Fintype.card (Fresco G W):= by positivity
    refine ⟨x,v0,V,B,lt_of_lt_of_le ?_ (halo_transport G p a D hy d x ph hl hx V θ t v B τ.1 he hV q)⟩
    rw [(scaleH G p a D hy x θ hx q _ B).2,mul_left_comm]; exact mul_lt_mul_of_pos_left h hF
 choose x p' V B w using hu
 have hp:Tendsto x atTop atTop:= tendsto_atTop_mono (fun i=> (Nat.cast_le.mpr (le_refl i): (i:ℝ) ≤ i) |>.trans ((by linarith only [p' i]))) tendsto_natCast_atTop_atTop -- tune
 let Y' (i:ℕ):= plainH G W θ a (DueQ G (V i) D (B i) W)
 let Fg(i:ℕ)(x':F'):=hostP G p a D d (x i) (V i) θ x'; let k(i:ℕ)(u:F'):= max (Fg i u - Y' i u) 0
 have hm(i:ℕ):0<x i:=by linarith [p' i]
 have hj(i): Measurable (Fg i):=host_meas G p a D hy _ (B i)
 have hw(i:ℕ):Integrable (Fg i):=g.1.mono' (hj i|>.aestronglyMeasurable) (Eventually.of_forall (fun z=> by obtain ⟨u,v⟩:= (g.2 z).2 _ (hm i) _; change 0≤ Fg i z at u; rw [Real.norm_of_nonneg u]; exact v))
 have he(i:ℕ):Integrable (Y' i):=(scaleH G p a D hy _ θ (hm i) q _ (B i)).1
 have hM(i u): ‖k i u‖ ≤ P u:=by
    have hp:0 ≤ Y' i u:=by unfold Y' plainH coldFee; have hx:=hy.scale; positivity
    unfold k; rw [Real.norm_of_nonneg (le_max_right ..)]; exact max_le (((sub_le_self _ hp).trans ((g.2 u).2 (x i) (hm i) (V i)).2)) (g.2 u).1
 have hK(i): AEStronglyMeasurable (k i) volume:= ((hj i).aestronglyMeasurable.sub (he i).aestronglyMeasurable).sup aestronglyMeasurable_const
 have he' := tendsto_integral_filter_of_dominated_convergence (μ:=volume) («F»:=k) (f:=fun _=>0) P (Eventually.of_forall hK) (Eventually.of_forall fun i=> Eventually.of_forall (hM i)) g.1 (Eventually.of_forall (by
    intro i; change Tendsto (fun n=> max _ _) atTop (𝓝 0); simpa only [max_self] using (reign G p a D hy x hp V B q ph i).max (tendsto_const_nhds (x:=(0:ℝ))))) -- tune
 rw [integral_zero] at he'
 obtain ⟨L,hL,hl⟩:=fare_u G p a D hy θ q W σ C Λ
 obtain ⟨i,t⟩:= (he'.eventually (ge_mem_nhds (mul_pos e hL))).exists
 have hx: ∫ u,Fg i u≤ (∫ u,k i u)+ ∫ u,Y' i u:=by rw [←integral_add (g.1.mono' (hK _) (Eventually.of_forall (hM i))) (he i)]; apply integral_mono (hw i) ((g.1.mono' (hK _) (Eventually.of_forall (hM i))).add (he i)) (fun u=> (sub_le_iff_le_add.mp (le_max_left ..)))
 have hV:(1+ε)*(∫ u,Y' i u)<∫ u,Fg i u:=w i; change _≤ ε*L at t; linarith only [hx,hV,t,mul_le_mul_of_nonneg_left (show L≤ _ from hl _ (B i)) e.le] -- tune
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.purseH
