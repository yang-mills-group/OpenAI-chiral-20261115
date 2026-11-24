import YM.SU5.Reconstruction.Quartz.Rake
import YM.SU5.Reconstruction.Crease.Fountain
import YM.SU5.Reconstruction.Crease.Keeper
import Mathlib.Analysis.Complex.LocallyUniformLimit
set_option autoImplicit false
noncomputable section
namespace YM.Quartz
open Function Set Filter MeasureTheory Spectral Analysis Metric Topology
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace Classical
open Multiplier CrossedFrame Clasp Complex HadamardThreeLines BridgeClub Anvil
variable {K H D:Hilbert}(C:Clasp K H D)
local notation "S"=> spectrum ℂ C.angle
local notation "Q" n:max=> glacier C n
local notation "R" n:max=> Quartz.rise C n
local notation "L" i:max=> C.Left.symm.conjStarAlgEquiv i
local notation "B" i:max=> C.Right.symm.conjStarAlgEquiv i
variable (X:H.Op)(Y:D.Op)
local notation "T" n:max=>twinkle C n (L X)
local notation "ℬ"=> verticalClosedStrip 0 1
local notation "L₀"=> verticalStrip 0 1
local notation "U"=> (Ultrafilter.of (atTop:Filter ℕ))
local notation "M"=> max ‖X‖ ‖Y‖
lemma validM : 0≤ max ‖X‖ ‖Y‖:= (norm_nonneg _).trans (le_max_left ..)
variable (h:C.Pass X Y)
lemma incite (z:ℂ)(v:z∈ℬ) (h: C.Pass X Y) : ∃ u:K.Op, ‖u‖≤ max ‖X‖ ‖Y‖ ∧ Limited (U:Filter ℕ) (fun n=> (T n) z) u := Limit_World U (validM X Y) (fun n=> max_blink C n X Y h _ ((lift_budget _ X).trans (le_max_left ..)) ((lift_budget _ Y).trans (le_max_right ..)) z v)
noncomputable def tirs (z:ℂ):K.Op:= if v:z∈verticalClosedStrip 0 1 then (incite C X Y z v h).choose else 0
local notation "Xy"=>tirs C X Y h
lemma ties (z:ℂ)(v:z∈ℬ): ‖Xy z‖≤M ∧ Limited (U:Filter ℕ) (fun n=>(T n) z) (tirs C X Y h z) := by rw [tirs,dif_pos v]; exact (incite C X Y z v h).choose_spec
lemma death (z:ℂ)(t:z∈ℬ)(n:ℕ): (Q n)*(Xy z) * Q n= (T n) z:= by
 ext1 x; apply ext_inner_left ℂ; intro y
 let w:= (ties C X Y h z t).2
 have hz:= ((w.toLeft (Pearl.still _ (Q n))).toRight (Pearl.still _ (Q n))).confirms y x -- ordering?
 refine tendsto_nhds_unique hz (tendsto_const_nhds.congr' ?_); apply (show ∀ᶠ p:ℕ in (U:Filter ℕ), n≤p from Ultrafilter.of_le atTop (eventually_ge_atTop n)).mono
 intro p hp; apply congrArg (fun B':K.Op=>inner ℂ y (B' x)); -- use add
 rw[←narrower C n (L X) p hp z]
lemma speed (x y: K)(q:K.Op) (v:‖q‖≤ M)(n:ℕ):
 dist (inner ℂ x (q y)) (inner ℂ x ((Q n*q*Q n) y)) ≤ ‖x-(Q n) x‖*(M*‖y‖)+‖(Q n) x‖*(M*‖y-(Q n) y‖) := by
 let δ:= Q n
 have ht(p r:K): ‖inner ℂ p (q r)‖≤ ‖p‖*(M*‖r‖):=(norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left ((q.le_opNorm r).trans (mul_le_mul_of_nonneg_right v (norm_nonneg _))) (norm_nonneg _))
 rw [dist_eq_norm]; change ‖inner ℂ x (q y)-inner ℂ x (δ (q (δ y)))‖ ≤ _; rw [← Clasp.through_self _ (glaze_self C n),show inner ℂ x (q y)-inner ℂ (δ x) (q (δ y))= inner ℂ (x-δ x) (q y)+inner ℂ (δ x) (q (y-δ y)) from by rw [map_sub,inner_sub_left,inner_sub_right]; abel]; exact (norm_add_le ..).trans (add_le_add (ht _ _) (ht _ _))
lemma sparkle (x y:K) : TendstoUniformlyOn (fun n (z:ℂ)=>inner ℂ x ((T n) z y)) (fun z=> inner ℂ x (Xy z y)) atTop ℬ := by
 apply Metric.tendstoUniformlyOn_iff.mpr; intro ε u; let f(n:ℕ):=‖x-(Q n) x‖*(M*‖y‖)+‖(Q n) x‖*(M*‖y-(Q n) y‖)
 have hf:Tendsto f atTop (𝓝 0):= by simpa [f] using! ((((tendsto_const_nhds (x:=x)).sub (glaze_shrinks C x)).norm.mul_const (M*‖y‖)).add ((glaze_shrinks C x|>.norm).mul (((tendsto_const_nhds (x:=y)).sub (glaze_shrinks C y)).norm.const_mul M)))
 apply (hf.eventually (gt_mem_nhds u)).mono; intro i p z t
 refine lt_of_le_of_lt ?_ (show f i < ε from p); unfold f; rw [← death C X Y h z t i]; exact speed _ _ _ x y (Xy z) (ties C X Y h z t).1 i
lemma apex (x y:K):ContinuousOn (fun z=> inner ℂ x (Xy z y)) ℬ ∧ DifferentiableOn ℂ (fun z=> inner ℂ x (Xy z y)) L₀:=by
 let r(n)(z:ℂ):= inner ℂ x ((T n) z y); have hr(n):Differentiable ℂ (r n):=fun z=> ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ K y)).differentiableAt.comp z (Quartz.confined ..)
 let k':= sparkle C X Y h x y; have hp:verticalStrip 0 1⊆ℬ:=preimage_mono Ioo_subset_Icc_self;
 exact ⟨k'.continuousOn (Frequently.of_forall (fun n=>(hr n).continuous.continuousOn)), (k'.mono hp).tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall (fun n=> (hr n).differentiableOn)) (isOpen_Ioo.preimage continuous_re) ⟩ -- names
lemma wise (z:ℂ)(v:z∈ℬ)(u:K.Op)(p:∀n,(T n) z=(Q n*u* Q n)) : Xy z=u:=by
 ext1 x; apply ext_inner_left ℂ; intro y; let h':=(ties C X Y h z v).2.confirms y x
 refine tendsto_nhds_unique h' (Tendsto.mono_left ?_ (Ultrafilter.of_le atTop))
 simp_rw [p];
 have hp(q:K.Op)(n:ℕ) : inner ℂ y ((Q n*q*Q n) x)=inner ℂ ((Q n) y) (q ((Q n) x)):= (Clasp.through_self (Q n) (glaze_self C n) y _).symm
 simp_rw[hp]
 exact (glaze_shrinks C y).inner ((u.continuous.continuousAt.tendsto).comp (glaze_shrinks C x))
end YM.Quartz
