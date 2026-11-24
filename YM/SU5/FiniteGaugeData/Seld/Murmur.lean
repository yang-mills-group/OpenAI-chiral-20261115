import YM.SU5.FiniteGaugeData.Seld.Jitney
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
open Spectral Boundary Probe
local notation "V"=> S.unit
local notation "U"=> M S
variable (A B: H.Op)(p:E4)(g h: Test4)(c:ℂ)
local notation "Vh"=> optx S
local notation "P" f:max x:max=> fun p:E4=> f p • Vh A p x
lemma spice(p:E4) : ‖g p • Vh A p x‖ ≤ ‖g p‖*(‖A‖*‖x‖):= (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (vcost ..) (norm_nonneg _))
lemma emberI : Integrable (P g x):= (g.integrable.norm.mul_const (‖A‖*‖x‖)).mono' (g.continuous.smul (village S x A)).aestronglyMeasurable (Eventually.of_forall (fun p=> spice S x A g p))
-- invoice
abbrev vial : ℝ:= ‖SchwartzMap.toLpCLM ℂ ℂ 1 volume g‖
lemma vmeets : vial g= ∫ p, ‖g p‖:=SchwartzMap.norm_toLp_one
lemma vialC : Continuous vial := continuous_norm.comp ((SchwartzMap.toLpCLM ℂ ℂ 1 (volume (α:=E4))).continuous)
lemma voyage : ‖∫ p,g p • Vh A p x‖ ≤ (vial g*‖A‖)*‖x‖ := by
 rw [mul_assoc,vmeets,←integral_mul_const]; exact norm_integral_le_of_norm_le (g.integrable.norm.mul_const _) (Eventually.of_forall fun p=>spice S x A g p)
def valise : H.Op:= LinearMap.mkContinuous (σ:= RingHom.id ℂ) {
 toFun v:=∫ p,g p • Vh A p v
 map_add' a b:=by simp only [map_add,smul_add]; rw [integral_add (emberI ..) (emberI ..)]
 map_smul' b v:= by simp_rw [map_smul,smul_comm _ b]; rw [integral_smul]; rfl } (vial g*‖A‖) (fun a=> voyage S a A g)
lemma vmap : valise S A g x= ∫ p,g p • Vh A p x:=rfl
lemma vnorm : ‖valise S A g‖≤ vial g*‖A‖:= ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun v=>voyage S v A g
lemma vadd : valise S (A+B) g= valise S A g+valise S B g:=by
 ext1 x; change _=valise S A g x+ valise S B g x; simp_rw [vmap,versA,_root_.add_apply,smul_add]; exact integral_add (emberI ..) (emberI ..)
lemma vscale : valise S (c • A) g= c • valise S A g:=by
 ext1 x; change _=c • valise S A g x; simp_rw [vmap,versL,_root_.smul_apply,smul_comm _ c,integral_smul]
def barren : Test4→ₗ[ℂ] H.Op where
 toFun:= valise S A
 map_add' g h:= by ext1 v; simp_rw [_root_.add_apply,vmap,_root_.add_apply,add_smul]; exact integral_add (emberI ..) (emberI ..)
 map_smul' c v:=by ext1 x; change _=c • valise S A v x; simp_rw [vmap,_root_.smul_apply,smul_eq_mul,mul_smul,integral_smul]
lemma ebb : Continuous (barren S A):= by
 apply continuous_of_continuousAt_zero (barren S A); apply Metric.tendsto_nhds.mpr; intro ε he; let f:=fun g:Test4 => vial g*‖A‖; rw [← show f 0=0 from by dsimp only [f]; rw [vial,map_zero,norm_zero,zero_mul]] at he; filter_upwards [((vialC.mul continuous_const)|> (show Continuous f from ·) |>.tendsto 0).eventually (gt_mem_nhds he)] with y p; rw [map_zero,dist_zero_right]; exact lt_of_le_of_lt (vnorm S A y) p
-- f ← ξ(Big F) limits independently
lemma scenery : valise S (star A) (bar g)=star (valise S A g):=by
 ext1 x; apply ext_inner_left ℂ; intro y; change _=inner ℂ y ((valise S A g).adjoint x); rw [ContinuousLinearMap.adjoint_inner_right,vmap,vmap, ← integral_inner (emberI ..),←inner_conj_symm (∫ _, _) x] -- orientation
 rw [← integral_inner (emberI ..),← integral_conj]; congr 1 with t; rw [inner_conj_symm,bar_at,← versX,inner_smul_right,inner_smul_left]; exact congrArg ((star (g t))* ·) (ContinuousLinearMap.adjoint_inner_right (Vh A t) y x) -- check inner star and binders
#print axioms ebb
def apron : Test4 →L[ℂ] H.Op:= ⟨barren S A, ebb S A⟩
@[simp] lemma apron_ap(f:Test4): apron S A f=valise S A f:=rfl
lemma overlap (h:∀ p, Commute (U p) B): valise S (B*A) g=B*valise S A g:= by
 ext1 x; change _=B (valise S A g x); rw [vmap,vmap,←B.integral_comp_comm (emberI S x A g)]; congr 1 with t; rw [versP S t A B (h t),map_smul]; rfl -- order
lemma overlap_R (h:∀ p, Commute (U p) B): valise S (A*B) g=valise S A g*B:= by
 ext1 x; change _=valise S A g (B x); rw [vmap, vmap]; congr 1 with t; rw [versQ S t A B (h _)]; rfl
lemma precursor : optx S (valise S A g) p = valise S A (ahead p g):= by
 ext1 x; change U p (valise S A g (U (-p) x))=_; rw [vmap,vmap,← (U p).integral_comp_comm (emberI S (U (-p) x) A g),← integral_add_left_eq_self (fun b=> ahead p g b • optx S A b x) p]; congr 1 with t; rw [ahead_at,add_sub_cancel_left,← opt_act S p t A, map_smul]; rfl
#print axioms precursor
#print axioms scenery
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
