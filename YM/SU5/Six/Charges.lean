import YM.SU5.Six.BankScore
import Mathlib.MeasureTheory.Integral.Prod
import YM.SU5.Cordial.Balloon
import YM.SU5.Cheer.Chapel
set_option autoImplicit false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.Score
open OS OS.Semigroup OS.Semigroup.Balloon Boundary Boundary.Probe Spectral
open Function Filter Set Metric MeasureTheory InnerProductSpace
open scoped Topology InnerProductSpace BigOperators Classical NNReal ENNReal ComplexOrder
open TopologicalSpace
open scoped ComplexConjugate
variable (X:Hilbert)
private abbrev Landscape:= Axis→ℝ
private lemma integralSpan (f:Landscape→ X)(h:Integrable f) :
    inner ℂ (∫ x,f x) (∫ x,f x)= ∫ x,∫ y, inner ℂ (f x) (f y):= by
 simp_rw [integral_inner h]; let x:=∫ x,f x; have hv(v:X): inner ℂ v x=starRingEnd ℂ (inner ℂ x v):=(inner_conj_symm ..).symm
 change inner ℂ (∫ x,f x) x=∫ y,inner ℂ (f y) x; nth_rw 1 [hv]; rw [← integral_inner h]; rw [← integral_conj (𝕜:=ℂ)]; exact integral_congr_ae (Eventually.of_forall fun i=>(hv _).symm)
section basic
variable (S:OS.Semigroup X (3:Axis))
local notation "μ"=> S.ℚmeasure.diagonal
local notation "Γ"=> S.ℚmeasure.region
private lemma UActs (U:Landscape→Clock)(h:Continuous U) (F:Landscape→X)(p:Continuous F): Continuous (fun i=> S.U (U i) (F i)):= by
 refine continuous_iff_continuousAt.mpr fun i=> Metric.tendsto_nhds.mpr fun ε e=>?_
 filter_upwards [Metric.tendsto_nhds.mp (p.tendsto i) (ε/2) (by positivity), Metric.tendsto_nhds.mp (((S.continuousU (F i)).comp h).tendsto i) (ε/2) (by positivity)] with j v g
 have he: dist (S.U (U j) (F j)) (S.U (U j) (F i))=dist (F j) (F i):= by rw [dist_eq_norm,← map_sub,S.unitary,dist_eq_norm]
 exact (dist_triangle _ (S.U (U j) (F i)) (S.U (U i) (F i))).trans_lt ((add_lt_add (he.trans_lt v) g).trans_eq (add_halves ε))
variable (f:(Axis→ℝ)→ℝ)(e:Continuous f)(c:HasCompactSupport f)
    (v:(Axis→ℝ)→ Clock)(a:Continuous v)(t:(Axis→ℝ)→ ℝ≥0)(h:Continuous t)
    (b:ℝ≥0) (x:X)
def spark (y: Landscape): X:= (f y:ℂ) • S.U (v y) (S.E (t y) (x-S.E b x))
def gain (y:Landscape)(p:E4):ℂ:= ↑(f y)*vote (v y) (t y) b p
local notation "K"=> gain f v t b
local notation "V"=> spark X S f v t b x
lemma spark_cost (p q:Landscape): inner ℂ (V p) (V q)=∫ z, starRingEnd ℂ (K p z) * K q z ∂μ x:= by
 unfold spark gain; rw [inner_smul_left,inner_smul_right,mix,← integral_const_mul, ← integral_const_mul]; apply integral_congr_ae; apply Eventually.of_forall; intro z; dsimp only; rw [map_mul]; ring
include e a h
@[fun_prop] lemma gain_cont : Continuous (Function.uncurry K):= by unfold gain vote lens plane tinct Function.uncurry; fun_prop
include c
lemma spark_ready : Integrable V :=by
 let g(y):=S.E (t y) (x-S.E b x)
 have H':Continuous g:= (S.continuousE _).comp h
 have hx: Continuous V:= (Complex.continuous_ofReal.comp e).smul (UActs X S v a g H')
 have hy:HasCompactSupport (fun x:Axis → ℝ=>(f x:ℂ)):= c.mono (fun i n h=> n ((congrArg Complex.ofReal h).trans Complex.ofReal_zero)) -- ofReal function?
 have hp:HasCompactSupport V:= hy.mono (fun i n h=> n ((congrArg (· • (S.U (v i) (g i))) (show (f i:ℂ)=0 from h)).trans (zero_smul ℂ _)))
 exact hx.integrable_of_hasCompactSupport hp
omit e c a h
section region
variable {R:Set E4}(p:MeasurableSet R)
include p
lemma spark_split (y:Landscape): Γ R (V y)= spark X S f v t b (Γ R x) y:= by
 unfold spark; rw [map_smul,inside_lens X S p,map_sub,coolLens X S p]
include e c a h
lemma consult : Γ R (∫ y,V y) = ∫ y:Landscape, spark X S f v t b (Γ R x) y:= by
 let Z:= (Γ R).restrictScalars ℝ
 have H': Γ R (∫ y,V y)=∫ y, Z (V y):= (Z.integral_comp_comm (spark_ready X S f e c v a t h b x)).symm
 exact H'.trans (integral_congr_ae (Eventually.of_forall fun y=> spark_split X S f v t b x p y))
end region
-- no faithfulness of *all* frequencies. Just consume local diagonal measures here
include e c a h
lemma consigned :
    Integrable (fun p=> ‖∫ y:Landscape,gain f v t b y p‖^2) (μ x) ∧
    ‖∫ y:Landscape,spark X S f v t b x y‖^2= ∫ p, ‖∫ y:Landscape,gain f v t b y p‖^2 ∂μ x := by
 let R:=volume (α:= Landscape) -- syntax
 let T:= R.prod R; let U: (Landscape × Landscape)→E4→ℂ:= fun y z=>starRingEnd ℂ (K y.1 z) * K y.2 z
 let F(p:E4):= ∫ y,K y p ∂ R
 let g(y:Landscape):ℝ:= ‖f y‖ * 2
 have hp:Integrable g R:= (e.integrable_of_hasCompactSupport («μ»:=R) c).norm.mul_const 2
 have hG(y:Landscape)(p:E4)(z:0≤time p): ‖K y p‖ ≤g y:= by unfold gain g; rw [norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (vote_norm _ _ _ p z) (norm_nonneg _)
 have H:Integrable U.uncurry (T.prod (μ x)):= by
    have hv:=hp.mul_prod hp|>.comp_fst (μ x)
    have he:=gain_cont f e v a t h b
    let Y(A:Landscape × Landscape × E4):= Function.uncurry K (A.1,A.2.2) -- type unused
    have hc: Continuous U.uncurry:=by
       unfold Function.uncurry U; exact (he.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).star.mul (he.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    refine hv.mono' hc.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.Measure.quasiMeasurePreserving_snd.ae (S.bright x)] with p u
    unfold Function.uncurry U; rw [norm_mul, Complex.norm_conj]; exact mul_le_mul (hG _ _ u) (hG _ _ u) (norm_nonneg _) (by unfold g; positivity)
 let W:= ∫ y,V y; have hX : inner ℂ W W= ∫ p, (↑(‖F p‖^2):ℂ) ∂μ x:= by
   -- outer inner product by iterated integral. then trade order for frequency-first
   rw [show inner ℂ W W=_ from integralSpan X V (spark_ready X S f e c v a t h b x)]
   simp_rw [spark_cost]
   rw [← integral_prod (fun i:Landscape × Landscape=> ∫ p,U i p∂μ x) H.integral_prod_left]
   rw [integral_integral_swap H]; apply integral_congr_ae
   filter_upwards [H.swap.prod_right_ae] with p u
   have hp: Integrable (fun y:Landscape × Landscape=> U y p) T:= u
   rw [integral_prod _ hp]; unfold U; simp_rw [integral_const_mul]; rw [integral_mul_const,integral_conj (𝕜:=ℂ)]
   exact Complex.normSq_eq_conj_mul_self.symm.trans (congrArg ((↑):ℝ→ℂ) (Complex.normSq_eq_norm_sq _))
 have hF:Integrable (fun p=> ‖F p‖^2) (μ x):= by
   refine (H.swap.integral_prod_left.re).congr ?_ -- avoid repeat? extract lemma local.
   filter_upwards [H.swap.prod_right_ae] with p u
   have hp : (∫ y:Landscape×Landscape,U y p ∂ T)=↑(‖F p‖^2):= by
     have ht: Integrable (fun y:Landscape × Landscape=> U y p) T:= u
     rw [integral_prod _ ht]; unfold U; simp_rw [integral_const_mul]; rw [integral_mul_const,integral_conj (𝕜:=ℂ)]
     exact Complex.normSq_eq_conj_mul_self.symm.trans (congrArg ((↑):ℝ→ℂ) (Complex.normSq_eq_norm_sq _))
   exact congrArg Complex.re hp
 refine ⟨hF,Complex.ofReal_injective ?_⟩
 have he: inner ℂ W W=((‖W‖^2:ℝ):ℂ):= by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
 rw [he, integral_complex_ofReal] at hX; exact hX
omit e c a h
end basic
end YM.Score
