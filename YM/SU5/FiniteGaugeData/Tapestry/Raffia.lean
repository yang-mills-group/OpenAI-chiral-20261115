import YM.SU5.FiniteGaugeData.Tapestry.NimbusSpan
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry.Altitude
open Function Filter Finset NormedSpace ContinuousLinearMap Metric
open scoped Classical BigOperators ENNReal Topology
/-!
# Bills for all `grade`-local finitely many level operations. Avoid vague uniformity
claims: the norm here needs either representation prices or continuity space from
specific finitely many slots. We work with a handy product price referencing the
slots present. Provide bound on valuations and last-level functions & on error costs
with our two forms of estimate under the dual system, using bilinear recurrence.
Enables additional thinnings where requested (training words, growing supports, etc.).
-/
variable {V W Z E:Type*} [NormedAddCommGroup V][NormedAddCommGroup W][NormedSpace ℂ V][NormedSpace ℂ W]
  [NormedAddCommGroup Z][NormedSpace ℂ Z]
private lemma duBound (c:V→L[ℂ](W→L[ℂ]Z))(x:V)(y:W){D:ℝ}(v:‖x‖ ≤ D): ‖c x y‖ ≤ ‖c‖*D*‖y‖:= ((c x).le_opNorm y).trans (mul_le_mul_of_nonneg_right ((c.le_opNorm x).trans (mul_le_mul_of_nonneg_left v (norm_nonneg _))) (norm_nonneg _))
lemma toBound{p q:V→L[ℂ] W}{v u:V}{A B C:ℝ}(h:‖p-q‖≤ C)(x:‖v‖ ≤ A)(t:‖v-u‖ ≤ B): ‖p v-q u‖ ≤ C*A+‖q‖*B:=by
 calc
 _ = ‖(p-q) v+q (v-u)‖:=by simp only [map_sub,ContinuousLinearMap.sub_apply]; congr 1; abel
 _ ≤ _ := (norm_add_le ..).trans (add_le_add (((p-q).le_opNorm _).trans (mul_le_mul h x (norm_nonneg _) ((norm_nonneg _).trans h))) ((q.le_opNorm _).trans (mul_le_mul_of_nonneg_left t (norm_nonneg _))))
lemma opPriceBelow {p q:V→L[ℂ] W}{a b:ℝ}(h:‖p-q‖ ≤ a) (k:‖q‖ ≤ b): ‖p‖ ≤ a+b:=by rw [←sub_add_cancel p q]; exact (norm_add_le ..).trans (add_le_add h k)
lemma compPriceBefore (u:W→L[ℂ] Z)(F B:V→L[ℂ] W){A:ℝ}(h:‖F-B‖≤ A) : ‖u.comp F-u.comp B‖ ≤ A*‖u‖ := by
 rw [←ContinuousLinearMap.comp_sub]; exact (u.opNorm_comp_le _).trans (mul_comm A _ ▸ mul_le_mul_of_nonneg_left h (norm_nonneg _)) -- orientation

variable {X:ℕ→ Type*}[∀ i,NormedAddCommGroup (X i)][ιX:∀i,NormedSpace ℂ (X i)]
  {Y:ℕ→ Type*}[∀ i, NormedAddCommGroup (Y i)][∀ i,NormedSpace ℂ (Y i)]
section
omit ιX
def nectar : ∀ n:ℕ,(∀ i,X i) → ℝ
 | 0, x=> ‖x 0‖
 | n+1,x=> nectar n x*‖x (n+1)‖
lemma licensedN(n)(x:∀ i,X i): 0 ≤ nectar n x:=by induction n with| zero=> exact norm_nonneg (x 0)| succ n ih=> exact mul_nonneg ih (norm_nonneg _)
lemma nectar_eq (n:ℕ)(x:∀ i,X i): nectar n x= ∏ i∈ Finset.Iic n, ‖x i‖:=by induction n with| zero=> simp [nectar, show Iic (0:ℕ)={0} by ext; simp]| succ n ih=> rw [nectar,ih, show Iic (n+1)=insert (n+1) (Iic n) from (by ext; simp; omega), Finset.prod_insert (by simp), mul_comm]
lemma nectarBelow (n:ℕ)(x:∀ i,X i){f:ℕ→ℝ}(h:∀ i,i≤n→ ‖x i‖ ≤ f i): nectar n x≤ ∏ i∈ Finset.Iic n,f i:=by rw [nectar_eq]; exact Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i v=> h i (mem_Iic.mp v))
end

variable (u:X 0→L[ℂ] Y 0)(v:∀ i:ℕ, Y (i+1) →L[ℂ] (X (i+1) →L[ℂ] Y (i+1)))(F G:∀ i,Y i→L[ℂ] Y (i+1))(D:ℕ→ℝ)(φ:∀ i,0 ≤ D i)
section
def herring : ∀ n:ℕ, (∀ i,X i)→Y n | 0,x=> u (x 0) | n+1,x=> v n (F n (herring n x)) (x (n+1))
local notation "P" => herring u v F
local notation "Q" => herring u v G
-- `priceQ` supply bulk and discrepancy estimates. explicit recurrences sphere; n=0 initialization constant.
def priceQ : ℕ→ℝ | 0=>‖u‖ | n+1=> ‖v n‖ * D n * priceQ n
include φ
lemma positiveQ (n:ℕ):0 ≤ priceQ u v D n:=by induction n with|zero=> exact norm_nonneg _|succ n ih=> exact mul_nonneg (mul_nonneg (norm_nonneg (v n)) (φ n)) ih
omit φ
lemma herringSize(n:ℕ)(t:∀ m<n, ‖F m‖ ≤ D m)(x:∀i,X i) : ‖herring u v F n x‖ ≤ priceQ u v D n*nectar n x:=by
 induction n with
 | zero=>exact u.le_opNorm _
 | succ n ih=>
   rw [herring]; have hv:= t n (by omega); apply (duBound (v n) (F n (P n x)) _ ((F n|>.le_opNorm _).trans (mul_le_mul hv (ih fun i v=> t i (by omega)) (norm_nonneg _) ((norm_nonneg _).trans hv)))).trans_eq; rw [priceQ,nectar]; ring

variable {a:ℝ}(Ψ:ℕ→ ℝ)
-- use D for bounding norm of F,G; Ψ bounds norm of F_i-G_i.
def discrepancy : ℕ→ ℝ | 0=>0 | n+1=> ‖v n‖*(Ψ n * priceQ u v D n + ‖G n‖ * discrepancy n)
include φ
lemma feePos(n)(p:∀ m,0≤ Ψ m): 0≤ discrepancy u v G D Ψ n:=by induction n with| zero=> exact le_refl _| succ n ih=> exact mul_nonneg (norm_nonneg (v n)) (add_nonneg (mul_nonneg (p n) (positiveQ u v D φ n)) (mul_nonneg (norm_nonneg _) ih))
omit φ
lemma reckons (n:ℕ)(q:∀i<n,‖F i-G i‖ ≤ a*Ψ i)(t:∀i<n,‖F i‖≤ D i)(x:∀i,X i): ‖herring u v F n x-herring u v G n x‖ ≤ a* discrepancy u v G D Ψ n * nectar n x:=by
 induction n with
 | zero=> change ‖u (x 0)-u (x 0)‖≤ a*0*_; simp
 | succ n ih=>
   have p:= toBound (q n (by omega)) (herringSize u v F D n (fun i v=>t i (by omega)) x) (ih (fun i v=> q i (by omega)) (fun i v=> t i (by omega)))
   rw [discrepancy,nectar,herring,herring,←ContinuousLinearMap.sub_apply,←map_sub]
   apply (duBound (v n) _ _ p).trans_eq; ring

variable (n:ℕ)(E₀:ℝ){D':ℝ}(p₁: Y n→L[ℂ]ℂ)(p₂: Y n→L[ℂ]ℂ)
-- n binder insert before. terminal cost even n=0.
lemma finalHerring (p:‖p₁-p₂‖≤a*E₀)(q:∀i<n,‖F i-G i‖ ≤ a*Ψ i)(t:∀i<n,‖F i‖≤ D i)(x:∀i,X i): ‖p₁ (herring u v F n x)-p₂ (herring u v G n x)‖ ≤ a*( E₀* priceQ u v D n+‖p₂‖*discrepancy u v G D Ψ n)* nectar n x:=by apply (toBound p (herringSize u v F D n t x) (reckons u v F G D Ψ n q t x)).trans_eq; ring
end
-- norm convergence on all factor price. use at inner fixed i. prove with nit.
variable {ι:Type*}(n:ℕ)(F:ι→∀ i,Y i→L[ℂ]Y (i+1)){k: Filter ι} (p:∀ i,Tendsto (fun v=>F v i) k (𝓝 (G i)))
include p
lemma glimpse (i): ∀ ε:ℝ,0<ε→∀ᶠ j in k, ‖F j i-G i‖ ≤ ε:=fun ε e=> (Metric.tendsto_nhds.mp (p i) ε e).mono fun j h=> (by rw [←dist_eq_norm]; exact h.le)
lemma upstream (q:Y n→L[ℂ]ℂ) (t:ι→Y n→L[ℂ]ℂ) (U:Tendsto t k (𝓝 q)): ∀ ε:ℝ,0 <ε → ∀ᶠ i in k, ∀ x: (∀ i:ℕ, X i),
     ‖t i (herring u v (F i) n x)- q (herring u v G n x)‖ ≤ ε* nectar n x:=by
 intro ε e; let J i:=1+‖G i‖; let P':ℕ→ℝ:=fun _=>1; let z:= priceQ u v J n; let d:= discrepancy u v G J P' n; let A:= ‖q‖; let c:= z + A*d
 have hz:0≤z:=positiveQ u v _ (fun i=>add_nonneg zero_le_one (norm_nonneg _)) n
 have hd:0≤d:=feePos u v G _ (fun i=>add_nonneg zero_le_one (norm_nonneg _)) _ n (fun i=>zero_le_one) -- args order tune
 have h:0 ≤c:=add_nonneg hz (mul_nonneg (norm_nonneg q) hd)
 let e':= min 1 (ε/(c+1)); have h':0 < e':= lt_min zero_lt_one (by positivity); have hf : e'*(1*z + A*d)≤ ε:=by
    have he:= min_le_right 1 (ε/(c+1)); have h0: e'*(c+1)≤ ε:= (le_div_iff₀ (by positivity)).1 he
    rw [one_mul]; change e'*c≤ _; linarith
 filter_upwards [(eventually_all_finset (range n)).mpr fun i p' => glimpse G F p i e' h', Metric.tendsto_nhds.mp U e' h'] with i H u' x
 apply (finalHerring u v (F i) G J P' n 1 (t i) q (a:=e') (by rw [mul_one,←dist_eq_norm]; exact u'.le) ?_ ?_ x).trans (mul_le_mul_of_nonneg_right hf (licensedN ..));
 · intro j p; change _ ≤ e'*1; rw [mul_one]; exact H j (mem_range.mpr p)
 intro j p; exact opPriceBelow ((H j (mem_range.mpr p)).trans (min_le_left ..)) (le_refl _)

end YM.CF.Buffered.Afterglow.Tapestry.Altitude
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.finalHerring
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.upstream
