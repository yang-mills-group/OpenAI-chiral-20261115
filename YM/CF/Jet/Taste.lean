/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Analysis.Polydisc
import YM.CF.Drapes.Open
/-! Holomorphic jets with dimension-independent budgets; adapt the
coordinate-polydisc lemma YM.Analysis.Polydisc to separate quiver curves. -/
set_option autoImplicit false
noncomputable section
namespace YM.PolyDisc
open Filter Function Set Complex MeasureTheory Topology Metric
open scoped ContDiff BigOperators NNReal ENNReal
variable {α : Type} [Fintype α][DecidableEq α]{c : Plain α} {R : ℝ} {f : Plain α → ℂ}{i:α}
structure Taste (c: Plain α)(R:ℝ)(f:Plain α→ℂ):Prop where
  full : 0<R
  cont x : Accept c R x→ ContinuousAt f x
  diff x : Accept c R x→∀ i:α, DifferentiableAt ℂ (fun w=> f (update x i w)) (x i)
variable (h : Taste c R f)

include h

lemma Taste.remains (s : Finset α) {x : Plain α} (u : Takes c R x) (z : Screen α) : Accept c R (choose s c R x z) := by
  intro i; unfold choose; split
  · exact sphere_subset_closedBall (circleMap_mem_sphere (c i) h.full.le _)
  exact ball_subset_closedBall (u i)

def Taste.image (s : Finset α) {x} (u : Takes c R x) : Reel α := {
    toFun := fun p => f (choose s c R x p)
    continuous_toFun := continuous_iff_continuousAt.mpr fun p => (h.cont _ (h.remains s u p)).comp (choose_cont s x).continuousAt }

def Taste.series (s : Finset α) {x} (u : Takes c R x) : Reel α := (∏ i∈s, kernel i c R x) * h.image s u

lemma channel_t {x : Plain α} (u : Takes c R x) {s : Finset α} (hi : i ∉ s) : average i (h.series (insert i s) u) = h.series s u := by
  classical
  -- fixed background point, specialize Cauchy in ℂ
  ext1 p
  let z := choose s c R x p
  let F w := f (update z i w)
  have he : DifferentiableOn ℂ F (closedBall (c i) R) := by
    intro q hq
    have hy (w) := h.remains s u p w
    have hz : Accept c R (update z i q) := fun k => by by_cases H : k=i; simpa [H] using hq; simpa [H] using hy k
    apply DifferentiableAt.differentiableWithinAt
    have hm:= h.diff (update z i q) hz i
    simpa only [update_self,update_idem,F] using! hm
  have hz : update z i (x i)=z := by rw [show x i=z i by simp [z,choose,hi]]; exact update_eq_self _ _
  have hQ := he.circleIntegral_sub_inv_smul (u i)
  unfold circleIntegral at hQ
  rw [show F (x i)=f z by unfold F; rw [hz]] at hQ
  let d := ∏ j∈s,kernel j c R x p
  let K := 2*Real.pi*I
  have hk : K≠0 := by unfold K; simp [Real.pi_ne_zero]
  let g t := deriv (circleMap (c i) R) t • ((circleMap (c i) R t - x i)⁻¹ • F (circleMap (c i) R t))
  have ht : ∀ t : ℝ,t∈ uIcc 0 (2*Real.pi) → h.series (insert i s) u (update p i (clamps t))=d*K⁻¹*g t := by
    intro t ht
    rw [uIcc_of_le (by positivity)] at ht
    let b := update p i (clamps t)
    have h0 : ((b i):ℝ)=t := by simp [b,clamps,Set.projIcc_of_mem _ ht]
    have h1 j (hh : j ∈ s) : kernel j c R x b=kernel j c R x p := by
      have hp : j≠i := fun h => hi (h ▸ hh)
      simp only [value j u, speed,ContinuousMap.coe_mk,b,update_of_ne hp]
    change h.series _ _ b = _
    have h2 : choose (insert i s) c R x b=update z i (circleMap (c i) R t) := by
      ext1 j
      by_cases H : j=i
      · simp only [H,choose,Finset.mem_insert_self,↓reduceIte,update_self]; unfold ride; simp [h0]
      rw [update_of_ne H]; unfold z choose; simp only [Finset.mem_insert,H,false_or]
      split; swap; rfl
      simp [ride,b,H]
    rw [Taste.series, ContinuousMap.mul_apply, ContinuousMap.prod_apply]
    rw [Finset.prod_insert hi, show (∏ j ∈ s, _) = d from Finset.prod_congr rfl fun j hj => h1 j hj]
    rw [Taste.image]; simp only [ContinuousMap.coe_mk]; rw [h2,value i u]
    simp only [speed,g,K,F,ContinuousMap.coe_mk,h0,smul_eq_mul]; ring
  have hr : h.series s u p = d*f z := by rw [Taste.series,ContinuousMap.mul_apply,ContinuousMap.prod_apply]; rfl
  rw [average_act,hr]
  rw [intervalIntegral.integral_congr ht,intervalIntegral.integral_const_mul]
  change (∫ t in (0:ℝ)..2*Real.pi,g t) = K • f z at hQ
  rw [hQ,smul_eq_mul, mul_assoc, inv_mul_cancel_left₀ hk]

lemma Taste.invertor (s : Finset α) : ∃ v : Reel α →L[ℂ] ℂ, ∀ x (u : Takes c R x), v (h.series s u)= f x := by
  induction s using Finset.induction_on with
  | empty =>
    let p : Screen α := fun i => clamps 0
    refine ⟨ContinuousMap.evalCLM ℂ p, fun x u => ?_⟩
    unfold Taste.series
    rw [Finset.prod_empty,one_mul]
    change f (choose ∅ c R x p)=_; rw [show choose ∅ _ _ _ p=x from funext fun i => by simp [choose]]
  | @insert i s hi IH =>
    obtain ⟨v,hv⟩ := IH
    refine ⟨v ∘L average i,fun x u => ?_⟩
    rw [ContinuousLinearMap.comp_apply,channel_t h u hi,hv]

lemma Taste.hol : AnalyticAt ℂ f c := by
  obtain ⟨v,hv⟩ := h.invertor Finset.univ
  have he : Takes c R c := mem_of_mem_nhds (Takes.at h.full)
  let F (z : Plain α) := (∏ i,kernel i c R z) * h.image Finset.univ he
  have hh : AnalyticAt ℂ F c := (show AnalyticAt ℂ (fun x : Plain α => ∏ i,kernel i c R x) c from
    (by apply Finset.analyticAt_fun_prod; intro i _; exact forms i h.full)).mul analyticAt_const
  refine ((v.analyticAt _).comp hh).congr ?_
  filter_upwards [Takes.at h.full] with x hx
  change v (F x)=f x
  rw [← hv x hx]; apply congr_arg v
  unfold F Taste.series
  congr 1; ext i; simp [Taste.image]; congr 1; funext j; simp [choose]
end YM.PolyDisc
