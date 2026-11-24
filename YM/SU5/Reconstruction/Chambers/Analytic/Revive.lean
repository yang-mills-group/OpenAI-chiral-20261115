import YM.SU5.Reconstruction.Chambers.Analytic.Frame
import Mathlib.Analysis.Normed.Group.FunctionSeries
/-!
# Jointly analytic from real separate budgets
-/
set_option autoImplicit false
noncomputable section
namespace YM.PolyDisc.Revival
open Function Filter Topology Complex Set Metric
open scoped BigOperators NNReal ENNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "M" => (ι→ℂ)
local notation "F" => (M→ℂ)

variable (s : List ι) (ρ : ∀ i:ι,i∈s)
variable {c : ι→ℝ} {d r K : ℝ} {f : (ι→ℝ)→ℂ}
local notation "U" n:max=> stage c d n s (bold f)
local notation "V"=> 64^(s.length)
private def spread (b : ℕ) : ℝ := 64^b
private def ratio (d r : ℝ) (b : ℕ) : ℝ := d/r * 64^(b+1)
private def budget (r K d : ℝ) (b:ℕ) : ℝ := (1-d/r)⁻¹*K*b*2
local notation "H₁"=> budget r K d s.length
local notation "U'"=> ratio d r s.length

variable (g : 0<d) (u : d<r) (h : Permit c r K f)
omit [Fintype ι] [DecidableEq ι] in
private lemma pos_r (g : 0<d)(p : 0<r): 0 < ratio d r s.length := by unfold ratio; positivity
private lemma pow_tower(n m : ℕ) : ((64:ℝ)^n)^m=((64:ℝ)^m)^n := by rw [←pow_mul,mul_comm n, pow_mul]

include g u h
omit [Fintype ι] in
private lemma pos_b : 0 ≤ budget r K d s.length := by
  have p := h.base; unfold budget; have ht:0<1-d/r:=sub_pos.mpr ((div_lt_one (g.trans u)).2 u); positivity
omit [Fintype ι] in
lemma contract (n : ℕ) (x : ι→ℂ) (p : patch c d [] x) :
    ‖stage c d n s (bold f) x - bold f x‖ ≤
      ((ratio d r s.length)^(n+1)) * budget r K d s.length := by
  have hb : 0≤ (1-d/r)⁻¹ := by refine inv_nonneg.mpr (sub_nonneg.mpr ((div_lt_one h.radius_pos).2 u).le)
  apply (price_real g u h s x p).trans -- maybe order
  have p:= pos_r (d:=d) s g h.radius_pos; unfold ratio budget; have hk:=h.base
  set v:= (64:ℝ)^(n+1)
  have hu:1 + v≤ v*2:=by unfold v; linarith [show 1≤ (64:ℝ)^(n+1) from one_le_pow₀ (by norm_num)]
  calc
    _ ≤ (d/r)^(n+1)*(1-d/r)⁻¹*K*(v*2)*s.length*v^s.length := by have ht:=h.radius_pos; gcongr
    _ = _ := by unfold v; rw [pow_tower (n+1) s.length,pow_succ (64:ℝ) s.length,mul_pow,mul_pow]; ring

omit g u h
variable (v : ratio d r s.length * spread s.length < 1)
include g u h v
private lemma cond : ratio d r s.length < 1 := lt_of_le_of_lt (le_mul_of_one_le_right (pos_r s g h.radius_pos).le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 64))) v

theorem on_real (x : ι→ℝ) (p : asC x∈ packet c d) : Tendsto (fun n : ℕ=> stage c d n s (bold f) (asC x)) atTop (𝓝 (f x)) := by
  have ht:Tendsto (fun n:ℕ=> (ratio d r s.length)^(n+1)*budget r K d s.length) atTop (𝓝 0):= by
    simpa [pow_succ] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (pos_r s g h.radius_pos).le (cond s g u h v)).mul_const (U')).mul_const H₁)
  apply Metric.tendsto_nhds.mpr; intro ε a
  filter_upwards [ht.eventually (gt_mem_nhds a)] with i t
  apply lt_of_le_of_lt _ t; rw [dist_eq_norm]
  have hh : bold f (asC x)=f x := by unfold bold; rw [Function.comp_apply,c_to_r]
  rw [←hh]; exact contract s g u h i (asC x) ((patch_iff ..).2 ⟨p,by rw [c_to_r]⟩)

private def sphereC (d r K:ℝ)(b n:ℕ) := (ratio d r b * spread b)^(n+1) * (2*spread b* budget r K d b)

include ρ
private lemma next_price (n : ℕ) (x : M) (w : x∈ packet c d) :
    ‖((U (n+1)) x)- (U n) x‖ ≤ sphereC d r K s.length n := by
  let l : M→ℂ := U (n+1) - U n
  let A := (64:ℝ)^(n+1+1)
  let c' (n:ℕ):= (ratio d r s.length)^(n+1)
  let f' (n:ℕ):= c' n * H₁
  have he(z:M)(a : patch c d [] z): ‖l z‖≤2*f' n:= (norm_sub_le_norm_sub_add_norm_sub _ (bold f z) _).trans (by
    rw [norm_sub_rev (bold f z)]; refine (add_le_add (contract s g u h (n+1) z a) (contract s g u h n z a)).trans ((add_le_add (b:=f' n) ?_ le_rfl).trans (le_of_eq (two_mul (f' n)).symm)) -- specify order?
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (pos_r s g h.radius_pos).le (cond s g u h v).le (Nat.le_succ (n+1))) (pos_b s g u h) )
  have hh : ‖l x‖≤ A^s.length*(2*f' n):= by
    apply lifted_bound c d (2*f' n) l (n+1) ?_ g s _ he x ⟨w,fun i p=> (p (ρ i)).elim⟩
    · unfold f' c'; have ha:=pos_b s g u h; have hz:= pos_r s g h.radius_pos; positivity
    intro i _; unfold l; rw [map_sub, captures c d (bold f) (n+1) (n+1) i s (ρ i) le_rfl g, captures c d (bold f) n (n+1) i s (ρ i) (by omega) g] -- tune
  refine hh.trans (le_of_eq ?_); unfold A f' c' sphereC spread; rw [pow_tower (n+1+1), pow_succ _ (n+1), mul_pow]; ring

theorem uniform : ∃ g : (ι→ℂ)→ℂ, TendstoUniformlyOn (fun (n:ℕ) => stage c d n s (bold f)) g atTop (packet c d) := by
  let l(i:ℕ):= U (i+1)-U i
  have ha : TendstoUniformlyOn (fun n:ℕ=> U n-U 0) (fun x=>∑' i:ℕ, l i x) atTop (packet c d) := by
    have p(i : ℕ)(x:M) (h' : x∈ packet c d):= next_price s ρ g u h v i x h'
    have hx : Summable (fun n:ℕ=> sphereC d r K s.length n):= by
       unfold sphereC; have hz:= pos_r s g h.radius_pos; have hx: 0< spread s.length:=by unfold spread; positivity
       simp_rw [pow_succ]; exact ((summable_geometric_of_lt_one (mul_pos hz hx).le v).mul_right _).mul_right _
    have e := tendstoUniformlyOn_tsum_nat (f:=fun n x=> l n x) hx p
    convert e using 1; ext n x; dsimp only [l,Pi.sub_apply]; rw [Finset.sum_range_sub (fun i=> (U i) x)] -- tune
  refine ⟨fun x=> (∑' i:ℕ, l i x)+ (U 0) x,?_⟩
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ha ε hε] with n b x t
  specialize b x t; rw [dist_eq_norm] at b ⊢; rw [Pi.sub_apply, sub_sub_eq_add_sub] at b; exact b

omit g u h v ρ

-- Universal collar evaluation, no convergence-of-multi-derivatives assumptions. Pay
-- boundary convergence of the analytic approximants directly. Same choice of linear
-- read for every *approximant*, old result `PolyDisc.Eats.hol` extended to this sequence.
variable {C : Plain ι}
private lemma cauchyC (s: Finset ι) (C:Plain ι)(d:ℝ) :
    ∃ v : Reel ι→L[ℂ] ℂ, ∀ (f: (ι→ℂ)→ℂ) (e : Eats C d f) (x:Plain ι) (u : Takes C d x), v (e.series s u)= f x := by
  induction s using Finset.induction_on with
  | empty =>
    let p : Screen ι := fun i => clamps 0
    refine ⟨ContinuousMap.evalCLM ℂ p, fun f e x u => ?_⟩
    unfold Eats.series
    rw [Finset.prod_empty,one_mul]
    change f (PolyDisc.choose ∅ C d x p)=_; rw [show PolyDisc.choose ∅ C d x p=x from funext fun i => by simp [PolyDisc.choose]]
  | @insert i s hi IH =>
    obtain ⟨v,hv⟩ := IH
    refine ⟨v.comp (average i),fun f h x u=> ?_⟩
    rw [ContinuousLinearMap.comp_apply, PolyDisc.channel h u hi,hv]

open ContinuousMap (norm_coe_le_norm)
local notation "pP" => (Finset.univ : Finset ι)
lemma complex_limit {Φ : (ι→ℂ)→ℂ} {f : ℕ → (ι→ℂ)→ℂ}
    (u : TendstoUniformlyOn f Φ atTop (packet c d)) (g : ∀ i:ℕ, Eats (asC c) d (f i)) : AnalyticAt ℂ Φ (asC c) := by
  let c' := asC c; let B: Set (ι→ℂ):= packet c d
  have h':= (g 0).full
  let a : Takes (asC c) d (asC c) := mem_of_mem_nhds (Takes.at h')
  let q : Screen ι→Plain ι := PolyDisc.choose Finset.univ c' d c'
  have q' : Continuous q:= PolyDisc.choose_cont ..
  have he : MapsTo q Set.univ B:=fun z _=> (g 0).remains pP a z
  have hz: ContinuousOn Φ B := u.continuousOn (Frequently.of_forall (fun i=> fun x v=> ((g i).diff x v).continuousAt.continuousWithinAt))
  let D : Reel ι := ⟨fun x=> Φ (q x), continuousOn_univ.mp (hz.comp q'.continuousOn he)⟩
  let M' (i:ℕ) : Reel ι:= (g i).image Finset.univ a
  have hb : Tendsto M' atTop (𝓝 D) := by
    apply Metric.tendsto_nhds.mpr; intro ε e
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp u _ (half_pos e)] with i h
    rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self e); refine (ContinuousMap.norm_le _ (half_pos e).le).mpr (fun x=>?_)
    exact (show _≤ _ from le_of_lt ( (by rw [← dist_eq_norm,dist_comm]; exact h _ (he (mem_univ x)) : ‖f i (q x)-Φ (q x)‖< ε/2) )) -- check dist order
  let T (z:M): Reel ι:= ∏ i:ι,PolyDisc.kernel i c' d z
  obtain ⟨v,hv⟩ := cauchyC pP c' d
  have ht : AnalyticAt ℂ (fun z : M=> v (T z *D)) c' :=
    (v.analyticAt _).comp (( (show AnalyticAt ℂ T c' from Finset.analyticAt_fun_prod _ (fun i _=> forms i h')) ).mul analyticAt_const)
  apply ht.congr
  filter_upwards [Takes.at (c:=c') h'] with x b
  have h0:Tendsto (fun i:ℕ=> v (T x * M' i)) atTop (𝓝 (v (T x * D))) := v.continuous.continuousAt.tendsto.comp (tendsto_const_nhds.mul hb)
  apply tendsto_nhds_unique h0
  have h(i:ℕ) : v (T x * M' i)= f i x := by
    rw [← hv (f i) (g i) x b]; apply congrArg v; apply congrArg (fun y:Reel ι=> T x*y)
    unfold M'
    ext1 z; simp only [Eats.image,ContinuousMap.coe_mk]; congr 1; ext i; simp [PolyDisc.choose,c']
  simp_rw [h]; exact u.tendsto_at (fun i=> ball_subset_closedBall (b i))

omit [DecidableEq ι] in
lemma small_r (r : ℝ) (d : ℕ) (h : 0<r) : ∃ b, 0<b ∧ b<r ∧ ratio b r d * spread d < 1 := by
  let s := (64:ℝ)^d; let v:=64*s^2; let b:=r/(2*v); have hw:1≤s:=one_le_pow₀ (by norm_num); have ht:v≥64:=by unfold v; nlinarith
  refine ⟨b,div_pos h (by linarith),?_ ,?_⟩
  · exact (div_lt_self h (by linarith))
  unfold ratio spread; rw [pow_succ']; change b / r * (64 * s) * s < 1
  unfold b; field_simp; unfold v; nlinarith

include h

lemma Permit.extend : ∃ G : (ι→ℂ)→ℂ,
    AnalyticAt ℂ G (asC c) ∧ (G ∘ asC) =ᶠ[𝓝 c] f := by
  classical -- use existing DecidableEq
  let l := (Finset.univ:Finset ι).toList
  have he(i:ι) : i∈ l := by simp [l]
  obtain ⟨d,g,u,v⟩ := small_r r l.length h.radius_pos
  obtain ⟨G,b⟩ := uniform l he g u h v
  refine ⟨G, complex_limit b (fun i=> ⟨g,fun x hx=>?_⟩), ?_⟩
  · exact essence (ι → ℂ) id differentiable_id l (by simp [he]) (fun j w=> captures c d (bold f) i i j l w le_rfl g) x -- tune differentiability expects constant comp id
  filter_upwards [show ∀ᶠ x in 𝓝 c, ∀ i : ι, x i∈Metric.ball (c i) d from eventually_all.mpr fun i=> (continuous_apply i).continuousAt.tendsto.eventually (ball_mem_nhds _ g)] with t ht
  have hz : asC t∈ packet c d := (real_packet _).2 (fun i=> ball_subset_closedBall (ht i))
  exact tendsto_nhds_unique (b.tendsto_at hz) (on_real l g u h v t hz)

theorem Permit.revives : AnalyticAt ℝ f c := by
  obtain ⟨F',a,p⟩ := Permit.extend h
  apply AnalyticAt.congr (f:=F' ∘ asC) _ p
  refine a.restrictScalars.comp (analyticAt_pi_iff.mpr (fun i=>?_))
  let P := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : ι=>ℝ) i
  exact ((ofRealCLM.comp P).analyticAt c)
end YM.PolyDisc.Revival
