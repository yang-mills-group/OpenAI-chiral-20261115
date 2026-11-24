import YM.SU5.Reconstruction.Chambers.Analytic.Revive
import YM.SU5.Reconstruction.Chambers.Analytic.Clock
/-!
# Produce budgets in any ALL-slots coordinate chamber; allow tangled orders across axes
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
open Function Filter Metric Set Analysis SelectionAnalysis OS
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal Classical
open Schedule Fixture Compose YM.PolyDisc.Revival

variable {α : Type} [hFin : Fintype α] {Γ : AddSubgroup ℝ} {j : Axis} {H : Hilbert}
variable (W : α → H.Op)
variable (G : Fixture Γ α)
variable (o : Axis→ List α) (q : Axis→Axis→Γ) (P : α→Axis→ℝ)
variable (h : P∈ G.ready q o)
local notation "K"=> uncurry P

include h in
lemma canCover : ∀ᶠ r in 𝓝[>] (0:ℝ), (0<r ∧ ∀ p : α × Axis → ℝ,
    asC p∈ packet (uncurry P) r → curry p∈ G.ready q o) := by
  have h0 : uncurry P ∈ (curry: (α × Axis→ℝ)→ (α→Axis→ℝ)) ⁻¹' G.ready q o := h
  have ht : Continuous (curry: (α × Axis→ℝ)→ (α→Axis→ℝ)) := continuous_pi fun i=> continuous_pi fun j=>continuous_apply (i,j)
  have hp := ( (G.ready_open q o).preimage ht).mem_nhds h0
  obtain ⟨d,hd,e⟩ := Metric.mem_nhds_iff.mp hp
  filter_upwards [self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hd)] with r (u : 0< r) t
  refine ⟨u,fun p h=>e (Metric.closedBall_subset_ball t ?_)⟩
  rw [Metric.mem_closedBall,dist_pi_le_iff u.le]; exact (real_packet p).1 h

omit hFin
lemma each_part {c : α × Axis → ℝ}{d r:ℝ} (p: α × Axis → ℝ) (h : asC p∈packet c d)(i:α × Axis) (a : r∈closedBall (c i) d) :
    asC (update p i r)∈packet c d := by rw [← update_C]; apply replace i h; rw [Metric.mem_closedBall,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,←dist_eq_norm]; exact a

-- decEq α/ι: `Permit` class argument instance. explicit? notation uses classical noncomputable via open scoped above. ok clients may have different, use omit.
section provide
variable (S : OS.Semigroup H j)
variable (r : ℝ) (g : 0<r) (b : ∀ p : α × Axis→ℝ, asC p∈ packet (uncurry P) r→ curry p∈ G.ready q o)
variable (x y:H)
variable {f : (α→Axis→ℝ)→ℂ}
local notation "E₀" ω:max => ((pointsOp S G W ω (paste (q j)) (o j)) y)
local notation "u₀" k:max=> uncurry P k

include g b in
lemma specials (i : α) (p : α × Axis→ℝ) (u : asC p∈packet (uncurry P) r)
    (w : ∀ p, p∈ G.ready q o → f p=inner ℂ x (E₀ p)) :
    ∃ l : ℂ→ℂ, DiffContOnCl ℂ l (ball (P i j:ℂ) r) ∧
      (∀ z∈ sphere (P i j:ℂ) r, ‖l z‖ ≤ ‖x‖ * upright W (o j)* ‖y‖) ∧
      ∀ v:ℝ, v∈closedBall (P i j) r → l v=f (curry (update p (i,j) v)) := by
  let l (z:ℂ) : α→ℂ := update (fun i=> (p (i,j):ℂ)) i z
  let e (z:ℂ) := curry (update p (i,j) z.re)
  let X := paste (q j)
  let Y (z:ℂ) := curve S G W (curry p) X (l z) (X j:ℂ) (o j) y
  have hv(z:ℂ)(a : z∈closedBall (P i j:ℂ) r): G.permission j true (e z) X (o j) := by
    apply b _ (each_part p u (i,j) ?_) j
    change dist z.re (P i j)≤ r
    rw [Metric.mem_closedBall,dist_eq_norm] at a; rw [Real.dist_eq, ← Complex.ofReal_re (P i j), ← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans a
  have ready(z:ℂ)(a : z∈closedBall (P i j:ℂ) r) : ProperCone G j (l z) (X j:ℂ) (o j) := by
    apply can_go G (e z) X (o j) (hv z a); intro k; by_cases v:k=i <;> simp [v,l,e]
  refine ⟨fun z=> inner ℂ x (Y z),⟨fun z a=>?_,?_⟩,?_,?_⟩
  · exact (diff z (ball_subset_closedBall a) (ready z (ball_subset_closedBall a)) z rfl |>.differentiableWithinAt) -- tune
  · rw [closure_ball (P i j:ℂ) g.ne']; exact fun z a=> (diff z a (ready z a) z rfl).continuousAt.continuousWithinAt
  · intro z t; rw [mul_assoc]; exact (norm_inner_le_norm (𝕜:=ℂ) x (Y z)).trans (mul_le_mul_of_nonneg_left (spin_price S G W (curry p) X _ _ _ (ready z (sphere_subset_closedBall t)) _) (norm_nonneg _))
  intro v t; rw [w _ (b _ (each_part p u (i,j) t))]; unfold Y; dsimp only
  rw [real_points S G W (curry p) X (l:=o j) (curry (update p (i,j) v)) (paste (q j))]
  · exact (b _ (each_part p u (i,j) t)) j
  · intro k t; refine ⟨rfl,?_⟩; intro i; simp [t]
  intro j'; by_cases t:j'=i <;> simp [t,l]
where -- easier generic
  diff (z:ℂ)(_ : z∈closedBall (P i j:ℂ) r) (h : ProperCone G j (update (fun k=> (p (k,j):ℂ)) i z) (paste (q j) j:ℂ) (o j)) (a:ℂ)(b:z=a) :
      DifferentiableAt ℂ (fun z':ℂ=> inner ℂ x (curve S G W (curry p) (paste (q j)) (update (fun k=> (p (k,j):ℂ)) i z') (paste (q j) j:ℂ) (o j) y)) a := by
    subst a; apply (innerSL ℂ x).differentiableAt.comp z
    refine curve_diff S G W (curry p) (paste (q j)) (o j) y z (fun (z:ℂ)=> (paste (q j) j:ℂ)) ?_ (differentiableAt_const _) h
    intro i'; by_cases p:i'=i <;> simp [p,differentiableAt_fun_id]
end provide

-- finite type gives simultaneous costs.
variable (T : Axis→Hilbert) (S : ∀ j:Axis,OS.Semigroup (T j) j) (U : (i:Axis)→α→(T i).Op)
variable (x y : ∀i:Axis, T i) {f : (α→Axis→ℝ)→ℂ}
variable (hA : ∀ p,p∈G.ready q o → ∀ i : Axis, f p=inner ℂ (x i) (pointsOp (S i) G (U i) p (paste (q i)) (o i) (y i)))
include h hA hFin
lemma certified : ∃ r K':ℝ, Permit (uncurry P) r K' (f ∘ curry) := by
  obtain ⟨r,g,b⟩ := (canCover G o q P h).exists
  let t(i:Axis) := ‖x i‖ * upright (U i) (o i) * ‖y i‖
  have he(i:Axis): 0≤ t i := by have e := cost_pos (W:=U i) (l:=o i); unfold t; positivity
  refine ⟨r, ∑ i:Axis,t i,g,Finset.sum_nonneg (fun i _=> he i),fun p ht v=>?_⟩
  rcases v with ⟨k,j⟩; obtain ⟨g,a,b,v⟩:= specials (U j) G o q P (S j) r g b (x j) (y j) k p ht (fun p h=>hA p h j)
  exact ⟨g,a,fun z h=>(b z h).trans (Finset.single_le_sum (f:=t) (fun i _=> he i) (Finset.mem_univ j)),v⟩

lemma attained : (∃ G₀ : (α × Axis→ℂ)→ℂ, AnalyticAt ℂ G₀ (asC (uncurry P)) ∧
    (G₀ ∘ asC)=ᶠ[𝓝 (uncurry P)] (f ∘ curry)) ∧ AnalyticAt ℝ f P := by
  obtain ⟨r,t,h⟩ := certified G o q P h T S U x y hA
  refine ⟨h.extend,?_⟩; apply (h.revives).comp (f:=uncurry) -- composition maybe explicit
  refine analyticAt_pi_iff.mpr ?_; intro i; rcases i with ⟨k,j⟩
  let u:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:α=>Axis→ℝ) k
  let v:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Axis=>ℝ) j
  exact ((v.comp u).analyticAt P)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
