/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Ink.WavePort
import YM.Shift.Osc
/-! Full-module port of analytic theory from pinned YM/Shift/Breath, Osc (actual C-chain proof reuses)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.InkWaves
open Boundary
open Boundary.Waves (moves coal)
open Filter Set Function MeasureTheory Probe Complex
open scoped Topology InnerProductSpace ContDiff BigOperators Interval ENNReal
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (F : InkWaves V)

def rocks (v : Fin n → V) (y : Heights n) (f : Joint n) (t : ℝ) (k : ℕ) := F.psi v (y+t • rate n) (moves k f)

def pol (v : Fin n → V) (y : Heights n) (f : Joint n) (t : ℝ) (m : ℕ) :=
    ∑ k ∈ Finset.range (m+1), coal t k * F.rocks v y f t k

def wind (v : Fin n → V) (m : ℕ) (y : Heights n) (f : Joint n) (t : ℝ) := coal t m * F.rocks v y f t (m+1)

def desired (v : Fin n → V) (m : ℕ) (y : Heights n) (f : Joint n) := F.pol v y f 1 m -∫ s : ℝ in Ioc 0 1,
    F.wind v m y f s

private lemma pipe (t : ℝ) (m : ℕ) : HasDerivAt (fun t : ℝ => coal t (m+1)) (-coal t m) t := by
  have he := (Complex.ofRealCLM.hasDerivAt (x:=t)).neg.pow (m+1) |>.mul_const ((m+1).factorial:ℂ)⁻¹
  apply he.congr_deriv
  unfold coal
  have hp : (m.factorial:ℂ)≠0 := by norm_cast; exact Nat.factorial_ne_zero _
  have hv : (m:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv]
  push_cast; simp only [Pi.neg_apply, ofRealCLM_apply,ofReal_one]
  field_simp

lemma right (h : F.Lines) (v : Fin n → V) (y : Heights n) (f : Joint n) (m : ℕ) (x : ℝ)
    (p : y+x • rate n∈east n) : HasDerivAt (fun t => F.pol v y f t m) (F.wind v m y f x) x := by
  have H (k) : HasDerivAt (fun t => F.rocks v y f t k) (F.rocks v y f x (k+1)) x := h n v (moves k f) y _ x p
  induction m with
  | zero => simpa [wind,pol,coal] using! H 0
  | succ m IH =>
    have ht := IH.add ((pipe x m).mul (H (m+1)))
    simp_rw [show (fun t => F.pol v y f t (m+1))= (fun t => F.pol v y f t m+coal t (m+1)*F.rocks v y f t (m+1)) from funext fun t => Finset.sum_range_succ (fun k ↦ coal t k*_) _]
    apply ht.congr_deriv; unfold wind; ring

theorem meant (ha : F.Along) (h : F.Lines) (v : Fin n → V) (y : Heights n) (hy : y∈east n)
    (f : Joint n) (m : ℕ) : F.desired v m y f= F.psi v y f := by
  unfold desired
  have he (x : ℝ) (hx : x ∈ uIcc (0:ℝ) 1) : y+x • rate n∈east n := grows hy (by rw [uIcc_of_le zero_le_one] at hx; exact hx.1)
  have ht : F.pol v y f 0 m= F.psi v y f := by
    unfold pol
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp [coal,rocks,moves]
    intro b _ hb; simp [coal,zero_pow hb]
  rw [← intervalIntegral.integral_of_le (a:=(0:ℝ)) (b:=1) zero_le_one, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => F.right h v y f m x (he x hx)), ht]; swap
  · have hh : ContinuousOn (F.wind v m y f) (uIcc (0:ℝ) 1) := by
      unfold wind; apply ContinuousOn.mul
      · unfold coal; fun_prop
      exact (ha n v _).comp (show ContinuousOn (fun t : ℝ => y+t • rate n) _ from by fun_prop) he
    exact hh.intervalIntegrable
  abel

lemma expense {v : Fin n → V} (m : ℕ) {C : ℝ}
    (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)
    (y : Heights n) (hy : y∈sunrise n) (f : Joint n) {t : ℝ} (hr : t∈Ioc (0:ℝ) 1) :
    ‖F.wind v m y f t‖ ≤ C*weight (moves (m+1) f) := by
  have hF : ‖(m.factorial:ℂ)‖ = (m.factorial:ℝ) := by exact Complex.norm_natCast _
  have he : ((m.factorial:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos m)
  rw [wind,norm_mul,coal,norm_mul, Complex.norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr.1.le, norm_inv,hF]
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg hr.1.le m) he) (norm_nonneg _))
    (beam F m C hm hy (moves (m+1) f) hr)

theorem maintains (v : Fin n → V) (ha : F.Along) (m : ℕ) {C : ℝ}
    (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)
    (f : Joint n) : ContinuousOn (fun y => F.desired v m y f) (sunrise n) := by
  intro s hs
  unfold desired
  apply ContinuousWithinAt.sub
  · apply ContinuousOn.continuousWithinAt (s:=sunrise n) (x:=s) (by
      unfold pol
      apply continuousOn_finsetSum; intro i _; apply ContinuousOn.const_mul
      exact (ha n v (moves _ f)).comp (continuous_id.add continuous_const).continuousOn (fun _ H => dawns H zero_lt_one)) hs
  refine tendsto_integral_filter_of_dominated_convergence (F:=fun (y : Heights n) => F.wind v m y f)
    (f:= F.wind v m s f) (bound := fun t : ℝ => C*weight (moves (m+1) f)) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have ht : ContinuousOn (F.wind v m y f) (Ioc 0 1) := by
      unfold wind; apply ContinuousOn.mul; unfold coal; fun_prop
      exact (ha n v _).comp (show ContinuousOn (fun t : ℝ => y+t • rate n) _ from by fun_prop) (fun _ p => dawns hy p.1)
    exact ht.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x h => F.expense m hm _ hy f h
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro x hx
  have H : ContinuousOn (fun y : Heights n => F.psi v (y+x • rate n) (moves (m+1) f)) (sunrise n) :=
    (ha n v _).comp (continuous_id.add continuous_const).continuousOn (fun _ hy => dawns hy hx.1)
  exact tendsto_const_nhds.mul (H s hs)
end YM.SatinWFixed.InkWaves

namespace YM.SatinWFixed.InkWaves
open Boundary
open Boundary.Waves (moves coal toll tolls)
open Filter Set Function MeasureTheory Probe Complex LinearMap
open scoped Topology ContDiff BigOperators Interval ENNReal
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (F : InkWaves V)

section price
variable {v : Fin n → V} {C : ℝ} {m : ℕ}
variable (hm : ∀ (y : Heights n) (k : ℝ), k ∈ Ioc 0 1 → broad y k → ∀ x, ‖F.restricted v y x‖ ≤ C*k⁻¹^m)

include hm
lemma cost (y) (hy : y∈sunrise n) (f : Joint n) : ‖F.desired v m y f‖ ≤ toll f C m := by
  unfold desired toll
  refine (norm_sub_le ..).trans (add_le_add ?_ ?_)
  · unfold pol; apply (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => ?_)
    have he := beam F m C hm hy (moves j f) (show (1:ℝ)∈Ioc 0 1 from ⟨zero_lt_one,le_rfl⟩)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (by simpa only [rocks,one_pow,one_mul] using he) (norm_nonneg _)
  have hh := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0:ℝ) 1))
    (g := fun _ => C*weight (moves (m+1) f)) (f := F.wind v m y f) (integrable_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun _ hx => F.expense _ hm _ hy f hx)
  simpa using hh

lemma storm (h : F.Along) (p : F.Lines) (y) (hy : y∈sunrise n) (f : Joint n) : Tendsto (fun x => F.psi v x f)
    (𝓝[east n] y) (𝓝 (F.desired v m y f)) := by
  apply ((F.maintains v h _ hm f y hy).mono fun x t => bigger (n:=n) t).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx using F.meant h p _ _ hx f m
end price

lemma seeks (h : F.Bounds) (ha : F.Along) (hm : F.Lines) (hp : F.Breathes) (y) (hy : y∈sunrise n) :
    ∃ W : MultilinearMap ℂ (fun _ : Fin n => V) (Distn (Points n)), ∀ (v : Fin n → V) (f : Joint n),
    Tendsto (fun t => F.psi v t f) (𝓝[east n] y) (𝓝 (W v f)) := by
  classical
  let T := 𝓝[east n] y
  have hT : T.NeBot := awaits hy
  choose m C hC H using hp n
  let g (v : Fin n → V) := F.desired v (m v) y
  have hg v f : Tendsto (fun t => F.psi v t f) T (𝓝 (g v f)) := F.storm (H v) ha hm y hy f
  let D (v : Fin n → V) : Joint n→ₗ[ℂ] ℂ :=
    { toFun := g v
      map_add' := by
        intro f p; refine tendsto_nhds_unique (hg v (f+p)) (((hg v f).add (hg v p)).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi; rw [← integral_add (h n v t ht f) (h n v t ht p)]
        apply integral_congr_ae; filter_upwards with x; simp [mul_add]
      map_smul' := by
        intro c f; apply tendsto_nhds_unique (hg v (c•f)) (((hg v f).const_mul c).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi; rw [← integral_const_mul]; congr! 1; ext x; simp; ring }
  let W (v) : Distn (Points n) := ⟨D v, sways (fun f => toll f (C v) (m v)) (tolls (m v) (C v)).2 (tolls (m v) (C v)).1 (fun f => F.cost (H v) y hy f)⟩
  let B : MultilinearMap ℂ (fun _ : Fin n => V) (Distn (Points n)) :=
    { toFun := W
      map_update_add' := by
        intro _ v j x z; ext1 f
        refine tendsto_nhds_unique (hg (update v j (x+z)) f) (((hg (update v j x) f).add (hg (update v j z) f)).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi
        rw [← integral_add (h n _ t ht _) (h n _ t ht _)]
        congr! 1; ext p; simp [restricted,add_mul]
      map_update_smul' := by
        intro _ v j c x; ext1 f
        refine tendsto_nhds_unique (hg (update v j (c•x)) f) (((hg (update v j x) f).const_mul c).congr' ?_)
        filter_upwards [self_mem_nhdsWithin (a:=y) (s:=east n)] with t ht
        unfold psi
        rw [← integral_const_mul]; congr! 1; ext p; simp [restricted,mul_assoc] }
  exact ⟨B,hg⟩

/-- All ordered heights, *not just fixed slopes*, as required for Hilbert vector limits. -/
lemma jointly (h : F.Bounds) (ha : F.Along) (hm : F.Lines) (hp : F.Breathes) :
    ∃ W : WView V, F.NonTangentialFree W := by
  choose B hB using fun n : ℕ => F.seeks h ha hm hp 0 (light n)
  exact ⟨⟨B⟩,⟨h,hB⟩⟩
end YM.SatinWFixed.InkWaves
