import YM.CF.Cadre.Rival
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open PowerSeries
variable (V: leaf A→ Finset A→PS)(v:∀ X:Palot.leaf A,∀ D ⊆ X.val,cent (V X D))(Q: leaf A→ℝ)(q:0≤Q)(κ:ℝ)(m:1≤κ)(L w:ℝ)(b:leaf A→ℝ)
variable {x s:ℝ}(T:Tour b s) (γ c d e h:ℝ)(g:h≥0)(k:∀ o:A,serif V κ L w b o 0 0<γ)
local notation "B"=> loom_v L w b
local notation "K_"=> seed_v V κ
local notation "S"=> serif V κ L w b
variable (p:0 ≤ L-w*h) (r:0 ≤ w)(mQ:0 ≤ γ)(z:Palot.leaf A→ℝ)(z₁:0 ≤ z)
variable (hC:∀ i:A, nook (fog (loom_v L w b 0) Q γ) i ≤ c)(hD:∀ i:A,shelfR (fog (loom_v L w b 0) Q γ) i ≤ d)(hI:∀ i:A, nook (z*loom_v L w b 0) i ≤ e)(hm:0 ≤ c)(hw:s*c ≤ w)
-- For x=1 forms; expansions actual.Reprice Width relative to d organic.
variable (H:∀ i:A,∀ n:ℕ,serif V κ L w b i n 1 ≤ γ)
include m v H
lemma ray (X:ΣA)(D: Finset A)(r:D⊆X.val):cent (V X D) ∧ Aqua (V X D):=by
 let B':=V X D; have he:=v X D r; obtain ⟨i,z⟩:=X.property; let d:=B 1 X; have hv:d>0:=Real.exp_pos _
 have hx(j:ℕ):mintL j 1 B' ≤ γ/d:=by
    apply (le_div_iff₀ hv).mpr; apply le_trans _ (H i j); let A':= K_ j 1; have hu(X:ΣA)(D:Finset A)(u:D⊆X.val):0≤ mintL j 1 (V X D):=(v X D u).negℜ _ zero_le_one _; have hz(X:ΣA)(D:Finset A)(u:D⊆X.val):0 ≤ duty κ D * mintL j 1 (V X D):= mul_nonneg ((duty_i D m).trans' zero_le_one) (hu X D u)
    have ht:mintL j 1 B' ≤ A' X:= le_trans (le_mul_of_one_le_left (hu X D r) (duty_i _ m)) (single_le_sum (fun i p=>hz X i (mem_powerset.mp p)) (mem_powerset.mpr r)); have hp:0≤A':=fun i=> sum_nonneg fun j p=>hz i j (mem_powerset.mp p); exact (mul_le_mul_of_nonneg_right ht hv.le).trans (single_le_sum (fun j (_:j∈spark i)=>mul_nonneg (hp j) (show 0≤ B 1 j from Real.exp_pos ..|>.le)) (show X∈spark i from mem_filter.mpr ⟨mem_univ _,z⟩)) -- lean implicit.
 refine ⟨he,summable_of_sum_range_le (c:= max 0 (γ/d)) (fun i=>norm_nonneg _) (fun i=>?_ )⟩; cases i; · simp
 rename_i i; refine le_trans ?_ ((hx i).trans (le_max_right ..)); unfold mintL; apply sum_le_sum; intro i _; rw [one_pow,one_mul,Real.norm_of_nonneg]; exact he _
lemma fort(i:A): nook ((roofL (fun X D=>hitU (V X D)) κ) * B 1) i≤ γ:=by
 refine le_of_tendsto (show Tendsto (fun n=> S i n 1) atTop _ from ?_) (Eventually.of_forall (H i)); apply tendsto_finsetSum; intro X _; apply Tendsto.mul _ tendsto_const_nhds; apply tendsto_finsetSum ; intro D r; apply Tendsto.const_mul; let F:=V X D; have hx:= (ray V v κ m L w b γ H X D (mem_powerset.mp r)).2.of_norm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1); change Tendsto (fun s=>mintL s 1 (V X D)) atTop (𝓝 _); simpa only [mintL,bark,Function.comp_def, add_comm 1,one_pow,one_mul] using hx
end YM.CF.Cadre
