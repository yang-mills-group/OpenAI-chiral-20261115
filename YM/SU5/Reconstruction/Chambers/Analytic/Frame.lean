import YM.SU5.Reconstruction.Chambers.Analytic.Sample
import YM.Analysis.Polydisc
import Mathlib.Analysis.Calculus.Deriv.Polynomial
/-!
# Amplify across the spatially extended analytic budget.

Reproduction of full multi-variate polynomials without requiring all variables
be simultaneously complex in the INPUT data. We never use "separately real
 analytic" without uniform radii & bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.PolyDisc.Revival
open Function Filter Topology Complex Set Metric Polynomial
open scoped BigOperators NNReal ENNReal
variable {ι : Type} [DecidableEq ι]
local notation "R" => ι→ℝ
local notation "M" => (ι→ℂ)
local notation "F" => (M→ℂ)

variable (c : ι→ℝ) (d r K : ℝ) (f : (ι→ℂ)→ℂ)
def asC (a : ι→ℝ) : ι→ℂ := fun i=> ((a i):ℝ)
def asR (a : M) : R := fun i=> (a i).re
omit [DecidableEq ι] in
lemma c_to_r (a:ι→ℝ) : asR (asC a)=a := by ext i; simp [asC,asR]
omit [DecidableEq ι] in
lemma c_at (a:ι→ℝ)(i:ι) : asC a i=a i:= rfl

def packet (c : ι→ℝ) (d : ℝ) : Set M := {x | ∀ i:ι, x i ∈ closedBall (asC c i) d}
def patch (s : List ι) (x : M) := x ∈ packet c d ∧ ∀ i∉ s, x i= (((asR x i):ℝ):ℂ)
omit [DecidableEq ι] in
lemma patch_iff (x : M) : patch c d [] x ↔ x∈ packet c d ∧ asC (asR x)=x := by
  refine and_congr_right fun _=> ⟨fun h=> funext fun i=> (h i List.not_mem_nil).symm,fun h i _=>?_⟩
  exact (congrFun h i).symm

variable {c d}
omit [DecidableEq ι] in
lemma real_packet (x:ι→ℝ) : asC x∈ packet c d ↔ ∀ i : ι,x i∈closedBall (c i) d := by
  change (∀ i, _)↔_; refine forall_congr' fun i=>?_; simp only [c_at, mem_closedBall,dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real]

omit [DecidableEq ι] in
lemma patch_grows {s t : List ι}{x:M} (p : patch c d s x) (h:∀ i∈s,i∈ t) : patch c d t x :=
 ⟨p.1,fun i b=> p.2 i fun v=>b (h i v)⟩
lemma replace (i : ι) {x : M} {v : ℂ} (a : x∈ packet c d) (b : v ∈ closedBall ((c i):ℂ) d) :
    update x i v∈ packet c d := by
  intro j; by_cases h:j=i
  · subst j; simpa only [c_at,update_self] using b
  rw [update_of_ne h]; exact a j
lemma patch_reset (i : ι){x:M}{s : List ι}{v:ℝ} (a : (v:ℂ)∈closedBall ((c i):ℂ) d) (b : patch c d (i::s) x) : patch c d s (update x i (v:ℂ)) := by
  refine ⟨replace i b.1 a,fun j h =>?_⟩; by_cases t : j=i
  · subst j; simp [asR]
  simp only [update_of_ne t,asR]; exact b.2 j (by simp [t,h])

open Sample
variable (c d)
variable (n m : ℕ) (i j : ι)

noncomputable def pull : ((ι→ℂ)→ℂ) →ₗ[ℂ] ((ι→ℂ)→ℂ) where
  toFun f:= fun z=> ∑ k∈ Finset.range (n+1), weights (c i) d n k (z i) * f (update z i (nodes (c i) d n k))
  map_add' f g:=by ext1 x; simp_rw [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' b f:= by ext1 x; simp_rw [Pi.smul_apply, RingHom.id_apply,smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro; intros; ring

local notation "P" => pull c d
lemma pull_sum (z:M) : pull c d n i f z= (poly (c i) d n (fun v=> f (update z i v))).eval (z i) := by rw [poly_eval]; rfl

lemma pull_twice {n m : ℕ} (h : n≤m) (g : 0<d) : pull c d m i (P n i f)= P n i f := by
  ext1 z
  simp_rw [pull_sum _ _ _ m i, pull_sum _ _ _ n i]
  simp_rw [update_idem,update_self]; -- tune
  rw [ifPol]
  · exact g
  apply lt_of_lt_of_le (Lagrange.degree_interpolate_lt (fun v=> f (update z i (nodes (c i) d n v))) (room _ _ g|>.injOn)) (by gcongr)

lemma pull_comm (h : i≠j) : P m i (P n j f)= P n j (P m i f) := by
  ext1 x; unfold pull; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [update_of_ne h,update_of_ne h.symm,Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro r _; rw [update_comm h]; ring

noncomputable def stage (l:List ι) : ((ι→ℂ)→ℂ) →ₗ[ℂ] ((ι→ℂ)→ℂ) := l.foldr (fun i p => (pull c d n i).comp p) LinearMap.id
local notation "Λ" => stage c d n
lemma stage_step (l:List ι) : Λ (i::l) f=P n i (Λ l f) := rfl
lemma captures (l : List ι)(h : i∈l)(v : n≤m)(g : 0<d): P m i (Λ l f)=Λ l f := by
  induction l with
  | nil=> simp at h
  | cons b l ih=> by_cases t:i=b; subst b; exact pull_twice c d (Λ l f) i v g; rw [stage_step,pull_comm c d (Λ l f) n m i b t, ih (by simpa [t] using h)]

lemma pull_bounds (h : 0≤ K) (w:0<d) (s : List ι) (u : ∀ x:M, patch c d s x→‖f x‖≤ K) :
    ∀ x:M, patch c d (i::s) x→‖pull c d n i f x‖≤ (64:ℝ)^(n+1)*K := by
  intro x a; let S:= Finset.range (n+1); unfold pull; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
  let K' (k:ℕ) := ‖weights (c i) d n k (x i)‖
  refine (norm_sum_le (s:=S) ..).trans ?_ -- argument names
  refine (Finset.sum_le_sum (g:=fun k=> K' k * K) (fun k hk=>?_)).trans ?_
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (u _ (patch_reset i (complex_inner _ n w hk) a)) (norm_nonneg _)
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (cost_sum (c i) w n (a.1 i)) h

-- amplify when all axes reproduced. List induction, no uniform functions on whole M required.
lemma lifted_bound (h : 0≤ K) (w:0<d)(s : List ι) (e : ∀ i ∈ s,pull c d n i f=f)
    (u : ∀ x:M, patch c d [] x→‖f x‖≤ K) :
    ∀ x:M, patch c d s x → ‖f x‖ ≤ ((64:ℝ)^(n+1))^s.length*K := by
  induction s with
  |nil=> simpa using u
  |cons i l ih=>
      intro x t; rw [List.length_cons,pow_succ',mul_assoc]; nth_rw 1 [← e i (List.Mem.head ..)]
      exact pull_bounds c d _ f n i (by positivity) w l (ih (fun i t=>e i (List.Mem.tail _ t))) _ t

lemma update_C (x:ι→ℝ)(k:ι)(v:ℝ): update (asC x) k (v:ℂ)=asC (update x k v):=by ext1 i; by_cases s:i=k <;>simp [asC,s]

variable {c d n r K}
structure Permit (c: ι→ℝ)(r K:ℝ)(f : (ι→ℝ)→ℂ) : Prop where
  radius_pos : 0 < r
  base : 0 ≤ K
  sectionC (p : ι→ℝ) (hp : asC p∈ packet c r) (i : ι) : ∃ g : ℂ→ℂ,
    DiffContOnCl ℂ g (ball ((c i):ℂ) r) ∧
    (∀ z∈sphere ((c i):ℂ) r, ‖g z‖≤ K) ∧
    ∀ x:ℝ, x∈closedBall (c i) r → g (x:ℂ) = f (update p i x)

def bold (f : (ι→ℝ)→ℂ) : (ι→ℂ)→ℂ := f ∘ asR
variable {f' : (ι→ℝ)→ℂ} (g : 0<d) (e : d<r) (p : Permit c r K f')
local notation "Λ'" => (1+64^(n+1):ℝ)
local notation "ε" => (d/r)
local notation "c₀" n:max => ((d/r)^(n+1)*(1-d/r)⁻¹*K)
include g e p in
lemma permit_approach (w : M) (b : patch c d [] w) :
    ‖bold f' w - pull c d n i (bold f') w‖ ≤ (1+64^(n+1):ℝ)* ((d/r)^(n+1)*(1-d/r)⁻¹*K) := by
  obtain ⟨hw,hY⟩ := (patch_iff c d w).1 b -- order
  let y:=asR w
  obtain ⟨u,h1,h2,h3⟩:= p.sectionC y (fun i=> closedBall_subset_closedBall e.le ( (hY.symm ▸ hw) i)) i
  let v (x:ℂ):= bold f' (update w i x); have he(x:ℝ)(t : x ∈ closedBall (c i) r): v (x:ℂ)=u (x:ℂ) := by
    rw [h3 x t]; unfold v; conv_lhs => rw [← hY,update_C]; unfold bold; rw [Function.comp_apply,c_to_r]
  have hx: poly (c i) d n u=poly (c i) d n v :=
    Lagrange.interpolate_eq_of_values_eq_on _ _ (fun i ht => (he _ (closedBall_subset_closedBall e.le (node_inner _ n g ht))).symm)
  have t : w i=(y i:ℂ) := (congrFun hY i).symm
  have ht : bold f' w=u (w i) := calc
    _ = v (w i):=by unfold v; rw [update_eq_self]
    _ = _ := t.symm ▸ he _ (closedBall_subset_closedBall e.le ((real_packet y).1 (hY.symm ▸ hw) i)) -- named args?
  rw [pull_sum]; change ‖bold f' w - Polynomial.eval _ (Sample.poly _ _ _ v)‖ ≤ _; rw [←hx,ht]
  exact approximate d g e h1 h2 _ _ (hw i)

-- Real extrapolation cost (arbitrary tolerance ratio by going much smaller in d). Avoid
-- conflating smaller edge widths with the supports in the actual model.
lemma fixed_price {L} (h : 0≤ L) (c : ι→ℝ) {d:ℝ} (w:0<d)(f : (ι→ℂ)→ℂ)(u : ∀ x:(ι→ℂ), patch c d [] x→‖f x‖≤ L)(n:ℕ) (x : ι→ℂ) (e : patch c d [] x) :
    ‖pull c d n i f x‖ ≤ 64^(n+1)*L := pull_bounds c d L f n i h w [] u x (patch_grows e (by simp))

include g e p in
lemma price_real (s : List ι) (x : M) (u : patch c d [] x) :
    ‖stage c d n s (bold f') x-bold f' x‖ ≤
    c₀ n * (1+ 64^(n+1)) * (s.length:ℝ) * (64^(n+1))^s.length := by
  have ha : 0 ≤ c₀ n := by have t : 0≤ 1-d/r:=sub_nonneg.mpr (by have h:= div_lt_one (g.trans e)|>.mpr e; exact h.le); have he:= p.base; have h':=p.radius_pos; positivity
  induction s generalizing x with
  |nil=> simp [stage]
  |cons i s ih=>
     let F' := stage c d n s (bold f')
     let L:ℝ := c₀ n*(1+64^(n+1)) * (s.length:ℝ) * (64^(n+1))^s.length
     have ht : 1 ≤ (64:ℝ)^(n+1) := one_le_pow₀ (by norm_num); have hu: 0≤ L := by unfold L; positivity
     have hb := fixed_price (i:=i) hu c g (F'-bold f') ih n x u
     change ‖(P n i (F'-bold f')) x‖ ≤ _ at hb; rw [map_sub,Pi.sub_apply] at hb
     have t : ‖(P n i (bold f')) x-bold f' x‖ ≤ c₀ n*(1+64^(n+1)):=by rw [norm_sub_rev, mul_comm (c₀ n)]; exact permit_approach i g e p x u
     rw [stage_step,List.length_cons,Nat.cast_add_one,pow_succ' _ s.length]; refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hb t).trans ?_)
     unfold L; -- show
     have he := one_le_pow₀ ht (n:=s.length) -- args?
     let M₀:ℝ := 64^(n+1); have he' : c₀ n*(1+M₀)≤ c₀ n*(1+M₀)*(M₀*M₀^s.length):=le_mul_of_one_le_right (by unfold M₀; positivity) (one_le_mul_of_one_le_of_one_le ht he)
     change M₀ * (c₀ n *(1+M₀) * (s.length:ℝ) * M₀^s.length) + c₀ n * (1+M₀) ≤ c₀ n*(1+M₀)*((s.length:ℝ)+1)*(M₀*M₀^s.length)
     refine (add_le_add_right he' _).trans (le_of_eq ?_) -- orientation API?
     ring

section allpoints
variable [Fintype ι] (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable (y : Y→ι→ℂ)
-- by differentiability in finite linear evaluation of this polynomial family. Axiomatic
-- budget equations allow also differences. Every captured coordinate in s makes full
-- evaluation analytic in those coords, holding the others fixed.
omit [Fintype ι] in
lemma essence {f : (ι→ℂ)→ℂ} (v : Differentiable ℂ y) (s : List ι) (t : ∀ i∉ s,∀ x x':Y,y x i=y x' i)
    (h : ∀ i∈ s, pull c d n i f=f) : Differentiable ℂ (fun x=> f (y x)) := by
  induction s generalizing y with
  |nil=>
    intro x; rw [show (fun z=>f (y z))=(fun _=> f (y x)) from funext (fun z=> congrArg f (funext fun i=> t i (List.not_mem_nil) ..))]; exact differentiableAt_const _
  |cons i s ih=>
    have he : (fun x=> f (y x))=(fun x=> (pull c d n i f) (y x)) := by rw [h i (List.Mem.head ..)]
    rw [he]; unfold pull; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
    apply Differentiable.fun_sum ; intro j _
    refine (Polynomial.differentiable _).comp (differentiable_pi.mp v i) |>.mul ?_ -- name
    let y'(x:Y) : M := update (y x) i (nodes (c i) d n j)
    have ht : Differentiable ℂ y' := by
      apply differentiable_pi.mpr; intro b
      by_cases p:b=i
      · unfold y'; simp only [p,update_self]; exact differentiable_const _
      unfold y'; simp only [update_of_ne p]; exact differentiable_pi.mp v b
    apply ih y' ht _ (fun i t=> h i (List.Mem.tail _ t))
    intro b p x z; by_cases p':b=i <;> simp [p',y']; exact t _ (by simp [p,p']) _ _ -- tune
end allpoints
end YM.PolyDisc.Revival
