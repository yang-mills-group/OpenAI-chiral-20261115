import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! Transfer local regularity and pointwise derivative bounds through a finite-order cone.
 The `k`th secant cone here has arbitrary real multiples and up to `2^k` terms.
 A bound on it transfers to the closed cone. Taking a derivative spends just one
 order of secant cone; projected derivative fields still satisfy *operator norm* control.
 This allows local stencil proofs of C^k estimates without differentiating their coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Set Function Filter Topology Metric
section
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
def combos (s:Set E): ℕ→Set E
 | 0 => {x| ∃ y∈s, ∃ r:ℝ,x=r • y}
 | n+1=> Set.image2 (·+·) (combos s n) (combos s n)
private abbrev com (s:Set E) (k:ℕ):= closure (combos s k)
variable {k:ℕ} {s t:Set E}
namespace combos
lemma cons {x} (h:x∈s) : x∈combos s 0:= ⟨x,h,1,(one_smul _ _).symm⟩
lemma mul (r:ℝ) : MapsTo (r • ·) (combos s k) (combos s k) := by
 intro x hx; induction k generalizing x with
 | zero=> obtain ⟨y,hy,t,rfl⟩:=hx; exact ⟨y,hy,r*t,smul_smul r t _⟩
 | succ n ih=> obtain ⟨x,h,y,p,rfl⟩:= hx; exact ⟨r•x,ih h,r•y,ih p,(smul_add r x y).symm⟩
lemma add {x y : E} (h : x ∈ combos s k) (h':y ∈ combos s k) : x+y∈combos s (k+1):= Set.mem_image2_of_mem h h'
lemma deepen : combos s k ⊆ combos s (k+1):=fun x hx=>by simpa using add hx (mul 0 hx)
private lemma comb_le {n m:ℕ} (p:n≤m): com s n ⊆ com s m:= closure_mono ((monotone_nat_of_le_succ (f:=combos s) (fun _=> deepen (s:=s))) p)
private lemma lift {x:E} (h:x∈s): x∈com s k:= comb_le (Nat.zero_le k) (subset_closure (cons h))
private lemma plus {x y : E} (h : x ∈ com s k) (h':y ∈ com s k) : x+y∈com s (k+1):= map_mem_closure₂ continuous_add h h' (fun _ ha _ hb=> add ha hb)
private lemma times (r:ℝ) : MapsTo (r •·) (com s k) (com s k):= (mul r).closure (continuous_const_smul r)
private lemma sub {x y:E} (h:x ∈ com s k) (p:y∈com s k) : x-y∈com s (k+1):= by simpa [sub_eq_add_neg] using plus h (times (-1) p)
private lemma lift_map {t:Set F} (L:E→L[ℝ] F) {k m:ℕ} (h: MapsTo L s (com t m)) : MapsTo L (com s k) (com t (m+k)):= by
 have V:MapsTo L (combos s k) (com t (m+k)):=by
   intro x hx; induction k generalizing x with
   | zero=> obtain ⟨x,hx,r,rfl⟩:=hx; rw [map_smul]; exact times r (h hx)
   | succ n ih=> obtain ⟨x,h,y,p,rfl⟩:=hx; rw [map_add]; exact plus (ih h) (ih p)
 simpa [com] using V.closure L.continuous
end combos

variable {C:ℝ} {f:E→F} {g:E→G} {x:E}
def Blocks (C:ℝ) (k:ℕ) (s:Set E) (f:E→F) (g:E→G) : Prop := ∀ p ∈ com ((fun x=>(f x,g x)) '' s) k, ‖p.1‖ ≤ C * ‖p.2‖
namespace Blocks
local notation "Γ" n => com ((fun x=>(f x,g x)) '' s) n
lemma from_raw (h: ∀ p∈combos ((fun x=>(f x,g x)) '' s) k, ‖p.1‖ ≤ C * ‖p.2‖) : Blocks C k s f g:=
 fun p hx=> (closure_minimal h (isClosed_le (continuous_fst.norm) (continuous_snd.norm.const_mul C))) hx
lemma bound (h : Blocks C k s f g) (p:x∈s) : ‖f x‖ ≤ C*‖g x‖:= h _ (combos.lift (mem_image_of_mem _ p))
lemma mono (h:Blocks C k s f g){m:ℕ}(e:m≤k):Blocks C m s f g:= fun _ p=>h _ (combos.comb_le e p)
lemma ct (h:Blocks C (k+1) s f g) (hp:0<C) (v:ContinuousOn g s) : ContinuousOn f s := by
 intro x hx; refine Metric.tendsto_nhds.mpr fun ε he=>?_
 filter_upwards [Metric.tendsto_nhds.mp (v x hx) (ε/C) (by positivity), self_mem_nhdsWithin] with y hy hy'
 rw [dist_eq_norm] at hy ⊢; exact lt_of_le_of_lt (h _ (combos.sub (combos.lift (mem_image_of_mem _ hy')) (combos.lift (mem_image_of_mem _ hx)))) (mul_comm C _ ▸ ((lt_div_iff₀ hp).mp hy))
variable [CompleteSpace F] [CompleteSpace G]
private lemma line (h:Blocks C 2 s f g) (hp:0<C) (hx:s∈𝓝 x) {L:E→L[ℝ] G} (hg:HasFDerivAt g L x) (v:E) : ∃ y:F, (y,L v)∈Γ 1 := by
 let u (r:ℝ):=x+r•v; let A(r:ℝ):= (f (u r),g (u r)); let Fp (r:ℝ):= slope (f∘u) 0 r; let Gp(r:ℝ):=slope (g∘u) 0 r; let l:= 𝓝[≠](0:ℝ)
 have T:l.NeBot:=by dsimp [l]; infer_instance
 have V:∀ᶠ r in l,(Fp r,Gp r)∈Γ 1:= by
   have H:Tendsto u l (𝓝 x):= by
     apply tendsto_nhdsWithin_of_tendsto_nhds; have : ContinuousAt u 0:=by unfold u; fun_prop
     simpa [ContinuousAt,u] using this
   filter_upwards [H.eventually hx] with r hr; convert combos.times r⁻¹ (combos.sub (k:=0) (combos.lift (mem_image_of_mem _ hr)) (combos.lift (mem_image_of_mem _ (mem_of_mem_nhds hx)))) <;> simp [Fp,Gp,u,slope_def_module]
 have H:HasDerivAt u v 0:= by simpa [u] using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add x
 have Y:Tendsto Gp l (𝓝 (L v)) := (((show u 0=x by simp [u]) ▸ (show HasFDerivAt g L x from hg) : HasFDerivAt g L (u 0)).comp_hasDerivAt 0 H).tendsto_slope
 obtain ⟨p,h'⟩:∃ x, Tendsto Fp l (𝓝 x):= by
   refine cauchy_map_iff_exists_tendsto.mp (cauchy_map_iff'.2 ?_); refine uniformity_basis_dist.tendsto_right_iff.mpr fun ε he=>?_
   have e:= uniformity_basis_dist.tendsto_right_iff.mp (cauchy_map_iff'.1 (cauchy_map_iff_exists_tendsto.mpr ⟨_,Y⟩)) (i:=ε/C) (by positivity)
   filter_upwards [tendsto_fst.eventually V,tendsto_snd.eventually V,e] with x ha hb hy; change dist (Fp _) (Fp _) < ε; change dist (Gp _) (Gp _) < ε/C at hy; rw [dist_eq_norm] at hy ⊢; exact lt_of_le_of_lt (h _ (combos.sub ha hb)) (mul_comm C _ ▸ ((lt_div_iff₀ hp).mp hy))
 exact ⟨p,isClosed_closure.mem_of_tendsto (h'.prodMk_nhds Y) V⟩
private lemma dF (h:Blocks C 3 s f g) (hp:0<C) (hx:s∈𝓝 x) {L:E→L[ℝ] G} (hg:HasFDerivAt g L x) : ∃ T:E→L[ℝ] F,HasFDerivAt f T x ∧ ∀ v:E,(T v,L v)∈Γ 1:= by
 choose p H using fun v=>(h.mono (by decide)).line hp hx hg v
 have uniq (a b:F)(c:G) (P:(a,c)∈Γ 2)(Q:(b,c)∈Γ 2):a=b:= by have z:=h _ (combos.sub P Q); exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using z))
 let V:E→ₗ[ℝ] F:=
   {toFun:=p
    map_add':=fun x y=> uniq _ _ (L (x+y)) (combos.comb_le (by decide) (H _)) (by rw [map_add]; exact combos.plus (H x) (H y))
    map_smul':=fun r x=> uniq _ _ (L (r•x)) (combos.comb_le (by decide) (H _)) (by rw [map_smul]; exact combos.comb_le (by decide : 1≤2) (combos.times r (H x))) }
 let T:= V.mkContinuous (C*‖L‖) (fun x => calc
     _ ≤ C*‖L x‖:=(h.mono (by decide)) _ (H x)
     _ ≤ (C*‖L‖)*‖x‖:= by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (L.le_opNorm _) hp.le)
 refine ⟨T,?_,H⟩; rw [hasFDerivAt_iff_tendsto] at hg ⊢
 refine squeeze_zero' (Eventually.of_forall fun _=>by positivity) (?_) (show Tendsto (fun y=> C*(‖y-x‖⁻¹*‖g y-g x-L (y-x)‖)) _ _ from by simpa using hg.const_mul C)
 filter_upwards [hx] with y hy; rw [mul_left_comm C]; refine mul_le_mul_of_nonneg_left (?_) (by positivity); exact h _ (combos.comb_le (by decide : 2≤3) (combos.sub (combos.sub (combos.lift (k:=0) (mem_image_of_mem _ hy)) (combos.lift (mem_image_of_mem _ (mem_of_mem_nhds hx)))) (H (y-x))))
private lemma d (h:Blocks C (k+3) s f g) (hp:0<C) (hs:IsOpen s) (e:DifferentiableOn ℝ g s) : DifferentiableOn ℝ f s ∧ Blocks C (k+2) s (fderiv ℝ f) (fderiv ℝ g) := by
 have V (x)(hx:x∈s):DifferentiableAt ℝ f x ∧ ∀ v:E, (fderiv ℝ f x v,fderiv ℝ g x v)∈Γ 1:= by
   obtain ⟨T,H,Q⟩:= (h.mono (by omega)).dF hp (hs.mem_nhds hx) (e.differentiableAt (hs.mem_nhds hx)).hasFDerivAt; rw [H.fderiv]; exact ⟨H.differentiableAt,Q⟩
 refine ⟨fun x hx=>(V x hx).1.differentiableWithinAt,?_⟩; intro p P; refine p.1.opNorm_le_bound (by positivity) fun v=>?_
 let L:= (ContinuousLinearMap.apply ℝ F v).prodMap (ContinuousLinearMap.apply ℝ G v)
 have H:L p ∈ Γ (1+(k+2)):= combos.lift_map L (fun x hx=>by obtain ⟨x, hx', rfl⟩:=hx; exact (V x hx').2 v) P
 refine (show ‖p.1 v‖ ≤ C*‖p.2 v‖ from h _ (combos.comb_le (by omega) H)).trans ?_; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (p.2.le_opNorm v) hp.le

/-- Local derivative payment at all orders up to the budgeted order; does not involve the dimension. -/
theorem pay (h:Blocks C (k+2) s f g) (hp:0<C) (hs:IsOpen s) (e:ContDiffOn ℝ k g s) : ContDiffOn ℝ k f s ∧
    ∀ j:ℕ,j≤k→∀ x∈s, ‖iteratedFDeriv ℝ j f x‖ ≤ C * ‖iteratedFDeriv ℝ j g x‖:= by
 induction k generalizing F G with
 | zero=> simp only [Nat.cast_zero,contDiffOn_zero] at e ⊢; refine ⟨h.ct hp e,?_⟩; intro j p x hx; obtain rfl : j=0:=Nat.eq_zero_of_le_zero p; simpa [norm_iteratedFDeriv_zero] using h.bound hx
 | succ k ih=>
    rw [Nat.cast_add_one,contDiffOn_succ_iff_fderiv_of_isOpen hs] at e ⊢; obtain ⟨p,q⟩:=h.d hp hs e.1; obtain ⟨Q,H⟩:= ih q e.2.2; refine ⟨⟨p,by simp,Q⟩,?_⟩; rintro (_|j) hj x hx; simpa [norm_iteratedFDeriv_zero] using h.bound hx; rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv]; exact H _ (by omega) x hx
end Blocks
end
end YM.CF.VolumeRate
