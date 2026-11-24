import YM.SU5.Macro.Move
import YM.SU5.Macro.Across

/-!
# Necessary price of locality for one ordered kernel, already at positive heat

No joint cone spectral condition. Candidates needn't be the two Label observables! It's
a failing test even at just TWO-point weak locality for any reconstruction wishing to keep
these readings in the stated positive-time sense. Not a claim that EVERY interpretation of
physical smearing would keep that sense (e.g., doesn't ask for or test recovering these costs by
integrating a DIFFERENT field's kernels with additional heat offsets).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinMacro
open Function Set Filter Metric NormedSpace Bornology Complex
open OS.Semigroup Spectral Spectral.Alps
open scoped Topology InnerProductSpace NNReal ComplexOrder

variable {H : Hilbert} {j : Axis} (S : OS.Semigroup H j) (X Y : H)

/-- True value at the specified spatial translation and heat (width) gap.
Consistent with translating by `joinST` at the edge. -/
def kernel (u : OS.Cross j) (a : ℝ≥0) := inner ℂ X (S.U u (S.E a Y))
/-- True continuation on the upper half-plane (and its real boundary). Don't interpret
    the actual values of this function on the LOWER half-plane physically. -/
def carried (u : OS.Cross j) (z : ℂ) : ℂ := inner ℂ X (S.U u (balcony S z Y))
local notation "K" => kernel S X Y
local notation "F" => carried S X Y
variable (u : OS.Cross j)

/-- Pure imaginary upward. -/
def rise (t : ℝ≥0) : ℂ := (↑(t:ℝ):ℂ)*I
@[simp] lemma rise_im (t : ℝ≥0) : (rise t).im=t := by simp [rise]

lemma carried_cost (z : ℂ) : ‖F u z‖≤ ‖X‖*‖Y‖ := by
  refine (norm_inner_le_norm (𝕜:=ℂ) ..).trans ?_
  rw [S.unitary]; exact mul_le_mul_of_nonneg_left (((balcony S z).le_opNorm Y).trans
    (mul_le_of_le_one_left (norm_nonneg _) (balcony_pay ..))) (norm_nonneg _)
lemma carried_cont : Continuous (fun p : OS.Cross j × ℂ => F p.1 p.2) :=
  continuous_const.inner (S.cont_cross _ _ ((balcony_cont S Y).comp continuous_snd) continuous_fst)
lemma carried_holo : AnalyticOnNhd ℂ (F u) {z | 0 < z.im} := by
  let k : H.Op→L[ℂ] ℂ := (innerSL ℂ X).comp ((S.U u).comp (ContinuousLinearMap.apply ℂ H.space Y))
  intro z t; exact (k.analyticAt (balcony S z)).comp (balcony_holo S z t)
@[simp] lemma carried_rise (a : ℝ≥0) : F u (rise a)= K u a := by
  unfold carried kernel rise; rw [balcony_high]
lemma carried_edge (a : ℝ) : F u a = inner ℂ X (S.unit.translation (joinST u a) Y) := by
  rw [motion_apply,carried,balcony_floor]; rfl
lemma carried_down : AnalyticOnNhd ℂ (fun z:ℂ=> F (-u) (-z)) {z| z.im < 0} := by
  intro z hz; apply AnalyticAt.comp (𝕜:=ℂ) (carried_holo S X Y (-u) (-z) ?_)
    (show AnalyticAt ℂ (fun x:ℂ=>-x) z from analyticAt_id.neg); simpa using (show z.im<0 from hz)
lemma carried_only_time : Continuous (F u) :=
  (carried_cont S X Y).comp (continuous_const.prodMk continuous_id)
lemma kernel_cont_space (v : ℝ≥0) : Continuous (fun u => kernel S X Y u v) :=
  continuous_const.inner (S.continuousU (S.E v Y))

/-- Interior heat is real analytic. Useful even referring to other-chart time
    (no common rotation premise). -/
lemma real_analytic_shift (b : ℝ) : AnalyticOnNhd ℝ
    (fun r:ℝ=> kernel S X Y u (Real.toNNReal (r+b))) (Set.Ioi (-b)) := by
  let k(x:ℝ) := (↑(x+b):ℂ)*I
  intro r h
  have hk {x:ℝ} (p : x∈ Set.Ioi (-b)) : 0 < (k x).im := by unfold k; simp; change -b < x at p; linarith
  have he : AnalyticAt ℝ k r := ((Complex.ofRealCLM.analyticAt _).comp
    (show AnalyticAt ℝ (fun r:ℝ=>r+b) r from analyticAt_id.add analyticAt_const)).mul analyticAt_const
  apply (((carried_holo S X Y u _ (hk h)).restrictScalars).comp he).congr
  filter_upwards [isOpen_Ioi.mem_nhds h] with x p
  rw [Function.comp_apply, ←carried_rise]; unfold k rise
  rw [Real.coe_toNNReal]; change -b < x at p; linarith

/-- A dense price observation in any open testing interval. -/
lemma analytic_price {g:ℝ→ℂ} {a p q : ℝ} {s : Set ℝ} (w:a<0)
    (hs : Dense s) (h : AnalyticOnNhd ℝ g (Ioi a)) (e : g 0 ≠ 0)
    (i : a ≤ p) (v : p < q) : ∃ x∈ Ioo p q ∩ s, g x≠0 := by
  have sub : Ioo p q ⊆ Ioi a := fun x hx => lt_of_le_of_lt i hx.1
  by_contra! l
  have ht : EqOn g (fun _=>0) (Ioo p q ∩ s) := l
  obtain ⟨x,hx,hx'⟩ := exists_between v
  have hp : x ∈ Ioo p q := ⟨hx,hx'⟩
  have hd := ht.of_subset_closure (h.continuousOn.mono sub) continuousOn_const inter_subset_left
    (hs.open_subset_closure_inter isOpen_Ioo)
  exact e (h.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_Ioi
    (sub hp) (hd.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hp)) w)

/-- Finite analytic time allowance somewhere in the vacuum vector. -/
def HasPadding := ∃ (r : ℝ≥0), 0 < r ∧ ∃ x : H, X=S.E r x

variable (p : HasPadding S Y)
include p
lemma extends_kernel : ∃ r : ℝ, r < 0 ∧ ∃ f : ℂ→ℂ,
    AnalyticOnNhd ℂ f {z:ℂ| r < z.im} ∧ IsBounded (range f) ∧ EqOn (F u) f {z:ℂ|0 ≤ z.im} := by
  obtain ⟨r,h,x,e⟩ := p
  let g := carried S X x u
  let Φ(z:ℂ) := z+rise r
  refine ⟨-(r:ℝ),neg_lt_zero.mpr h, g ∘ Φ,fun z s=>?_, ?_, fun z t=>?_⟩
  · apply AnalyticAt.comp (𝕜:=ℂ) (carried_holo S X x u (Φ z) ?_) (show AnalyticAt ℂ Φ z from analyticAt_id.add analyticAt_const)
    change 0 < (z+rise r).im; rw [add_im,rise_im]; linarith only [show -(r:ℝ)<z.im from s]
  · rw [isBounded_iff_forall_norm_le]; exact ⟨_,by rintro z ⟨w,rfl⟩; exact carried_cost S X x u _⟩
  have hi : (r:ℝ)= (rise r).im := (rise_im r).symm
  unfold Function.comp g Φ carried; rw [basis_cost S z (rise r) t (hi ▸ NNReal.zero_le_coe),rise,balcony_high]; exact congrArg (fun Y:H=> inner ℂ X (S.U u (balcony S z Y))) e

variable {a b : ℝ} (g : S.orth Y=0) {Δ : ℝ≥0} (q : kernel S X Y u Δ ≠ 0) (h : a < b)
include g q h
/-- One-sided further extension already means spacelike locality would be
     impossible at any open time interval for this pair (given this nonzero price). -/
lemma refuses_lower {f : ℂ → ℂ} (s : AnalyticOnNhd ℂ f {z| z.im < 0})
    (c : ContinuousOn f {z| z.im ≤ 0}) (t : IsBounded (f '' {z:ℂ| z.im < 0})) :
    ¬ ∀ x∈ Ioo a b, F u (x:ℂ)=f x := by
  intro e
  obtain ⟨r,r₀,f',j,v,e'⟩:= extends_kernel S X Y u p
  obtain ⟨z,v,_⟩:= Glue.rigid_of_edge h r₀ j s c (v.subset (image_subset_range _ _)) t
    (fun i χ=> (e' (show 0 ≤ (i:ℂ).im by simp)).symm.trans (e i χ))
  have eq (b:ℝ≥0) : K u b=z:= by
    have he : 0 ≤ (rise b).im := by rw [rise_im]; exact NNReal.zero_le_coe
    exact (carried_rise S X Y u b).symm.trans ((e' he).trans (v (lt_of_lt_of_le r₀ he)))
  have hi : Tendsto (fun v:ℝ≥0=> kernel S X Y u v) atTop (𝓝 0):= by
    change Tendsto (⇑((innerSL ℂ X).comp (S.U u)) ∘ (fun t=> S.E t Y)) atTop _
    simpa only [g,map_zero] using
      ( ((innerSL ℂ X).comp (S.U u)).continuous.continuousAt.tendsto.comp (S.emerges Y))
  exact q ((eq Δ).trans (tendsto_nhds_unique ((tendsto_const_nhds (x:=z) (f:=atTop)).congr (fun v=>(eq v).symm)) hi))

/-- The native swap (of candidate operators with these very vacuum vectors)
    fails even without assumptions on the adjoint vacuum vectors. -/
lemma edge_refusal (X' Y' : H) :
    ∃ t∈ Ioo a b, ¬ swap S.unit (joinST u t) X X' Y Y' := by
  by_contra! d
  let f (z:ℂ) := carried S Y' X' (-u) (-z)
  apply refuses_lower S X Y u p g q h (f:=f) (carried_down S Y' X' u)
    ((carried_only_time S Y' X' (-u) |>.comp continuous_neg).continuousOn)
  · rw [isBounded_iff_forall_norm_le]; exact ⟨_,by rintro z ⟨w,_,rfl⟩; exact carried_cost S Y' X' (-u) _⟩
  intro v t; specialize d v t; unfold f; rw [← ofReal_neg,carried_edge,carried_edge,← neg_joinST]; exact d

omit p g q h
variable {H' : Hilbert} (S' : OS.Semigroup H' j) (A B : H')
/-- Enough for identification in this question. (Can also use positive moments of heat powers.) -/
def accord : Prop := ∃ r:ℝ≥0, 0<r ∧ ∃ᶠ t in 𝓝[≠] r, kernel S' A B u t = K u t
lemma coincides (m : accord S X Y u S' A B) : EqOn (carried S' A B u) (F u) {z|0 ≤ z.im} := by
  obtain ⟨r,p,t⟩:=m
  have he : Tendsto rise (𝓝[≠] r) (𝓝[≠] rise r):=by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have c : Continuous rise := by unfold rise; fun_prop
      exact c.continuousWithinAt
    filter_upwards [self_mem_nhdsWithin] with v hv
    intro e; have eu : rise v=rise r:= e
    apply hv; exact Subtype.ext ((rise_im v).symm.trans ((congrArg Complex.im eu).trans (rise_im r)))
  have ht:= (carried_holo S' A B u).eqOn_of_preconnected_of_frequently_eq (carried_holo S X Y u)
    (convex_halfSpace_im_gt 0).isPreconnected (show 0 < (rise r).im by rw [rise_im]; exact p) (he.frequently (by simpa only [carried_rise] using t))
  rw [← closure_setOf_lt_im]; exact ht.closure (carried_only_time ..) (carried_only_time ..)
include p g q h
/-- More robust no-go: take *any* assignment retaining this pair's positive-time
heat readings in a (possibly new!) positive-energy system. Ordered matching in the
sense of `accord`, on this one translation test, already detects the error. -/
lemma edge_any (m : accord S X Y u S' A B) (A' B' : H') :
    ∃ t∈ Ioo a b, ¬ swap S'.unit (joinST u t) A A' B B' := by
  by_contra! d
  let f (z:ℂ) := carried S' B' A' (-u) (-z)
  apply refuses_lower S X Y u p g q h (f:=f) (carried_down S' B' A' u)
    ((carried_only_time S' B' A' (-u) |>.comp continuous_neg).continuousOn)
  · rw [isBounded_iff_forall_norm_le]; exact ⟨_,by rintro z ⟨w,_,rfl⟩; exact carried_cost S' B' A' (-u) _⟩
  intro v t
  rw [← coincides S X Y u S' A B m (show 0≤(v:ℂ).im by simp)]
  specialize d v t; unfold f; rw [← ofReal_neg,carried_edge,carried_edge,← neg_joinST]; exact d
end YM.SatinMacro

#print axioms YM.SatinMacro.edge_refusal
#print axioms YM.SatinMacro.edge_any
