import YM.CF.Jet.Tall
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice Lat Broc Branch
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I T D E Y G:Type} [Fintype I][DecidableEq I][Fintype Y][DecidableEq Y][TopologicalSpace T][CompactSpace T][T2Space T][SecondCountableTopology T][MeasurableSpace T][BorelSpace T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ]
variable [TopologicalSpace D]{A:D→Plan I μ}{b: Light Y D G}{S:Seal Y→Finset I}{Q:Draw D}{Q':Draw (Sam A)}{n:ℕ}{v c C K a:ℝ}(L:Lit A b S)
structure Inspired (Q:Draw D)(A:D→Plan I μ)(Q':Draw (Sam A))(K:ℝ)(n:ℕ):Prop where
 pos:0≤K
 fire : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E],∀ (V:Set E),IsOpen V→∀ (f:E→D),Q.test E V f→FireK V (A ∘ f) K n
 tested: ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E],∀ (V W:Set E),W⊆V→IsOpen V→IsOpen W→∀ (f:E→D),Q.test E V f→∀ F:E→Sam A,∀ t:I→T,(∀ x∈W,(F x).val=(f x,t))→ Q'.test E W F
lemma bigger (n s:ℕ)(hc:0≤c)(hK:0≤K): c ≤ mercury s n K c:=by
  unfold mercury; apply le_trans _ (le_mul_of_one_le_right _ _)
  · apply le_trans _ (le_mul_of_one_le_left (by positivity) ?_); exact le_add_of_nonneg_right (by positivity); apply one_le_mul_of_one_le_of_one_le; exact_mod_cast n.factorial_pos; exact Real.one_le_exp (by positivity)
  · positivity
  exact one_le_pow₀ (by simp)
lemma flash_mean [LocallyCompactSpace D][FirstCountableTopology D] {f:Sam A→ℂ} (H:Inspired Q A Q' K n) (R:Seal Y)(h:Flash L.botL Q' n R f c) (g:∀ x,Bank (A x) (S R))(l:∀ x y,b.rel R x y→∀ z,sails (A x) (S R) z=sails (A y) (S R) z)(r:∀ T x,b.rel T x x):Flash b Q n R (means A f) (mercury (S R).card n K c):=by
 classical
 have he:=bigger n (S R).card h.pos H.pos
 refine ⟨⟨h.pos.trans he,fun k=>h.travel (fun l=>k (by simp [l,mercury])),L.box h.toPeak,fun x=>(means_val A _ _ L.phase h.cont h.sumline x).trans he,fun x y u=>L.inoc f h.reads c h.cont h.sumline x y u _ subset_rfl (g x) (g y) (l x y u),L.tide f h.toPeak⟩,?_⟩
 intro E _ _ _ V hv p P x hx
 let q:=A ∘ p; let F(t:E)(y:I→T):=sampler A f (p t,y)
 have hg:= H.fire E V hv p P
 apply waitB hg F (S R) (fun t _=>g _) _ h.pos _ _ x hx
 · intro y z u hp
   let W:= V∩{z:E|fall (q z) y≠0}; have hi:IsOpen W:= by
      rw [isOpen_iff_mem_nhds]; intro w hx; have hq:w∈V∧fall (q w) y≠0:=hx; exact inter_mem (hv.mem_nhds hq.1) (((fire_num hg hq.1 Finset.univ y).continuousAt).eventually_ne hq.2)
   let Z(t:E): Sam A:= if h:t∈W then ⟨(p t,y), (show _ ∧ fall (q t) y≠0 from h).2⟩ else ⟨(p z,y),hp⟩
   have he(t:E)(hx:t∈W):(Z t).val=(p t,y):=by unfold Z; rw [dif_pos hx]
   have hr:=h.plot E W hi Z (H.tested E V W Set.inter_subset_left hv hi p P Z y he) z ⟨u,hp⟩; apply hr.germ
   filter_upwards [hi.mem_nhds (show z∈W from ⟨u,hp⟩)] with i t; unfold F; rw [← he i t]; exact (sampler_p f (Z i).val (Z i).property).symm
 · intro x _ t u d p' w; unfold F; rw [sampler_p f (p x,t) d,sampler_p f (p x,u) p']; exact h.reads _ _ ⟨r R _,w⟩
 intro z _; exact (cream_gift A f c L.phase h.cont h.sumline).weighted.comp (show Continuous (fun y:I→T =>(p z,y)) from continuous_const.prodMk continuous_id)

lemma stash (K:ℝ)(h:0 ≤ K)(n:ℕ)(ha:0<a) :∃ Y:ℝ,0≤Y∧∀ c:ℝ,0≤c →∀ x y:ℕ, y≤x → Real.exp (a/2*x)*mercury y n K c ≤ Y*(Real.exp (a*x)*c):=by
  let s:= (n:ℝ)+1; have hs: 0<s:=by unfold s; positivity
  let t:=a/(2*s); have ht:0<t:=by unfold t; positivity
  let w:=max 1 t⁻¹; have hw: 1≤w:= le_max_left ..
  refine ⟨(n.factorial:ℝ)* Real.exp (n*K)*s*w^n,by have hg:0<w:=zero_lt_one.trans_le hw; positivity,fun c hc x y hy=>?_⟩
  have he: (1+y:ℝ)^n ≤ w^n*Real.exp (a/2*x):=by
    calc
     _ ≤ (w*(1+t*x))^n:=by
        gcongr ?_ ^ n; calc
           (1+y:ℝ) ≤ w+ (x:ℝ):=add_le_add hw (by exact_mod_cast hy)
           _ ≤ _:= by
             rw [mul_add,mul_one,←mul_assoc]; apply add_le_add_right; apply le_mul_of_one_le_left (by positivity); have H:=mul_le_mul_of_nonneg_right (le_max_right 1 t⁻¹) ht.le; rwa [inv_mul_cancel₀ ht.ne'] at H
     _ ≤ (w*Real.exp (t*x))^n := by
         have h:0<w:= by linarith
         gcongr; linarith [Real.add_one_le_exp (t*x)]
     _ ≤ _:=by
       have hp: 0<w:= by linarith
       rw [mul_pow,←Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_le_exp.mpr; unfold t s; field_simp; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hD: (1+n:ℝ)*c=c+n*c:= by ring
  unfold mercury; rw [←hD]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)); unfold s
  rw [show a*(x:ℝ)= a/2*x+a/2*x by ring,Real.exp_add]; ring_nf; rfl
lemma Screen.reserve {q v:ℝ}(p:a≥q)(e:v≤c){f:D→ℂ}(l:Screen b Q n f a v): Screen b Q n f q c:=by
 obtain ⟨F,G,l,r,L⟩:=l; exact ⟨F,G,l,fun i=>(sum_le_sum (fun j _=> mul_le_mul_of_nonneg_right (rent_up p j) (l j).pos)).trans ((r i).trans e), L⟩
variable {V:ℝ}
lemma screen_mean [LocallyCompactSpace D][FirstCountableTopology D]{F:Sam A→ℂ} (H:Inspired Q A Q' K n) (h:Screen L.botL Q' n F a V)(hG:∀ T,(S T).card≤ T.card)(k:∀ R x,Bank (A x) (S R))(e:∀ R x y,b.rel R x y→∀ z,sails (A x) (S R) z=sails (A y) (S R) z)(r:∀ T x,b.rel T x x)(hc:0≤ c)(w:∀ R: Seal Y,∀ f:ℝ,0≤ f → rent (a/2) R*mercury (S R).card n K f ≤ c*(rent a R*f)):Screen b Q n (means A F) (a/2) (c*V):=by
 obtain ⟨P,C,u,Y',hu⟩:=h; refine ⟨_,_,fun R=> flash_mean L H R (u R) (k R) (e R) r,?_,?_⟩
 · intro i; unfold hitE; exact (sum_le_sum (fun z _=> w z _ (u z).pos)).trans (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (Y' _) hc)
 intro x
 unfold means; rw [← integral_finsetSum]
 · apply integral_congr_ae; apply Eventually.of_forall; intro y; unfold cream; by_cases ht:fall (A x) y≠0
   · simp_rw [sampler_p _ (x,y) ht]; rw [hu]; exact Finset.smul_sum ..
   rw [not_not] at ht; simp [ht]
 intro i _; exact net_compact ((cream_gift A (P i) (C i) L.phase (u i).cont (u i).sumline).weighted.comp (show Continuous (fun y:I→_ =>(x,y)) from continuous_const.prodMk continuous_id))
end YM.CF.Jet
