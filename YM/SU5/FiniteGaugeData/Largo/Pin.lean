import YM.SU5.FiniteGaugeData.Largo.Wave
/-! Crumbs, abstract complex pole assembly with compact reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Metric Finset Set
open scoped Topology BigOperators Pointwise
section
variable {X:Type*}(p:X→ℂ)(f:X→ℂ→ℂ)
structure Bank : Prop where
 apart : ∀ r:ℝ, {i:X| ‖p i‖ ≤ r}.Finite
 ticket : ∀ r:ℝ,∃ g:X→ℝ,(∀ i,0≤g i) ∧ Summable g ∧ ∀ (i:X)(z:ℂ), ‖z‖ ≤ r → ‖f i z‖ ≤ g i
 entire (i:X):Differentiable ℂ (f i)
variable (B:Bank p f)
def acre (z:ℂ):ℂ:= ∑' i, f i z / (z-p i)
open scoped Classical
namespace Bank
variable {p f}
lemma level (B:Bank p f)(z:ℂ): {i | p i=z}.Finite:= (B.apart ‖z‖).subset fun i h=>by simp only [Set.mem_setOf_eq, (show p i=z from h), le_refl]
def stash (z:ℂ): Finset X:= (B.level z).toFinset
lemma store (z:ℂ)(i:X) : i∈ B.stash z ↔ p i=z:=by simp [stash]
lemma remote (z:ℂ): ∃ e:ℝ, 0<e ∧ ∀ w, dist w z < e → ∀ i:X,i∉B.stash z→ e ≤ ‖w-p i‖:=by
 let T:={i:X| ‖p i‖ ≤ ‖z‖+2}; let s:= (B.apart (‖z‖+2)).toFinset \ B.stash z; have he: ∀ᶠ e:ℝ in 𝓝 0, ∀ i∈ s,2*e ≤ ‖z-p i‖:=(eventually_all_finset s).mpr (fun i h=> (show Continuous (fun e:ℝ=> (2:ℝ)*e) from by fun_prop).continuousAt (x:=0) |>.eventually (ge_mem_nhds (by dsimp only; rw [mul_zero]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (mt (B.store z i).2 (mem_sdiff.mp h).2))))))
 obtain ⟨e,⟨hv,t⟩,h⟩:= ((Filter.Eventually.filter_mono nhdsWithin_le_nhds (he.and (ge_mem_nhds zero_lt_one))).and (self_mem_nhdsWithin (a:=0) (s:=Ioi (0:ℝ)))).exists
 refine ⟨e,h,fun w g i Q=> ?_⟩; rw [dist_comm,dist_eq_norm] at g; by_cases u:i∈ s; · specialize hv i u; have h:=norm_sub_le_norm_sub_add_norm_sub z w (p i); linarith
 have he:‖z‖+2<‖p i‖:=lt_of_not_ge (fun h=> u (mem_sdiff.mpr ⟨(B.apart _).mem_toFinset.2 h,Q⟩)); have hp:‖p i‖-‖z‖ ≤ ‖z-p i‖:= (norm_sub_rev z _).symm ▸ norm_sub_norm_le ..; linarith only [hp,he,norm_sub_le_norm_sub_add_norm_sub z w (p i),g,t]
variable (z:ℂ)
lemma floorMe {A: Set X}(p':A=(B.stash z:Set X)):∀ᶠ w in 𝓝 z, ∀ i∉A, p i ≠w:=by obtain ⟨e,t,h⟩:= B.remote z; exact (Metric.eventually_nhds_iff.mpr ⟨e,t,fun w u i v g=>(sub_ne_zero.mpr (by intro r; have hv:=h w u i ((by rwa [p'] at v)); rw [r,sub_self,norm_zero] at hv; linarith) : w-p i≠0) (sub_eq_zero.mpr g.symm)⟩)
include B
lemma openGate : IsOpen (Set.range p)ᶜ:=isOpen_iff_mem_nhds.mpr fun x h=> (B.floorMe x rfl).mono (fun i hi z=>by obtain ⟨i',e⟩:= z; exact hi i' (fun g=>h ⟨i',(B.store ..).1 g⟩) e)
theorem analyticL : ∃ r:ℝ,0<r∧
    (∀ (w:ℂ),dist w z < r→ Summable (fun i => ‖f i w / (w-p i)‖)) ∧ ∃ G:ℂ→ℂ,
      DifferentiableOn ℂ G (ball z r) ∧ ∀ (w:ℂ), dist w z < r → acre p f w=G w+(∑ i∈B.stash z, f i w)/(w-z):=by
 classical
 obtain ⟨e,t,h⟩:=B.remote z; obtain ⟨g,h₀,hg,H⟩:=B.ticket (‖z‖+e); let A:= B.stash z; let W (i:X)(u:ℂ):= f i u/(u-p i); let F(i:X)(u:ℂ):= if i∈ A then 0 else W i u
 have hp(i:X): DifferentiableOn ℂ (F i) (ball z e):=by
    by_cases p:i∈A; · unfold F; simp only [if_pos p]; exact differentiableOn_const _
    unfold F; simp only [if_neg p]; exact (B.entire i).differentiableOn.div (by fun_prop) (fun i' t'=> norm_pos_iff.mp (t.trans_le (h i' (mem_ball.mp t') i p)))
 have hB(i:X)(w:ℂ)(u:dist w z < e) : ‖F i w‖ ≤ g i * e⁻¹ := by
    unfold F; split; · rw [norm_zero]; exact mul_nonneg (h₀ _) (by positivity)
    rename_i g; unfold W; rw [norm_div,←div_eq_mul_inv]; apply div_le_div₀ (h₀ i) _ t (h _ u _ g); rw [dist_eq_norm] at u; exact H _ w (by linarith [norm_sub_norm_le w z])
 have hs(w)(u:dist w z < e) : Summable fun i => ‖F i w‖:= Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=> hB i w u) (hg.mul_right _)
 have he(w:ℂ) (u:dist w z< e) : Summable fun i=> ‖W i w‖:= (hs w u).congr_cofinite (A.eventually_cofinite_notMem.mono fun i u=> by simp only [F,if_neg u]) -- method?
 refine ⟨e,t,he,fun w=> ∑' i,F i w, Complex.differentiableOn_tsum_of_summable_norm (hg.mul_right _) hp isOpen_ball hB, fun w u=>?_⟩
 let Y (i:X):= W i w-F i w; have hz:(∑' i,Y i)= (∑ i∈B.stash z, f i w)/(w-z):= by
    rw [tsum_eq_sum (s:=A) (by intro i p; simp [Y,F,p]), Finset.sum_div]; refine sum_congr rfl fun i v=>?_ ; simp only [Y,F,A,if_pos v,sub_zero,W, show p i=z from (B.store ..).1 v]
 unfold Y at hz; rw [Summable.tsum_sub (he w u|>.of_norm) ((hs w u).of_norm)] at hz; exact sub_eq_iff_eq_add'.mp hz
lemma smoothOff (h:z∉Set.range p): DifferentiableAt ℂ (acre p f) z:= by
 obtain ⟨e,t,v,G,hg,H⟩:= B.analyticL z; refine (hg.differentiableAt (ball_mem_nhds _ t)).congr_of_eventuallyEq ((Eventually.mono (p:=fun w => w∈ball z e) (ball_mem_nhds z t)) fun w u=>?_); exact (H _ u).trans (by simp [show B.stash z=∅ from eq_empty_iff_forall_notMem.mpr fun i u=> h ⟨i,(B.store ..).1 u⟩])
lemma localOrder : Tendsto (fun w=> (w-z)*acre p f w) (𝓝[≠] z) (𝓝 (∑ i∈B.stash z, f i z)):=by
 obtain ⟨e,t,v,G,g,H⟩:= B.analyticL z; let h:= ball_mem_nhds z t; have he(w:ℂ):Continuous (fun w:ℂ=> ∑ i∈ B.stash z, f i w):= continuous_finsetSum _ fun i _=> (B.entire i).continuous; refine Tendsto.congr' ?_ ((show Tendsto (fun w=> (w-z)*G w+(∑ i∈ B.stash z, f i w)) (𝓝 z) (𝓝 (∑ i∈B.stash z,f i z)) from ?_).mono_left nhdsWithin_le_nhds)
 · filter_upwards [self_mem_nhdsWithin (s:={z}ᶜ) (a:=z),mem_nhdsWithin_of_mem_nhds h] with w a u; rw [H _ u,mul_add,mul_div_cancel₀ _ (sub_ne_zero.mpr (show w≠z from a))] -- w-z multiplies numerator, cancellation direction
 have he: ContinuousAt (fun w => (w-z)*G w + ∑ i∈B.stash z,f i w) z:= ((((continuous_id.sub continuous_const).continuousAt (x:=z)).mul (g.differentiableAt h).continuousAt) |>.add ((he z).continuousAt)); simpa using! he.tendsto
end Bank
end
end YM.CF.Window.Largo
