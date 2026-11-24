import YM.SU5.Selected.Actress.Support
/-! Determination of continuation on reservoir of upper-half-plane gaps from time-only
Euclidean samples. Not assuming joint spectral support. One-ray argument. Later use with
real history-proved heat orbit measures and multi-height exact samplings. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open Function Filter Real Set Complex Analysis Boundary Probe OS.Semigroup MeasureTheory Measure
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
variable {d:Type*}[Fintype d]
def waist(d: Type*) : Set (d→ℂ):= {x |∀ i:d, (x i)∈ Paley.loft} -- `Set` rewrite
noncomputable def ivory(d: Type*) : Set (d→ℂ):= {x|∀ i:d, x i∈Paley.high}
private abbrev knot := (waist d)
private lemma mayWalk : waist d⊆ ivory d:= fun i t x=> Paley.subset (t x)
private lemma openV : IsOpen (waist d):= by
 let F(i:d):Set (d→ℂ):= (fun v=> v i)⁻¹' Paley.loft; have he : waist d = ⋂ i:d,F i:=Set.ext fun i=> (by change (∀ j:d, i∈ F j) ↔ _; rw [Set.mem_iInter]); rw [he]; exact isOpen_iInter_of_finite (fun i=> Paley.open_loft.preimage (continuous_apply i))
private def clear(i:d→ℂ)(z:ℂ) : d→ℂ:= (fun j=> (↑(i j).im:ℂ)*I+z*(↑(i j).re:ℂ))
private lemma clears (i:d→ℂ)(j:d)(x:ℂ): (clear i x j).im = (i j).im+x.im*(i j).re:= by simp [clear]
private lemma clear_s (i:d→ℂ)(u:ℝ)(j:d): clear i (↑u*I) j= (↑((i j).im+u*(i j).re):ℂ)*I:=by unfold clear; push_cast; ring
private lemma clear_c (i:d→ℂ)(x:ℂ) : AnalyticAt ℂ (clear i) x:= by
 -- show vector affine CLM
 let f : d→ℂ:= fun j=> ↑(i j).im*I; let g : d→ℂ:= fun j=> ↑(i j).re; change AnalyticAt ℂ (fun z:ℂ=> f+z • g) x; exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
local notation "Λ" => waist d
private lemma naturally(i:d→ℂ)(p:i∈ waist d) (v:ℝ): clear i (↑v:ℂ)∈ waist d:= by intro j; change 0 < (clear ..).im; rw [clears]; simpa using (show 0 < (i j).im from p j) -- metavar
private lemma chain(i:d→ℂ)(p:i∈ waist d) : Convex ℝ (clear i⁻¹' waist d):=by
 intro u t v w a b p' q z j; change 0 < (clear i (a • u+b • v) j).im; specialize t j; specialize w j; change 0<(clear i u j).im at t; change 0<(clear i v j).im at w; rw [clears] at *; push_cast; simp only [Complex.add_im,Complex.smul_im,smul_eq_mul]; by_cases k:a=0; · subst a; simp only [zero_add] at z; subst b; simpa using w
 nlinarith only [congrArg (· * (i j).im) z|>.le,congrArg (· * (i j).im) z|>.ge,mul_pos (lt_of_le_of_ne p' (Ne.symm k)) t, mul_nonneg q w.le]
variable (F G:(d→ℂ)→ℂ)
noncomputable def imaginary (i:d→ℝ≥0) : d→ℂ:= fun j=> ((↑(i j):ℝ):ℂ)*I
lemma waist_img (i:d→ℝ≥0): imaginary i∈ ivory d:=by intro j; change 0 ≤ ( ( (↑(i j):ℝ):ℂ)*I).im; simp
private lemma tend_i : Tendsto (fun x:ℝ=>(x:ℂ)*I) (𝓝[>] 0) (𝓝[≠] 0):=by refine tendsto_nhdsWithin_iff.mpr ⟨Continuous.tendsto' (by fun_prop) (0:ℝ) 0 (by simp)|>.mono_left nhdsWithin_le_nhds,?_⟩; filter_upwards [self_mem_nhdsWithin] with i h; change _*I ≠ 0; exact mul_ne_zero (by exact_mod_cast (mem_Ioi.mp h).ne') I_ne_zero -- tune
private lemma winds(i:d→ℂ)(h:i∈Λ)(f:AnalyticOnNhd ℂ F Λ)(g:AnalyticOnNhd ℂ G Λ)(p:∀x:d→ℝ≥0, F (imaginary x)=G (imaginary x)): F i=G i:=by
 let L:=clear i ⁻¹' (waist d); let k:=clear i; have hz:(0:ℂ)∈ L:= naturally i h 0 -- tune args
 have hf:EqOn (F∘k) (G∘k) L:=by
    apply (show AnalyticOnNhd ℂ (F ∘ k) L from fun z h=>(f _ (show k z∈ waist d from h)).comp (clear_c i z)).eqOn_of_preconnected_of_frequently_eq (f:=F∘ k) (show AnalyticOnNhd ℂ (G ∘ k) L from fun z h=>(g _ (show k z∈ waist d from h)).comp (clear_c i z)) (chain i h).isPreconnected hz
    intro u; have hN: ∀ᶠ z in 𝓝 (0:ℂ), z∈ L:= (openV.preimage (continuous_iff_continuousAt.mpr fun x=> (clear_c i x).continuousAt)).mem_nhds hz; obtain ⟨x,g,h'⟩:= (tend_i.eventually (u.and (hN.filter_mono nhdsWithin_le_nhds))).exists
    apply g; have hv : ∀ j:d,0≤ (k ((x:ℂ)*I) j).im := fun j=> (show (0:ℝ) < (k ((x:ℂ)*I) j).im from h' j).le; let z(j:d):ℝ≥0:=⟨_,hv j⟩; have he: imaginary z=k (↑x*I):=by funext j; change ( ((k ((x:ℂ)*I) j).im):ℂ)*I=_; unfold k; rw [clear_s]; simp -- both sides
    change F (k _) = G (k _); rw [←he]; exact p z
 have he:k 1=i:=funext fun j=> by unfold k clear; rw [one_mul, add_comm]; exact Complex.re_add_im _
 exact he ▸ (hf (show (1:ℂ)∈ L from naturally i h 1)) -- defeq via k
noncomputable def incline (t:ℝ)(x:d→ℂ):d→ℂ:=fun i=> x i+ (t:ℂ)*I
lemma tropical (f:ContinuousOn F (ivory d))(g:ContinuousOn G (ivory d))(w:AnalyticOnNhd ℂ F (waist d))(x:AnalyticOnNhd ℂ G (waist d))(p:∀ i:d→ℝ≥0,F (imaginary i)= G (imaginary i)) : EqOn F G (ivory d):= by
 intro t ht; let D(i:ℝ):= incline i t; have hz(v:ℝ)(u:0<v): incline v t∈ waist d:=by intro i; specialize ht i; change 0 < (incline ..).im; unfold incline; change 0 ≤ (t i).im at ht; simp; linarith
 have he:Tendsto D (𝓝[>] 0) (𝓝[ivory d] t):=by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Continuous.tendsto' (by unfold D incline; apply continuous_pi; intro i; fun_prop) 0 t ?_).mono_left nhdsWithin_le_nhds,?_⟩ -- cast h
    · ext i; simp [D,incline]
    exact Eventually.mono self_mem_nhdsWithin (fun i h=> mayWalk (hz i h))
 exact tendsto_nhds_unique_of_eventuallyEq ((f t ht).tendsto.comp he) ((g t ht).tendsto.comp he) (Eventually.mono self_mem_nhdsWithin fun i h=> winds F G _ (hz i h) w x p)
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms tropical
