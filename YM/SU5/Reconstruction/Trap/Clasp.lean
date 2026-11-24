import YM.SU5.Reconstruction.Trap.SOT
/-!
# The comparison graph; abstract analyt. Does NOT assume there's a polar decomposition, prove.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp
variable {K H D:Hilbert} {X Y:Type*}
/-- One trap to compare. -/
structure Clasp (K H D:Hilbert) where
 l : K →L[ℂ] H
 r : K →L[ℂ] D
 j : Injective l
 k : Injective r
 p : DenseRange l
 q : DenseRange r
 frame : l.adjoint.comp l + r.adjoint.comp r= (1:K.Op)
namespace Clasp
variable (C : Clasp K H D)
lemma calculation (x:K) : C.l.adjoint (C.l x) + C.r.adjoint (C.r x) = x:= DFunLike.congr_fun C.frame _
def Latch (x:H) (y:D):Prop := ∃ z:K, C.l z=x∧ C.r z=y
def Pass (u:H.Op) (v:D.Op):Prop:= ∀ x : K,C.Latch (u (C.l x)) (v (C.r x))
-- dual test for equality. pairing arrows via graph normed test.
lemma latch_self (x:K): C.Latch (C.l x) (C.r x):=⟨x,rfl,rfl⟩
lemma latch_dual (x:H ) (y:D) : C.Latch x y ↔ C.l (C.l.adjoint x+C.r.adjoint y)=x ∧ C.r (C.l.adjoint x+C.r.adjoint y)=y:= by
 constructor
 · rintro ⟨w,rfl,rfl⟩; rw [C.calculation]; exact ⟨rfl,rfl⟩
 intro h; exact ⟨_,h⟩
lemma pass_criterion (a:H.Op ) (b:D.Op ) (h:∀ (x:K), C.Latch (a (C.l x)) (b (C.r x))) : C.Pass a b:=h
noncomputable def bring (u:H.Op) (v:D.Op):K.Op:= (C.l.adjoint).comp (u.comp C.l)+(C.r.adjoint).comp (v.comp C.r)
lemma sustain (u:H.Op ) (v:D.Op): C.Pass u v ↔ C.l.comp (C.bring u v)=u.comp C.l ∧ C.r.comp (C.bring u v)=v.comp C.r := by
 refine ⟨fun p=> ⟨ContinuousLinearMap.ext (fun x=> (latch_dual ..|>.1 (p x)).1),ContinuousLinearMap.ext (fun x=> (latch_dual .. |>.1 (p x)).2)⟩,fun p x=>⟨C.bring u v x,DFunLike.congr_fun p.1 x,DFunLike.congr_fun p.2 x⟩⟩
theorem latch_limit {ι:Type*}(l:Filter ι)[l.NeBot]{x y}{U:ι→H} {V:ι→D}(p:Tendsto U l (𝓝 x) ) (q:Tendsto V l (𝓝 y) ) (v:∀ᶠ i in l,C.Latch (U i) (V i)): C.Latch x y:= by
  have he := ((C.l.adjoint.continuous.tendsto _).comp p).add ((C.r.adjoint.continuous.tendsto _).comp q)
  exact latch_dual ..|>.2 ⟨tendsto_nhds_unique_of_eventuallyEq ((C.l.continuous.tendsto _).comp he) p (v.mono fun i h=> (latch_dual ..|>.1 h).1),tendsto_nhds_unique_of_eventuallyEq ((C.r.continuous.tendsto _).comp he) q (v.mono fun i h=> (latch_dual .. |>.1 h).2)⟩
lemma passLimit {ι:Type*}(l:Filter ι)[l.NeBot]{a:H.Op}{b:D.Op}{u:ι→H.Op}{v:ι→D.Op}(p:∀ x,Tendsto (fun i=> u i x) l (𝓝 (a x)) ) (q:∀ x,Tendsto (fun i=> v i x) l (𝓝 (b x)) ) (e:∀ᶠ i in l,C.Pass (u i) (v i)): C.Pass a b:= fun x=> latch_limit C l (p (C.l x)) (q (C.r x)) (e.mono (fun i t=> t x)) -- tune type
lemma one: C.Pass 1 1:= C.latch_self
lemma tape (a:H.Op ) (b:D.Op ) (p:C.Pass a b ) (u:H ) (v:D ) (t:C.Latch u v): C.Latch (a u) (b v):=by obtain ⟨x,rfl,rfl⟩:=t; exact p x
variable {C}
lemma Pass.scale {a b}(p:Pass C a b ) (z:ℂ) : Pass C (z • a) (z • b):=by
 intro x; obtain ⟨w,u,v⟩:=p x; exact ⟨z • w, by rw [map_smul,u]; rfl,by rw [map_smul,v]; rfl⟩
lemma Pass.sub {a b c d}(p: Pass C a b ) (q:Pass C c d): Pass C (a-c ) (b-d):=by
 intro x; obtain ⟨w,u,v⟩:=p x; obtain ⟨z,f,g⟩:=q x; exact ⟨w-z, by rw [map_sub,u,f]; rfl,by rw [map_sub,v,g]; rfl⟩
lemma Pass.add {a b c d}(p: Pass C a b ) (q:Pass C c d): Pass C (a+c ) (b+d):=by
 intro x; obtain ⟨w,u,v⟩:=p x; obtain ⟨z,f,g⟩:=q x; exact ⟨w+z, by rw [map_add,u,f]; rfl,by rw [map_add,v,g]; rfl⟩
lemma Pass.times {a b c d}(p: Pass C a b ) (q:Pass C c d): Pass C (a*c ) (b*d):= fun x => tape C a b p _ _ (q x)
variable (C)
lemma passIntegral [MeasurableSpace X]{μ:Measure X}{a:X→H.Op}{b:X→D.Op}(p:Integrable a μ ) (q:Integrable b μ ) (h:∀ᵐ x ∂μ, C.Pass (a x ) (b x)): C.Pass (∫ x, a x∂μ) (∫ x, b x∂μ):= by
 let U := ∫ x, a x ∂ μ; let V:= ∫ x, b x ∂ μ
 intro x
 let W := ContinuousLinearMap.apply ℂ H (C.l x); let T := ContinuousLinearMap.apply ℂ D (C.r x)
 let l := (C.l.adjoint).comp W; let r:= (C.r.adjoint).comp T
 rw [latch_dual]; change C.l (l U + r V)=W U ∧ C.r (l U + r V)=T V
 constructor
 · have he : ∫ y, (C.l.comp l) (a y)+(C.l.comp r) (b y)∂ μ=∫ y, W (a y) ∂ μ:= by
     apply integral_congr_ae; filter_upwards [h] with y hy; have u := (latch_dual .. |>.1 (hy x)).1; rwa [map_add] at u
   rw [integral_add ((C.l.comp l).integrable_comp p) ((C.l.comp r).integrable_comp q), ContinuousLinearMap.integral_comp_comm _ p,ContinuousLinearMap.integral_comp_comm _ q, W.integral_comp_comm p] at he
   rw [map_add]; exact he
 have he : ∫ y, (C.r.comp l) (a y)+(C.r.comp r) (b y)∂ μ=∫ y, T (b y) ∂ μ:= by
     apply integral_congr_ae; filter_upwards [h] with y hy; have u := (latch_dual .. |>.1 (hy x)).2; rwa [map_add] at u
 rw [integral_add ((C.r.comp l).integrable_comp p) ((C.r.comp r).integrable_comp q), ContinuousLinearMap.integral_comp_comm _ p,ContinuousLinearMap.integral_comp_comm _ q, T.integral_comp_comm q] at he
 rw [map_add]; exact he
variable (F:ℂ→H.Op) (J:ℂ→ D.Op)
lemma holPass {A:Set ℂ}(u:IsPreconnected A ) (p:AnalyticOnNhd ℂ F A ) (q:AnalyticOnNhd ℂ J A ) (a:ℂ ) (ha:a∈A ) (f:∃ᶠ z in 𝓝[≠] a,C.Pass (F z ) (J z) ) (z:ℂ ) (t:z∈A) : C.Pass (F z ) (J z):= by
 intro x
 rw [latch_dual]; let M:= ContinuousLinearMap.apply ℂ H (C.l x); let N:= ContinuousLinearMap.apply ℂ D (C.r x)
 let l:= C.l.adjoint; let r:= C.r.adjoint; let V(z:ℂ):= l (M (F z)) + r (N (J z))
 have ht: AnalyticOnNhd ℂ V A:= fun x h=> ((l.comp M).analyticAt (F x) |>.comp (p x h)).add ((r.comp N).analyticAt (J x) |>.comp (q x h))
 constructor
 · exact (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (f:=C.l ∘ V) (fun x h=> C.l.analyticAt _|>.comp (ht x h)) (g:=M ∘ F) (fun x h=> M.analyticAt _|>.comp (p x h)) u ha (f.mono fun z h=>(C.latch_dual .. |>.1 (h x)).1)) t
 exact (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (f:=C.r ∘ V) (g:=N ∘ J) (fun x h=> C.r.analyticAt _|>.comp (ht x h)) (fun x h=> N.analyticAt _|>.comp (q x h)) u ha (f.mono fun z h=>(C.latch_dual ..|>.1 (h x)).2)) t
section deriv
lemma derivPass {a:ℝ}(e:DifferentiableAt ℂ F (a:ℂ) ) (v:DifferentiableAt ℂ J (a:ℂ) ) (p:∀ᶠ b:ℝ in 𝓝[>] a,C.Pass (F b ) (J b)): C.Pass (deriv F (a:ℂ)) (deriv J (a:ℂ)) := by
 have pt:Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝[>] a) (𝓝[≠] (a:ℂ)):= tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds) (Eventually.mono self_mem_nhdsWithin (fun t h=> show (t:ℂ)≠ (a:ℂ) from by exact_mod_cast (mem_Ioi.mp h).ne'))
 -- need Pass at a too using continuity
 let he: C.Pass (F (a:ℂ)) (J (a:ℂ)):= passLimit C (𝓝[>] a) (fun x=> (ContinuousLinearMap.apply ℂ H x).continuous.tendsto _|>.comp (e.continuousAt.tendsto.comp (pt.mono_right nhdsWithin_le_nhds))) (fun x=> (ContinuousLinearMap.apply ℂ D x).continuous.tendsto _|>.comp (v.continuousAt.tendsto.comp (pt.mono_right nhdsWithin_le_nhds))) p
 refine passLimit C (𝓝[>] a) (u:=fun z=>slope F (a:ℂ) z) (v:=fun z=>slope J (a:ℂ) z) ?_ ?_ ?_
 · intro x; exact ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp ((e.hasDerivAt.tendsto_slope.comp pt))
 · intro x; exact ((ContinuousLinearMap.apply ℂ D x).continuous.tendsto _).comp ((v.hasDerivAt.tendsto_slope.comp pt))
 apply p.mono; intro z hz; simp only [slope, vsub_eq_sub]; exact (hz.sub he).scale _
end deriv
end Clasp
end YM.CrossedFrame
