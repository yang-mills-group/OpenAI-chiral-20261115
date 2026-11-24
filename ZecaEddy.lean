import ZecaSky
import ZecaOspreys
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open MeasureTheory Complex
def Inlet:Set ℂ:={z|0<Complex.re z}
lemma quay:IsOpen Inlet:=isOpen_lt continuous_const Complex.continuous_re

structure Seaward (A:ℕ→ℂ→ℂ) : Prop where
 enters : ∀n,DifferentiableOn ℂ (A n) Inlet
 cost : ∃(d:ℕ)(M:ℝ),0<M ∧ ∀ n, ∀z∈Inlet, ‖A n z‖≤M*spur d z.re
def atReef (A:ℕ→ℂ→ℂ)(K:ℂ→ℂ)(z:ℂ):Prop:=Tendsto (fun n=>A n z) atTop (𝓝 (K z))
structure Splash (A:ℕ→ℂ→ℂ)(K:ℂ→ℂ):Prop where
  analyticK: DifferentiableOn ℂ K Inlet
  keysweep: ∃a∈ Inlet,∃ᶠ x in 𝓝[≠] a, atReef A K x

open BoundedContinuousFunction
def Loop {s:Set ℂ} (f:ℕ→Str s):Submodule ℂ (Cost s) where
 carrier:={v| Tendsto (fun n=>v (f n)) atTop (𝓝 0)}
 zero_mem':= tendsto_const_nhds
 add_mem' {x y} u v:=by
    have p:Tendsto (fun n=>x (f n)+y (f n)) atTop (𝓝 (0+0)):= Tendsto.add u v
    rw [zero_add] at p
    exact p
 smul_mem' c x u:= by
    have p:Tendsto (fun n=>c*x (f n)) atTop (𝓝 (c*0)):= Tendsto.const_mul _ u
    rw [mul_zero] at p
    exact p
lemma loop_closed {s:Set ℂ}(f:ℕ→Str s):
 IsClosed ((Loop f):Set (Cost s)):=by
  refine isClosed_iff_frequently.mpr ?_
  intro v h
  change Tendsto (fun n=>v (f n)) atTop (𝓝 0)
  refine Metric.tendsto_nhds.mpr fun e p=>?_
  obtain ⟨u,t,d⟩:=(h.and_eventually (eventually_mem_nhds_iff.mpr (ball_mem_nhds v (half_pos p)))).exists
  change Tendsto (fun n=>u (f n)) atTop (𝓝 0) at t
  filter_upwards [Metric.tendsto_nhds.mp t (e/2) (half_pos p)] with n a
  have b:dist (v (f n)) (u (f n)) < e/2:=by
    have h' := norm_coe_le_norm (u-v) (f n)
    rw [dist_comm,dist_eq_norm]
    have hd:‖u-v‖<e/2:= (dist_eq_norm u v) ▸ (Metric.mem_ball.mp (mem_of_mem_nhds d))
    exact lt_of_le_of_lt h' hd
  exact (dist_triangle _ _ _).trans_lt
       ((add_lt_add b a).trans_eq (add_halves e))

lemma quay_magic {s:Set ℂ}(v: IsOpen s)(w:IsPreconnected s)
 (f:ℕ→Str s)
 (a:ℂ) (p:a∈s)
 (h:∃ᶠ x in 𝓝[≠] a,
    Tendsto (fun n=> (f n).f x) atTop (𝓝 0)):
 ∀x∈s,Tendsto (fun n=> (f n).f x) atTop (𝓝 0):=by
 haveI:=loop_closed f
 let q:=(Loop f).mkQL
 have y:= ((q.analyticOnNhd Set.univ).comp (ev_magic v) (mapsTo_univ ..)).eqOn_zero_of_preconnected_of_frequently_eq_zero w p
    (h.mono (fun _ t=> (Submodule.Quotient.mk_eq_zero (Loop f)).mpr t))
 exact fun _ t=>(Submodule.Quotient.mk_eq_zero (Loop f)).mp (y t)

lemma enters_all {A:ℕ→ℂ→ℂ}{K:ℂ→ℂ}
 (h: Seaward A)(p: Splash A K)
 (z:ℂ)(w:z∈Inlet): atReef A K z:=by
 obtain ⟨d,M,g,t⟩:=h.cost
 obtain ⟨a,b,c⟩:=p.keysweep
 change 0<z.re at w
 change 0<a.re at b
 obtain ⟨u,e,f⟩:=exists_between (lt_min b w)
 rcases lt_min_iff.mp f with ⟨r0,r1⟩
 let R:=max ‖a‖ ‖z‖+1
 let s:= ball (0:ℂ) R ∩ {y|u<y.re}
 let B:=closedBall (0:ℂ) R ∩ {y|u≤y.re}
 have i:IsOpen s:=isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
 have l :s ⊆ B:= inter_subset_inter ball_subset_closedBall (fun w k=>le_of_lt (show u<w.re from k))
 have k : B ⊆ Inlet:= fun _ j=>lt_of_lt_of_le e j.2
 have y:a∈s:= ⟨by simpa only [Metric.mem_ball, dist_zero_right] using (le_max_left ‖a‖ ‖z‖).trans_lt (lt_add_one _),r0⟩
 have y1:z∈s:= ⟨by simpa only [Metric.mem_ball, dist_zero_right] using (le_max_right ‖a‖ ‖z‖).trans_lt (lt_add_one _),r1⟩
 have eB:IsCompact B:= (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_re)
 obtain ⟨x,mx⟩:= eB.bddAbove_image (((p.analyticK.mono k).continuousOn).norm)
 let D:=|x|+M*spur d u
 have su:0<spur d u:=by unfold spur; positivity
 have D0:0<D:= add_pos_of_nonneg_of_pos (abs_nonneg _) (mul_pos g su)
 let fee(n)(w):=(A n w-K w)/(D:ℂ)
 have cc(n): ∀w∈s,‖fee n w‖≤1:=by
    intro v j
    have a1:= (t n v (k (l j)))
    have sp:spur d v.re ≤ spur d u := by
       unfold spur
       have r:u≤v.re:=(l j).2
       have := e.trans_le r
       gcongr
    have a2: ‖K v‖≤x:=mx ⟨v,l j,rfl⟩
    unfold fee; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg D0.le,div_le_one D0]
    have e1:= a1.trans (mul_le_mul_of_nonneg_left sp g.le)
    exact (norm_sub_le ..).trans ((le_of_eq (add_comm ..)).trans (add_le_add (a2.trans (le_abs_self x)) e1))
 have df(n):DifferentiableOn ℂ (fee n) s:= (((h.enters n).sub p.analyticK).mono (l.trans k)).div_const (D:ℂ)
 classical
 let J(n):Str s:= ⟨s.indicator (fee n),
      fun w=>by
         by_cases a:w∈s
         · rw [indicator_of_mem a]
           exact cc n w a
         rw [indicator_of_notMem a,norm_zero]
         exact zero_le_one, (df n).congr (fun w t=> indicator_of_mem t (fee n))⟩
 have ys:IsPreconnected s:=
   ((convex_ball ..).inter (convex_halfSpace_gt Complex.reCLM.isLinear u)).isPreconnected

 have h0(w)(p:w∈s)(n) : (J n).f w = (A n w-K w)/(D:ℂ):=Set.indicator_of_mem p (fee n)
 have e0: ∃ᶠ x in 𝓝[≠] a, Tendsto (fun n=> (J n).f x) atTop (𝓝 0):=by
    refine (c.and_eventually (nhdsWithin_le_nhds (i.mem_nhds y))).mono ?_
    rintro w ⟨(p: atReef A K w),e⟩
    have k: Tendsto (fun n=> A n w) atTop (𝓝 (K w)):=p
    simpa only [sub_self,zero_div] using (((k.sub_const (K w)).div_const (D:ℂ)).congr (f₂:=fun n=> (J n).f w) (fun n=>(h0 w e n).symm))
 have pay:= quay_magic i ys J a y e0 z y1
 have u: (D:ℂ)≠0:=by exact_mod_cast D0.ne'
 have ht: Tendsto (fun n=> A n z-K z) atTop (𝓝 0):=by
   have j:= pay.mul_const (D:ℂ)
   rw [zero_mul] at j
   exact j.congr (fun n=> by rw [h0 _ y1, div_mul_cancel₀ _ u])
 unfold atReef; simpa using ht.add_const (K z)
#print axioms enters_all
