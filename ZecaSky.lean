import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology


variable {c z:ℂ}{R:ℝ} {f:ℂ→ℂ}
lemma shadow_ball (r:0<R)
    (h:DifferentiableOn ℂ f (ball c R))
    (p:∀ z ∈ ball c R,‖f z‖≤1):
 ‖deriv f c‖ ≤ 2/R ∧
   ∀ z∈ball c R,‖f z-f c-(z-c)•deriv f c‖≤4*(‖z-c‖/R)^2:=by
 have u: c∈ball c R:=mem_ball_self r
 have j:∀ z∈ball c R,dist (f z) (f c) ≤2:=
    fun z e=> (dist_le_norm_add_norm _ _).trans ((add_le_add (p z e) (p c u)).trans_eq (by norm_num))
 have b:=Complex.norm_deriv_le_div_of_mapsTo_ball h
                (fun z w=>show f z∈closedBall (f c) 2 from j z w) r
 refine ⟨b,?_⟩
 let g(v:ℂ):=f v-f c-(v-c)•deriv f c
 have g0:g c=0:=by simp [g]
 have e:DifferentiableOn ℂ g (ball c R):=by
    exact (h.sub_const _).sub ((differentiable_id.sub_const c).differentiableOn.smul
             (differentiableOn_const _))
 have t:MapsTo g (ball c R) (closedBall (g c) 4):=by
    rw [g0]
    intro z v
    rw [mem_closedBall,dist_zero_right]
    refine (norm_sub_le _ _).trans ((add_le_add (show ‖f z-f c‖≤2 from (dist_eq_norm (f z) (f c)) ▸ j z v)
        (show ‖(z-c)•deriv f c‖≤2 from ?_)).trans_eq (by norm_num))

    have z0:= (Metric.mem_ball.mp v).le
    rw [dist_eq_norm] at z0
    rw [norm_smul]
    exact (mul_le_mul z0 b (norm_nonneg _) r.le).trans_eq (by field_simp)
 intro z v
 have m:=(h.differentiableAt (Metric.isOpen_ball.mem_nhds u)).hasDerivAt.isLittleO
 have m1:(fun z=>g z-g c) =o[𝓝 c] (fun z=>‖z-c‖^1):=by
    simp_rw [g0,sub_zero,pow_one]
    exact m.norm_right
 have a:=Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO e t m1 v
 rw [g0,dist_zero_right,dist_eq_norm] at a
 exact a

structure Str (s:Set ℂ) where
  f:ℂ→ℂ
  paid:∀z, ‖f z‖≤1
  enters:DifferentiableOn ℂ f s

instance {s:Set ℂ}: TopologicalSpace (Str s):=⊥
instance {s:Set ℂ}: DiscreteTopology (Str s):=⟨rfl⟩
open BoundedContinuousFunction
abbrev Cost (s:Set ℂ) := Str s →ᵇ ℂ
def ev (s:Set ℂ)(z:ℂ):Cost s:=
 ofNormedAddCommGroup (fun f:Str s=>f.f z) (continuous_of_discreteTopology)
     1 (fun f=>f.paid _)
lemma ev_here (s:Set ℂ)(z:ℂ)(h:Str s):ev s z h=h.f z:=rfl
-- ^α totalizes 0 outside, asks paid everywhere but holomorphic only within open s
lemma ev_magic {s:Set ℂ}(p: IsOpen s) : AnalyticOnNhd ℂ (ev s) s:=by
 suffices h:DifferentiableOn ℂ (ev s) s from h.analyticOnNhd p
 intro w e
 obtain ⟨r,R,v⟩:=Metric.isOpen_iff.mp p w e
 have a(f:Str s): ‖deriv f.f w‖ ≤ 2/r ∧
   ∀ z∈ball w r,‖f.f z-f.f w-(z-w)•deriv f.f w‖≤4*(‖z-w‖/r)^2:=
     shadow_ball R (f.enters.mono v) fun _ _=>f.paid _
 let d:= ofNormedAddCommGroup (fun f:Str s=>deriv f.f w) (continuous_of_discreteTopology)
     (2/r) (fun f=>(a f).1)

 suffices HasDerivAt (ev s) d w from this.differentiableAt.differentiableWithinAt
 rw [hasDerivAt_iff_isLittleO,isLittleO_iff]
 intro c hc
 have h:Tendsto (fun z:ℂ=> 4/r^2 * ‖z-w‖) (𝓝 w) (𝓝 0):=by
    simpa using ((tendsto_id (α:=ℂ) (x:=𝓝 w)).sub_const w).norm.const_mul (4/r^2)
 filter_upwards [h.eventually (ge_mem_nhds hc),ball_mem_nhds w R] with z u t
 refine le_trans ?_ (mul_le_mul_of_nonneg_right (show 4/r^2 * ‖z-w‖≤c from u) (norm_nonneg _))
 rw [show 4/r^2 * ‖z-w‖ * ‖z-w‖=4*(‖z-w‖/r)^2 from by ring]
 exact (BoundedContinuousFunction.norm_le (by positivity)).mpr fun f=> (a f).2 z t
#print axioms ev_magic
