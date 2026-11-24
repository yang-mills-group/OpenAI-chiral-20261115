import YM.SU5.Selected.Actress.Dahl
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open Function Filter Real Set Complex Analysis Boundary Probe OS.Semigroup
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a) (t:ℝ≥0)
variable {x:H}
lemma once (u:0<t) (p:S.E t x=x) : x∈ S.ground:=by
 let f(i:ℕ):= (i:ℝ≥0)*t; have ht(i:ℕ):S.E (f i) x=x:=by induction i with
    | zero=> unfold f; rw [Nat.cast_zero,zero_mul,S.eZero]; rfl
    | succ i h => rw [show f (i+1)=f i+t from (by unfold f; push_cast; ring),S.time,ContinuousLinearMap.comp_apply,p,h]
 have he : Tendsto f atTop atTop:= Tendsto.atTop_mul_const (by assumption : 0<t) tendsto_natCast_atTop_atTop  -- NNReal Semiring maybe lemma?
 have hh:S.orth x=x:= tendsto_nhds_unique ((S.emerges x).comp he) (tendsto_const_nhds.congr' (Eventually.of_forall (fun i=>(ht i).symm))) -- ht binder
 exact S.ground.starProjection_eq_self_iff.mp hh
lemma veto (A:H.Op)(v:x∈ S.ground)(u:0<t)(p:A x∉S.ground): ¬Commute (S.E t) A:=fun b=> p (once S t u ((show S.E t (A x)=A (S.E t x) from DFunLike.congr_fun b.eq x).trans (congrArg A ((S.fixed x).mp v t))))
-- endpoint correlation in actual real-time algebra from Clock.Cross.seam. base v at h. make phase-equiv proof strong;
def fare (Ω:H) (A B:H.Op)(t:ℝ):ℂ := inner ℂ Ω ((star A* conduct S t B) Ω)
lemma utc (Ω:H)(v:Ω∈ S.ground)(A B:H.Op)(x y:H)(h:A Ω=x)(w:B Ω=y)(p:ℝ):fare S Ω A B p=inner ℂ x (S.edge p y):=by
 change inner ℂ Ω (A.adjoint (conduct S p B Ω))= _; rw [occupied S Ω v,ContinuousLinearMap.adjoint_inner_right,h,w] -- check
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms once
#print axioms veto
#print axioms utc
