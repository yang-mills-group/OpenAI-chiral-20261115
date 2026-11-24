import YM.CF.BPress.Homes.East
import YM.CF.BPress.Pf.Log
/-!
 Supplement B-phase. Borel test on the whole pricing domain using geometric (gapped) restrictions. No path-space projection hypotheses needed.
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 550000
namespace YM.CF.BPress.Homes
open Function NormedSpace Metric Finset Lattice Fock Spin Pf Thera Cellar Cellar.Pass Spin.Trans Set MeasureTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I X:Type}[LinearOrder I][Fintype I][Nonempty I][TopologicalSpace X]
variable {A C B P Q L:X→Op I}{r ε:ℝ}{F G:X→ℝ→Op I}
lemma fixed (s:Prop) : IsClosed {_x:X|s}:= by by_cases t:s <;> simp [t]
lemma star_f (p:Continuous A) : IsClosed {x|IsStarProjection (A x)}:=by
 rw [show {x|IsStarProjection (A x)}={x|A x*A x=A x∧star (A x)=A x} by
      ext x; exact ⟨fun h=>⟨h.1.eq,h.2⟩,fun h=>⟨h.1,h.2⟩⟩, setOf_and]
 exact (isClosed_eq (p.mul p) p).inter (isClosed_eq p.star p)
lemma pass_f (p:Continuous A)(v:Continuous P)(h:Continuous Q)(_l:Continuous L)(g:∀ x,Empties (P x) (Q x) (L x)) (ε:ℝ): IsClosed {x| Pass (P x) (Q x) (L x) (A x) ε}:=by
 simp_rw [show ∀ x, Pass _ _ _ (A x) ε↔ _ from (fun x=> (show Pass (P x) (Q x) (L x) (A x) ε ↔ IsStarProjection (A x)∧0<ε ∧ ε≤1∧ ε • P x≤P x*A x*P x∧ε • Q x≤Q x*(1-A x)*Q x from ⟨fun h=>⟨h.a,h.pos,h.small,h.payP,h.payQ⟩, fun ⟨a,p,s,t,b⟩=>⟨g x,a,p,s,t,b⟩⟩)), setOf_and]
 exact (star_f p).inter ((fixed _).inter ((fixed _).inter ((isClosed_le (v.const_smul ε) ((v.mul p).mul v)).inter (isClosed_le (h.const_smul ε) ((h.mul (continuous_const.sub p)).mul h)))))
lemma unit_p(p:Continuous A): IsClosed {x| A x∈ unitary (Op I)}:= (isClosed_eq (p.star.mul p) continuous_const).inter (isClosed_eq (p.mul p.star) continuous_const)
lemma bore_p(p:Continuous P)(c:Continuous A)(r:ℝ): IsClosed {x|Bore (P x) (A x) r}:=by
 simp_rw [show ∀ (A C:Op I), Bore A C r↔ IsStarProjection A ∧ C∈unitary (Op I) ∧ Cᵀ = -C∧ ‖Pf.toll A C‖≤r∧ r<1 from fun i x=> ⟨fun h=>⟨h.p,h.unit,h.sk,h.low,h.hi⟩, fun ⟨p,c,r,v,q⟩=>⟨p,c,r,v,q⟩⟩,setOf_and]
 have he : Continuous fun x=> Pf.toll (P x) (A x) := ((continuous_const.sub p).mul c).mul (show Continuous (fun x=>cc (P x)) from p.star.matrix_transpose)
 exact (star_f p).inter ((unit_p c).inter ((isClosed_eq c.matrix_transpose c.neg).inter ((isClosed_le he.norm continuous_const).inter (fixed _))))

lemma beam_p (p:Continuous P)(c:Continuous C)(h:∀ x, IsUnit (Trans.gram (P x) (C x))): Continuous (fun x=> Trans.beam (P x) (C x)):=by
 have he : Continuous (fun x=>Trans.gram (P x) (C x)):= (c.star.mul c).add (continuous_const.sub p)
 exact Continuous.mul c ((continuous_iff_continuousAt.mpr (fun x=>ContinuousAt.comp (g:=fun c:Op I=>c⁻¹) (InvC_cont (h x)) he.continuousAt)).mul c.star)
lemma tilt_f (p:Continuous P)(c:Continuous A)(h:∀ x, IsStarProjection (P x))(v:∀ x,TagG (P x) (A x)) (t:ℝ): Continuous (fun x=>tilt (P x) (A x) t):= beam_p p (p.add (c.const_smul t)) (fun x=> (tiltR (h x) (v x) t).live_G)
lemma smooth_f (p: Continuous P)(q: Continuous Q)(r: Continuous L)(s:Continuous A)(v:∀ x,Pass (P x) (Q x) (L x) (A x) ε)(t:ℝ)(h:‖t‖≤1) : Continuous (fun x=> smoothP (P x) (Q x) (L x) (A x) t):=by
 let f(x):=rent1 (P x) (A x); have ht:Continuous f:= beam_p p (s.mul p) (fun x=>(v x).gate1.live_G)
 have hb:Continuous (fun x=>slide (P x) (Q x) (L x) (A x) t):=by
    unfold slide coeff0 coeff1 rent0
    exact (((p.add (r.const_smul t)).add (q.const_smul (t^2))).mul ht).add ((r.add (q.const_smul t)).mul (s.sub ht))
 exact beam_p s hb (fun x=>(Pass.enjoy (v x) t h).live_G)
end YM.CF.BPress.Homes
