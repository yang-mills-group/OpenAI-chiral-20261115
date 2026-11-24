import YM.CF.BProof.Wick.Thrill
import YM.CF.BProof.Wick.Dict

/-! Actual integration of Wick increments with no argument choices in scalar log. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {p q:ℝ}{f g:ℝ→ℂ}
lemma ode (h:p≤q)(t:ContinuousOn g (Set.Icc p q))(v:∀ x∈Set.Icc p q,HasDerivAt f (g x*f x) x): f q=Complex.exp (∫ x in p..q,g x)*f p:=by
 let ρ(x:ℝ):=max p (min q x); let H:=g ∘ ρ; have hρ(x): ρ x ∈ Set.Icc p q:=⟨le_max_left ..,max_le h (min_le_left ..)⟩; have hp:Continuous H:=continuousOn_univ.mp (t.comp (f:=ρ) (show Continuous ρ from continuous_const.max (continuous_const.min continuous_id)).continuousOn (fun i _=>hρ i)); have he(x)(h:x∈Set.uIcc p q): H x=g x:=by
    rw [Set.uIcc_of_le ‹p≤q›] at h; unfold H ρ; simp only [Function.comp_apply,min_eq_right h.2,max_eq_right h.1] -- tune scope ; inside
 let z(x:ℝ):= ∫ y in p..x,H y; have hz(x): HasDerivAt z (H x) x:=intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable ..) hp.stronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt -- tune
 let A(x:ℝ):=f x*Complex.exp (-z x); have hg(x)(h:x∈Set.uIcc p q): HasDerivAt A 0 x:=by apply (((v x (by rwa [Set.uIcc_of_le ‹p≤q›] at h)).mul ((hz x).neg.cexp)).congr_deriv); rw [he _ h]; ring
 have ht:A q=A p:= by have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=p) (b:=q) (f:=A) (f':=fun _=>0) hg (by simp); rw [intervalIntegral.integral_zero] at he; exact sub_eq_zero.mp he.symm; -- tune
 have hr:z p=0:=intervalIntegral.integral_same; have hx:z q= ∫ x in p..q,g x:=intervalIntegral.integral_congr (fun i v=> he i v); unfold A at ht; rw [hr,neg_zero,Complex.exp_zero,mul_one,hx,Complex.exp_neg,←div_eq_mul_inv] at ht; rw [(div_eq_iff (Complex.exp_ne_zero _)).1 ht, mul_comm]
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{g v:ℝ→ Wave I}{P Z B:Op I}{X:Wave I}{e:ℝ}
-- shears
abbrev salary (A M C:Op I) := costQ A 0 0 C M true false
abbrev bonus (A M C: Op I):= (1/2:ℂ) • costQ A 0 0 C (star M) false false
def poses (A P L:ℝ→ Op I)(p q:ℝ):= ∫ t in p..q,(salary (P t) (L t) (A t)).trace
def hose (A:Op I)(V L:ℝ→Op I)(p q:ℝ):= ∫ t in p..q,(bonus A (L t) (V t)).trace
-- use regular derivatives. prove continuity of increment from ContinuousOn bra,H etc and relation to norm; or supply as assumption and later from price.
lemma coast (h:p≤q)(P G:ℝ→Op I)(r:ℝ)(F:Op I)(g:∀ t∈Set.Icc p q, Shelf (P t) F r)(s:∀ t∈Set.Icc p q, Task (P t) (v t))(t:∀ t∈Set.Icc p q,HasDerivAt v (acts (dg (G t)) (v t)) t)(L:ContinuousOn (fun t=>(salary (P t) (G t) F).trace) (Set.Icc p q)):
    overlap F (v q)=Complex.exp (poses (fun _=>F) P G p q)*overlap F (v p):=by
 apply ode (f:=fun x=> overlap F (v x)) h L; intro x e; let E:=dg (G x); have hu:HasDerivAt (fun x=> overlap F (v x)) (inner ℂ (pairWave F) (acts E (v x))) x:= by have hu:= ((hasDerivAt_const x (pairWave F)).inner (𝕜:=ℂ) (t x e)); rw [inner_zero_left,add_zero] at hu; exact hu
 rw [show (salary (P x) (G x) F).trace=normal (v x) (pairWave F) E from (dgTest (g x e) (s x e) _).symm, overlap, ← sample_paid (x:=(v x)) ((g x e).bills (s x e)) E] -- tune
 exact hu
lemma pairCoast (h:p≤q)(H Y:ℝ→Op I)(s:Task P X)(g:∀ t∈Set.Icc p q, Shelf P (H t) e)(r:∀ t∈Set.Icc p q,HasDerivAt H (Y t) t)(b:ContinuousOn (fun t=> (bonus P (Y t) (H t)).trace) (Set.Icc p q)):
    overlap (H q) X=Complex.exp (hose P H Y p q)* overlap (H p) X:=by
 apply ode (f:=fun x=> overlap (H x) X) h b; intro x u; let W:=star (coupl (Y x)); have he:= ((turn (r x u)).inner (𝕜:=ℂ) (hasDerivAt_const x X)); simp only [inner_zero_right,zero_add] at he; rw [← show star W=coupl (Y x) from star_star _,act_inner] at he; rw [show (bonus P (Y x) (H x)).trace=normal X (pairWave (H x)) W from (pairTest (g x u) s _).symm, overlap, ← sample_paid ((g x u).bills s) W]; exact he
end YM.CF.BProof.Wick
