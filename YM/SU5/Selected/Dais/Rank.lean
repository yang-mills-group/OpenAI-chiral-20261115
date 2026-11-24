import YM.SU5.Selected.Dais.Blanc
import YM.SU5.Selected.Dais.Cocos
/-! Filtering taxes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dais.Parity
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace ComplexOrder ComplexConjugate
attribute [local instance] opCStarAlgebra
open CF.Pannier Chancel Rous
section
open Damask
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I] {P:Op I}{S:Finset I}{M W:Wave I}{A A':FC I}{t h v:ℝ}{n m:ℕ}
def Riser (n:ℕ)(A:FC I) := ∀ (P:Op I) (W:Wave I)(t:ℕ), Access P t W → Access P (n+t) (acts A W)
lemma Riser.mono(p:Riser n A)(v:n ≤ m): Riser m A:=fun P W t h=> (p P W t h).mono (by omega)
lemma token_spend (L:List (Token I)): Riser L.length (fo Damask.use L):=by
 intro P W t h; induction L with
 | nil=> simpa [Pannier.Chancel.fo,act_one] using h
 | cons x l p=> rw [List.length_cons,Nat.add_right_comm]; change Access P _ (acts (use x*_) W); rw [act_mul]; exact access_letter p ⟨x.val.1, x.val.2,rfl⟩
lemma Riser.letter (x:Chancel.Letter A): Riser 1 A:=fun P W m p=> add_comm m 1 ▸ access_letter p x
lemma Riser.add (p:Riser n A)(q:Riser n A'): Riser n (A+A'):= fun P W m h=> by rw [act_add]; exact (p _ _ _ h).add (q _ _ _ h)
lemma Riser.sub (p:Riser n A)(q:Riser n A'): Riser n (A-A'):= fun P W m h=> by rw [act_sub]; exact (p _ _ _ h).sub (q _ _ _ h)
lemma Riser.scale (p:Riser n A)(x:ℂ): Riser n (x • A):= fun P W m h=> by rw [act_smul]; exact (p P W m h).scale x
lemma Riser.mul (p:Riser n A)(q:Riser m A'):Riser (n+m) (A*A'):= fun P W k h=> by rw [act_mul,add_assoc]; exact p _ _ _ (q _ _ _ h)
lemma Riser.one : Riser n (1:FC I):= fun P W m h=>by rw [act_one]; exact h.mono (by omega)
-- Eq rotation with active Q? general on bra
lemma psych (p:IsStarProjection P)(e:0<t)(u:t≤1)(a:t⁻¹≤h)(P₀:Sea P W)(g:Riser n A): Yep h (acts (star A) M) W ((t⁻¹^n* ‖A‖)*‖driftW (cards P t) M‖):=by
 intro l; rw [act_inner]; let f:= fo Damask.use l; let x:=acts f W; let K:=driftW (cards P t) M; let Q:= ‖K‖; let L:=l.length; have hz : ‖acts A x‖ ≤ ‖A‖:= (Graph.spentS ..).trans ((mul_le_mul_of_nonneg_left (token_limit l P₀.2) (norm_nonneg _)).trans_eq (_root_.mul_one _)); apply (income (k:=n+(l.length+0)) (g P x (l.length+0) (token_spend l P W 0 (access_unit P₀))) p e u).trans
 calc _ ≤ Q*((t⁻¹^n * h^L)*‖A‖) := by rw [add_zero,pow_add]; have ht:0≤t⁻¹:=(inv_pos.mpr e).le; unfold Q L; have hy:0≤h:=ht.trans a; gcongr
      _ = _:=by unfold Q K costs; ring
-- pay universal t small (t chosen before h), physical no insertion plug.
end
variable {N:Side}{ΛΓ:ℕ}{S: Skye.Pane N} {q:Tulip.Male}{t:ℝ}
lemma powerR (p:IsStarProjection (spar ΛΓ q S))(e:0<t)(v:t≤1): ‖driftW (cards (spar ΛΓ q S) t) (mateK N)‖=Real.exp (Rous.logo t ΛΓ q S):=by
 let Q:= spar ΛΓ q S; let V:= ‖driftW (cards Q t) (mateK N)‖; let Z:= Rous.logo t ΛΓ q S; let T:= grip (tickA N) Q t
 have ht:0<T.det.re:= (Complex.lt_def.mp ((grip_lives (cut_t N) p e v).det_pos)).1; have hp:V^2=T.det.re:= price_wave t (cut_t N) p (mateK N) (tickB N); change V= Real.exp Z; apply pow_left_inj₀ (norm_nonneg (driftW _ _)) (Real.exp_pos _).le (show (2:ℕ)≠0 by norm_num) |>.mp; rw [hp,←Real.exp_nat_mul, show ↑(2:ℕ) * Z=Real.log T.det.re from ?_,Real.exp_log ht]; unfold Z logo; push_cast; ring -- tune
end YM.CF.Dais.Parity
#print axioms YM.CF.Dais.Parity.psych
#print axioms YM.CF.Dais.Parity.powerR
