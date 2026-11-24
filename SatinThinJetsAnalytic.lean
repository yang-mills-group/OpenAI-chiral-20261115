import SatinFixedContrastNovember4
import YM.Heat.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries
/-!
# An all-positive-time profile has analytic jets, in op norm at each positive time
-/
set_option autoImplicit false
set_option maxHeartbeats 260000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j) (Y : ℝ → H)
/-- Coherence at every **positive** time. Don't use `Y 0` anywhere. -/
def Positive : Prop := ∀ s t:ℝ, 0<s → s ≤ t → Y t=S.E (t-s).toNNReal (Y s)
-- glue at compatible heights

def lifted (z:ℂ): H:= S.F (z- ↑(z.re/2)) (Y (z.re/2))
lemma branch_eq_heat (t:ℝ)(ht:0<t): S.F (t:ℂ)= S.E t.toNNReal:= by
  rw [show (t:ℂ) = duration t.toNNReal from congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal t ht.le).symm,
      S.roots_heat (Real.toNNReal_pos.mpr ht)]
variable (h:Positive S Y)
include h
private lemma common_branch (z:ℂ) {r t:ℝ} (u:0<r)(p:r ≤ t)(q:t < z.re):
    S.F (z-(t:ℂ)) (Y t)= S.F (z-(r:ℂ)) (Y r):= by
  rcases lt_or_eq_of_le p with v|v; swap; · rw [v]
  rw [show z-(r:ℂ)=z-t+↑(t-r) from (by push_cast; abel),S.pairs (show 0 < (z-(t:ℂ)).re from (by simpa using (sub_pos.mpr q))) (show 0<(↑(t-r):ℂ).re from sub_pos.mpr v), h r t u p, branch_eq_heat S (t-r) (sub_pos.mpr v)]
  rfl
lemma lifted_branch (z:ℂ)(r:ℝ)(u:0<r)(p:r < z.re): lifted S Y z=S.F (z-(r:ℂ)) (Y r):= by
  unfold lifted; have hp:=lt_trans u p
  rcases le_total r (z.re/2) with o|o; · exact common_branch S Y h z u o (half_lt_self hp)
  exact (common_branch S Y h z (half_pos hp) o p).symm
lemma lifted_heat {t:ℝ}(p:0<t): lifted S Y (t:ℂ)= Y t:= by
 rw [lifted_branch S Y h t (t/2) (half_pos p) (half_lt_self p), ← ofReal_sub, branch_eq_heat S _ (sub_pos.mpr (half_lt_self p)), ← h (t/2) t (half_pos p) (half_le_self p.le)]
lemma lifted_analytic : AnalyticOnNhd ℂ (lifted S Y) inside:= by
 intro z hz
 let a:= z.re/2
 have p:0<a:= half_pos hz; have q:a < z.re:= half_lt_self hz
 let f:ℂ→ℂ:=fun w=> w-a
 have hw : f z ∈ inside:= show 0<(f z).re from (by simpa only [f,sub_re,ofReal_re] using (sub_pos.mpr q))
 let L:H.Op →L[ℂ] H:= ContinuousLinearMap.apply ℂ H.space (Y a)
 apply ((L.analyticAt _).comp ((S.localHeat _ hw).comp (f:=f) (analyticAt_id.sub analyticAt_const))).congr
 filter_upwards [continuous_re.continuousAt.eventually (lt_mem_nhds q)] with x b
 exact (lifted_branch S Y h x a p b).symm
lemma lifted_shift {z w:ℂ}(p:z∈inside)(q:w∈inside): lifted S Y (z+w)=S.F z (lifted S Y w):=by
 let t:=w.re/2; have ht:0<t:= half_pos q; have hw:t<w.re:= half_lt_self q
 rw [lifted_branch S Y h _ t ht (lt_trans hw (by linarith only [add_re z w, show 0<z.re from p])),
     show z+w-↑t=z+(w-↑t) from (by abel), S.pairs p (show 0<(w-(t:ℂ)).re from (by simp only [sub_re,ofReal_re]; exact sub_pos.mpr hw)),
     lifted_branch S Y h w t ht hw]; rfl
-- transport jets
variable (n:ℕ)
def jet (z:ℂ): H:= iteratedDeriv n (lifted S Y) z
omit h
lemma jet_up : jet S Y (n+1)= deriv (jet S Y n):= iteratedDeriv_succ .. -- implicit tune
private lemma inner_analytic {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X] (f:ℂ→X)(p:AnalyticOnNhd ℂ f inside) : ∀ n:ℕ, AnalyticOnNhd ℂ (iteratedDeriv n f) inside
| 0=> by simpa using p
| n+1=> by rw [iteratedDeriv_succ]; exact (inner_analytic f p n).deriv -- implicit S Y h ..
include h
lemma jet_analytic : AnalyticOnNhd ℂ (jet S Y n) inside:= inner_analytic _ (lifted_analytic S Y h) n
lemma jet_shift {z w:ℂ}(p:z∈inside)(q:w∈inside): jet S Y n (z+w)=S.F z (jet S Y n w):=by
 induction n generalizing w with
 | zero=> simpa [jet] using lifted_shift S Y h p q
 | succ i ih =>
   let f:= jet S Y i
   rw [jet_up] -- both
   have a:= (jet_analytic S Y h i w q).differentiableAt.hasDerivAt
   have b: HasDerivAt (fun y=> S.F z (f y)) (S.F z (deriv f w)) w:= (S.F z).hasFDerivAt.comp_hasDerivAt w a
   have s: z+w ∈ inside:= add_pos (show 0 < z.re from p) (show 0<w.re from q)
   have g := (jet_analytic S Y h i _ s).differentiableAt.hasDerivAt
   have c: HasDerivAt (fun y=> f (z+y)) (deriv f (z+w)) w:= by
     simpa only [Function.comp_def,id,f,one_smul] using g.scomp w (show HasDerivAt (fun y=> z+y) 1 w from (hasDerivAt_const _ _).add (hasDerivAt_id w) |>.congr_deriv (by simp)) -- tune
   exact (c.congr_of_eventuallyEq (Eventually.mono (p:=fun x=>x∈inside) (open_inside.mem_nhds q) fun u p' => (ih p').symm)).unique b
lemma jet_tick (z w:ℂ)(p:z∈inside)(q:w∈inside): jet S Y (n+1) (z+w)= deriv S.F z (jet S Y n w):= by
 let f:= jet S Y n
 let L:H.Op →L[ℂ] H:= ContinuousLinearMap.apply ℂ H.space (f w)
 have b: HasDerivAt (fun x=> S.F x (f w)) (deriv S.F z (f w)) z:= L.hasFDerivAt.comp_hasDerivAt z (S.localHeat z p).differentiableAt.hasDerivAt
 have s: z+w ∈ inside:= add_pos (show 0 < z.re from p) (show 0<w.re from q)
 have g: HasDerivAt (fun x=> f (x+w)) (deriv f (z+w)) z:= by
   simpa only [Function.comp_def,id,f,one_smul] using (jet_analytic S Y h n _ s).differentiableAt.hasDerivAt.scomp z ((hasDerivAt_id z).add_const w)
 rw [jet_up]
 exact (g.congr_of_eventuallyEq (Eventually.mono (p:=fun x=>x∈inside) (open_inside.mem_nhds p) fun u p' => (jet_shift S Y h n p' q).symm)).unique b
end YM.SatinJets
#print axioms YM.SatinJets.jet_analytic
#print axioms YM.SatinJets.jet_shift
#print axioms YM.SatinJets.jet_tick
