import YM.CF.Esti.FlowP
set_option autoImplicit false
noncomputable section
namespace YM.CF.Esti
open CF.Jet
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (Multiplicity PaintSupply travelCost)
open Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {α β τ:Type}[Fintype α][Fintype β]
def wheelH(U:E → α→ β→ Pay G)(n:ℕ)(x:E)(V:ℝ) : Prop:=
 (∀ (Y: β→ E→ G.Color) (M:ℝ),0 ≤ M→(∀ i,Allows n (Y i) x M)→∀ i,Allows n (fun y=> zip (U y) (fun j=>Y j y) i) x (V*M)) ∧
 (∀ (Y: α→ E→ G.Color) (M:ℝ),0 ≤ M→(∀ i,Allows n (Y i) x M)→∀ i,Allows n (fun y=> unzip (U y) (fun j=>Y j y) i) x (V*M))
def rollP(G:Gauge)(s:ℝ)(l:ℕ):ℝ:=l*(2*((1+s)/s))^(Fintype.card Axis)
private lemma weightG {P:α→Site f}(p:Multiplicity P l)(k:Cover→ Site f)(R:Finset Cover)(h:0<s)(ht:0≤ A) : ∑ i:α,∑ j∈R,(if P i=k j then tal j s*A else 0) ≤ rollP G s l*A:=by
 let S:=Laurent.Width.compactPay (α:=Axis) s h
 rw [sum_comm]; calc
    _ ≤ ∑ j∈R,(l:ℝ)*(tal j s*A):=by
        apply sum_le_sum; intro i hi; rw [← Finset.sum_filter,sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right (by exact_mod_cast p (k i)) (mul_nonneg (Real.exp_pos _).le ht)
    _ ≤ _:=by rw [← Finset.mul_sum,← sum_mul,rollP,mul_assoc (l:ℝ)] -- tune
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (((S.2.1.sum_le_tsum R (fun i _=>S.1 i)).trans S.2.2)) ht) (by positivity)
lemma trek(G:Gauge){D L C A:ℝ}(h:0<D)(hl:0<L)(ha:0 ≤ A)(hc:0 ≤ C)(n l:ℕ):∃ V:ℝ, 0 ≤ V ∧∀{c f:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (U:E → Config G f)(x:E), (∀ i, Allows n (fun y=> G.mat (U y i)) x C) →∀ {α β:Type}[Fintype α][Fintype β] (o:α→Site c)(T:β→Site c), Multiplicity o l → Multiplicity T l →∀ (p:α→ Site f)(w:α→ Cover→Walk)(K:Finset Cover), (∀ i j,((w i j).length:ℝ) ≤ L*(1+size j)) →∀ (P:α→ β→ Cover→ℝ), (∀ i j k, |P i j k|≤tal k D * A) →∀ (r b:ℕ), (∀ i j, (w i j).length*b ≤ r → j∈K) →wheelH (fun y i j=> ∑' k : Cover, if (w i k).length*b ≤ r ∧ T j=o i+wrap c k then rated (U y) (p i) (w i k) (P i j k) else 0) n x V:=by
 obtain ⟨t,ht,hF⟩:= flick G n h hl ha hc; let B:=rollP G (D/2) l; refine ⟨B*t,by unfold B rollP; positivity,?_⟩
 intro c f E _ _ U x hU α β _ _ o T ho hT p w K hw P hP r b hr
 let g i j k (y:E) := if (w i k).length*b ≤ r ∧ T j=o i+wrap c k then rated (U y) (p i) (w i k) (P i j k) else 0
 have he i j y : (∑' k,g i j k y)=∑ k∈K,g i j k y:= tsum_eq_sum fun k hk=> if_neg fun h=> hk (hr _ _ h.1)
 have hh i j k {M:ℝ} (f:E→ G.Color) (h:Allows n f x M):
  let V:=if T j=o i+wrap c k then tal k (D/2)*(t*M) else 0
  Allows n (fun y=> g i j k y (f y)) x V ∧ Allows n (fun y=> (g i j k y).adjoint (f y)) x V:=by
    intro V; unfold g; split_ifs with hi
    · unfold V; rw [if_pos hi.2]; exact hF U x hU _ _ (hw i k) _ (hP _ _ _) f f _ h _
    have hV:0 ≤ V:=by unfold V; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg ht h.nonneg); rfl
    simp only [ContinuousLinearMap.zero_apply, map_zero]; exact ⟨allows_const _ (by simpa using hV),allows_const _ (by simpa using hV)⟩
 change wheelH (fun y i j=> ∑' k,g i j k y) n x _; simp_rw [he]; constructor
 · intro Y M hm hp i; unfold zip; simp_rw [_root_.sum_apply]; refine (allows_sum (s:=Finset.univ) (fun j _=> allows_sum (s:=K) (fun k _=> (hh i j k _ (hp j)).1))).mono ?_
   rw [mul_assoc B]; exact weightG hT _ K (half_pos (by assumption)) (mul_nonneg ht hm)
 intro Y M hm hp j; unfold unzip; simp_rw [map_sum,_root_.sum_apply]; refine (allows_sum (s:=Finset.univ) (fun i _=> allows_sum (s:=K) (fun k _=> (hh i j k _ (hp i)).2))).mono ?_
 rw [mul_assoc B]; let f(k:Cover):= T j-wrap c k; simp_rw [show ∀ i k, T j=o i+wrap c k ↔o i=f k from fun i k=>by unfold f; rw [eq_sub_iff_add_eq,eq_comm]]
 exact weightG ho f K (half_pos h) (mul_nonneg ht hm)
end YM.CF.Esti
