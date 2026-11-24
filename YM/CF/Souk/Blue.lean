import YM.CF.Souk.Big
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort
variable{X Y:Fish ι →Neige.Shelf τ}{x':Fish ι}{p:ι→Site c}{u:τ→Site c}{a j:ℕ}
lemma sat (h: ContDiffAt ℝ n X x')(i j)(v:Fin n→ι): pS n X v x' i j=Uniform.entry (fun y=> X y i j) x' v:=by
 let L:Neige.Shelf τ →L[ℝ] ℝ:=LinearMap.toContinuousLinearMap {toFun:=fun z:Neige.Shelf τ=> z i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
 unfold Uniform.entry; change _= iteratedFDeriv ℝ n (L ∘ X) _ _; erw [L.iteratedFDeriv_comp_left h le_rfl]; exact rfl
private lemma glazeP(A:ℝ)(h:0 ≤ A)(p:ι→Site c)(y:Site c)(q:Fin n→ι): Uniform.glaze p y q A ≤ 1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (Nat.cast_nonneg _))
private lemma wan_b (X:Positions ι→Matrix τ τ ℝ)(h:Cable p u u none s i X x' C)(hs:0<s)(hp:0 ≤ C)(hq:n+1 ≤ i)(q:Fin (n+1)→ι)(i j:τ)(hh:a ≤ separation (p (q (Fin.last n))) (u i)):
 let A:=Real.exp (-(s/2)*(a:ℝ)); ‖Uniform.entry (fun y=> X y i j) x' q‖ ≤ A*C*Uniform.Decay (s/2) (p (q (Fin.last n))) (u i)*Uniform.Decay s (u i) (u j):=by
 intro A; let v:=p (q (Fin.last n)); let w:= Fin.init q; let k:=u i; let D:=Uniform.glaze p k q s; have he: Uniform.Decay s k v ≤ A*Uniform.Decay (s/2) v k:=by
    rw [Uniform.decay_comm,decay_div]; unfold A; apply mul_le_mul_of_nonneg_right ?_ (Uniform.decay_pos ..).le; unfold Uniform.Decay; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left ?_ (by linarith); exact_mod_cast hh
 have ht : D ≤ A*Uniform.Decay (s/2) v k:= by unfold D; rw [glaze_last]; exact (mul_le_of_le_one_right (Uniform.decay_pos ..).le (glazeP s hs.le p _ _)).trans he
 apply (h.paid i j q hq).trans; rw [thread_none,mul_one,←mul_assoc]; apply (mul_le_mul_of_nonneg_left ht (mul_nonneg hp (Uniform.decay_pos ..).le)).trans_eq; unfold v k; ring
lemma farX(h:Cable p u u none s i X x' C)(hs:0<s)(hp:0 ≤ C)(hq:n+1 ≤ i)(q:Fin (n+1)→ι)(hm:Multiplicity u j)(H:Finset τ)(ht:∀ i∈H, a ≤ separation (p (q (Fin.last n))) (u i))(hg:ContDiffAt ℝ (n+1:ℕ) X x') : (∑ i∈H,∑ k, |pS (n+1) X q x' i k|) ≤ Real.exp (-(s/2)*a)*C*(j*countCost (s/2))*(j*countCost s):=by
 let U:= (Uniform.Decay (s/2) (p (q (Fin.last n)))); let L:=(Real.exp (- (s/2)*(a:ℝ)))*C; let M:=(j:ℝ)*countCost s; have hL:0 ≤ L:=by unfold L; positivity; -- ok
 have hv(i:τ)(hi:i∈H):∑ k,|pS (n+1) X q x' i k|  ≤ L*U (u i)*M:=by
    refine (Finset.sum_le_sum (g:=fun k=> L*U (u i)*Uniform.Decay s (u i) (u k)) ?_).trans ?_
    · intro k _; rw [sat hg]; exact wan_b X h hs hp hq q i k (ht _ hi)
    rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left (hm.count u hs _) (mul_nonneg hL (Uniform.decay_pos ..).le)
 apply (Finset.sum_le_sum hv).trans; rw [← Finset.sum_mul,←Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (Uniform.count_pos hs).le)
 exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun a _ _=> (Uniform.decay_pos ..).le)).trans (hm.count u (half_pos hs) _)) hL
lemma far_H {z}(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(hp:Cert P K S T x)(ht: W.Service F T.high T.up z)(k:S.Choices)(t:ℝ)(hs:0 ≤ t)(hx:t ≤ 1):
 let Y':= W.tables K.top.clip P
 let X(y:Mast G c) := ξ T F k t z y; let v:=transit Y' n
 (0<v ∧ 0<chargeBill Y' n) ∧ ContDiffAt ℝ (n+1:ℕ) X 0 ∧ Cable (address F G ∘ Sum.inl) (address F G ∘ Sum.inr) (address F G ∘ Sum.inr) none v (n+1) X 0 (chargeBill Y' n):=by
 intro Y' X v; have h:=hp.funds.1; obtain ⟨C,V,hc,he⟩:=h.feeds; rw [←h.high] at hc
 have hC: Counter Y' n k T.high T.up z:=by unfold Y'; rw [←h.high,←hp.got]; exact Counter.service ht hc hp.pace h.atStep h.knobs k
 have hi:0 ∈ Planned.JetPort.domain (G:=G) (c:=c) Y':=by unfold Y'; rw [←h.high,←hp.got]; exact mem_ball_self ht.x_pos
 let L:=inside k T.high T.up z; have he:=(hC.alongShell hi).smooth
 let U(y:Mast G c):=t•y; have hh:U 0=0:=smul_zero _; have hM:=hC.alongShell hi; have hm i j : ContDiffAt ℝ ω (fun y=> L y i j) (U 0):= by rw [hh]; exact he i j
 refine ⟨⟨hM.rate_pos,hM.cost_pos⟩, ?_, fun i j k' hk r=>?_⟩
 · -- smooth matrix finite strict `∀ n`? proved ω analytic via LinearMap; use tests
   exact (show ContDiffAt ℝ (n+1:ℕ) L (U 0) from FreeResolvent.TestD.rectangle_smooth (fun i j=> (hm i j).of_le le_top)).comp (f:=U) _ (contDiffAt_id.const_smul _) -- tune
 rw [show Uniform.entry (fun y=> X y i j) 0 r= t^k' • Uniform.entry (fun y=>L y i j) 0 r from ?_,norm_smul_of_nonneg (pow_nonneg hs _)]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hx)).trans (hM.coefficient _ _ k' hk r)
 unfold X ξ; rw [entry_scale (fun y=>inside k T.high T.up z y i j) t r 0 ((hm i j).of_le le_top),smul_zero]
end YM.CF.Souk
