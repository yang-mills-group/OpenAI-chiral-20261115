import YM.CF.Buffered.Tepid
import YM.CF.Buffered.Merchant
/-! Precise tolerance price for sharp anchors' GAUGE Angle. -/
set_option autoImplicit false
set_option synthInstance.maxSize 21000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Alloy.Tariff
open Function Filter Finset Lattice Wilson RG PathData Work.F03 Cube Region Roost Rush MeasureTheory Metric Girt Nova Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Kea Ember Mint Mint.Roe
open Crust Crust.Grid Region
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x a b β r C L M:ℝ} {p:BudgetPoint}{c:Clip}{G:Gauge}{F: PathData G}{N P:Side} {I J:Side}
private lemma exp_q {a b c h:ℝ}(e:0<a)(p:Real.exp (-h)*(a*b)^81 ≤ c)(g:0<b): (0<c)∧81*Real.log b ≤ h+Real.log c - 81*Real.log a:=by
 have hh:0<Real.exp (-h)*(a*b)^81:=by positivity
 have he:=Real.log_le_log hh p
 rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_mul e.ne' g.ne', Real.log_exp] at he; push_cast at he; exact ⟨hh.trans_le p,by linarith⟩
set_option quotPrecheck false in local notation "ω" => globe P F c p x p.threshold -- prefer explicit
lemma fence (d:ℝ)(t:0<d)(K:Planck N P (3:Side))(S:ℕ) (hs:2≤S) (h:F.Bounds c a C L)(q:0≤C)(g:0<x)(p₁:d≤1)(w:16*d ≤ p.threshold)(u:0<globe P F c p x p.threshold)(v:globe P F c p x p.threshold/2 ≤ globe P F c p x (p.threshold/2)) :
   Real.log (globe P F c p x p.threshold) - Real.log (globe N F c p x p.threshold)/81 ≤
   Plan.cellsCost N (3:Side) P x p.threshold C L S (2*d) a c.direct /81 + (2*Real.log 2+ (4*(4*(2*(2*S))):ℝ)*P.val^3 * Module.finrank ℝ G.Mat*|Real.log (d/4)|) := by
 let a':=(d/4)^ (Module.finrank ℝ G.Mat*(stripP P (2*S)).card); let G':= globe P F c p x p.threshold; let X:= globe P F c p x (p.threshold/2); have hX:0<X:= (half_pos u).trans_le v
 have e := Grid.plan_ex K h g.le hs t p₁ (a:=p.threshold/2) (by linarith only [w]) q hX
 let T:=Plan.cellsCost N (3:Side) P x p.threshold C L S (2*d) a c.direct; have hA:0<a':=by unfold a'; positivity
 change Real.exp (-T)*(a'/2*X)^(Fintype.card _ )≤_ at e; rw [towers] at e; have hp:= (exp_q (half_pos hA) e hX).2; have hq:= Real.log_le_log (half_pos u) v
 let M:=Module.finrank ℝ G.Mat; let L:= Real.log (d/4); have hv:L≤0:=Real.log_nonpos (by positivity) (by linarith)
 rw [Real.log_div u.ne' (by norm_num)] at hq; have hl: -(4*(4*(2*(2*S))):ℝ)*P.val^3 * Module.finrank ℝ G.Mat *|Real.log (d/4)| ≤ Real.log a':=by
   let c:ℕ:= (stripP P (2*S)).card; let C:=4*(4*(2*(2*S*P.val^3))); have ht:c ≤ C:= le_trans (strip_count ..) (by unfold C; apply le_of_eq; ring)
   unfold a'; rw [Real.log_pow,abs_of_nonpos hv]; apply le_trans ?_ (mul_le_mul_of_nonpos_right (show ((M*c:ℕ):ℝ)≤ ((M*C:ℕ):ℝ) by exact_mod_cast Nat.mul_le_mul_left M ht) hv); apply le_of_eq; unfold C M L; push_cast; ring -- tune omega
 rw [Real.log_div hA.ne' (by norm_num : (2:ℝ)≠0)] at hp; change Real.log G' - _/81 ≤ T/81+_ ; change Real.log G'-_ ≤ Real.log X at hq; nlinarith only [hl,hq,hp]
lemma eventual_fence (G:Gauge) (a:ℝ)(h:0<a)(k V₀ C:ℝ)(p:0≤C)(c:Clip)(u:0<k):
 ∀ᶠ x:ℝ in atTop,∀ {N P:Side},Planck N P 3 → (Real.log x)^4 ≤ (P.val:ℝ) →∀ {F:PathData G}{q:BudgetPoint}, F.Bounds c a C V₀ → q.threshold=temp x → 0< globe P F c q x q.threshold → globe P F c q x q.threshold/2 ≤ globe P F c q x (q.threshold/2) →
   Real.log (globe P F c q x q.threshold) - Real.log (globe N F c q x q.threshold)/81 ≤ k*P.val^4:=by
 let l(x):= Real.log x; let t(x):=spikes a x; let M:= Module.finrank ℝ G.Mat
 let w:= 64*(M:ℝ)
 filter_upwards [(Xentry₀ (b:=C) (c:=V₀) (d:=c.direct) h).eventually (ge_mem_nhds u), district h (show 0≤w by unfold w; positivity) _ (half_pos u) _ (show 0≤2*Real.log 2 by have he:=Real.log_nonneg (by norm_num : (1:ℝ)≤2); positivity),forerun,eventually_ge_atTop (1:ℝ)] with x v Q hu hx
 intro N P K e F q r f p₀ p₁
 have hz:= Q (P.val:ℝ) e; let E:=Xentry a C V₀ c.direct x
 have ht : Plan.cellsCost N (3:Side) P x q.threshold C V₀ (t x) (2*shunt x) a c.direct /81 ≤ k/2*P.val^4:=by
    rw [f]; unfold t; rw [← Xledger]; swap; · exact K.ratio
    change E * _/81 ≤ _; calc
      _ ≤ k*(P.val:ℝ)^4/81:= div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (show E ≤ k from v) (by positivity)) (by norm_num)
      _ ≤ _ := by nlinarith [pow_nonneg (show 0 ≤ (P.val:ℝ) by positivity) 4]
 refine le_trans (fence (shunt x) (shunt_p _) K (t x) (by unfold t spikes; omega) r p (zero_lt_one.trans_le hx) hu.1 (f ▸ hu.2) p₀ p₁) ?_
 refine le_trans (add_le_add ht (show 2*Real.log 2+_*(P.val:ℝ)^3*Module.finrank ℝ G.Mat*|Real.log (shunt x/4)|≤ k/2 * P.val^4 from ?_)) (le_of_eq (by ring))
 refine le_trans ?_ hz; apply Eq.le; unfold w M t; ring
end YM.CF.Buffered.Alloy.Tariff
#print axioms YM.CF.Buffered.Alloy.Tariff.eventual_fence
