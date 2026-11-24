import YM.CF.Vol.Gars
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Next.Fluctuations (AgreeNear)
open Next.SectorChange Next.SectorChange.Rows
private def fundsV (G:Gauge)(C D:ℝ)(n:ℕ):=G.colorScale⁻¹*(2^n*(2^n*C*(G.colorScale*D))*C)
lemma shortened(q:Clip)(C:ℝ)(hs:0<s)(p:PaintSupply G n D)(h:0 ≤ A):∃ M v:ℝ,0<M∧0<v ∧∀ {c:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E → Config G c)(x:E), (∀ i, Allows n (fun y=>G.mat (U y i)) x A) →∀ {Y:ℝ}(R:PathData G), R.Bounds q s C Y→∀ r b:ℕ,0<b→∀ i, Allows n (fun y=>plotted R q r b (U y) i) x M:=by
 let g:=G.colorScale; obtain ⟨N,hN,h⟩:=travel_coupon G n A h (half_pos hs)
 let L:=curvatureCost G*travelCost G n 4 A; let M:=fundsV G N L n; let H:= Real.sqrt q.direct*L; let V:= max (max H (C*M)) 1
 refine ⟨V,1,lt_of_lt_of_le zero_lt_one (le_max_right ..),zero_lt_one,?_⟩
 intro c E _ _ U x hU Y R hp r b hb i; have ht(j:Cell c): Allows n (fun y=>G.curvature (faceValue (U y) j)) x L:= curvature_price (U:=fun y=>faceValue (U y) j) (travel_jets (U:=U) hU j.1 (a:=4) le_rfl); have hM:0 ≤ M:=by have hx:0≤L:=(ht i.1).nonneg; unfold M fundsV; have :=G.colorScale_pos; positivity
 unfold plotted; split
 · have he(U:Config G c)(x:Cell c) : shorten R r b U x=∑ z∈Stack.allShort (r/b), Stack.grouped R x.2 z • G.adjoint (travel U x.1 z.walk) (G.curvature (faceValue U (Work.F03.slotFace z x.1))):=by
       rw [← Stack.finite_price x (r/b) U (fun i=>G.curvature (faceValue U i)) hp, barrel_term]; unfold shorten; refine tsum_congr fun i=> ?_; simp [shortenTerm,Nat.le_div_iff_mul_le hb]
   simp_rw [he]; refine (allows_sum (s:=Stack.allShort (r/b)) (C:=fun z=>|Stack.grouped R i.1.2 z| *(Real.exp (s*z.length)*M)) (fun j _=>?_)).mono ?_
   · let X:=Real.exp (s/2*j.length); have hm:= (travel_jets hU i.1.1 (w:=j.walk) (show j.walk.length ≤ j.length from Nat.le_add_right ..)).mono (h _)
     refine (((adjoint_cost (U:=fun y=> travel (U y) i.1.1 j.walk) hm (ht (Work.F03.slotFace j _))).smul _).mono (Eq.le ?_)); rw [show Real.exp (s*j.length) =X*X from by unfold X; rw [← Real.exp_add]; congr 1; ring]; unfold X M fundsV; ring
   simp_rw [← mul_assoc |Stack.grouped R _ _|, ← sum_mul]; exact (mul_le_mul_of_nonneg_right (Stack.grouped_le _ hp i.1.2) hM).trans ((le_max_right ..).trans (le_max_left ..))
 have he:= (ht i.1).smul (Real.sqrt q.direct); rw [abs_of_nonneg (Real.sqrt_nonneg _)] at he; exact he.mono ((le_max_left H (C*M)).trans (le_max_left ..))
def tideX{c f:Side}(S:StepData c f)(k:S.Choices)(V:Config G c)(U:Config G f) : Bond c→G.El:= fun i=> V i*(S.prediction U k i)⁻¹
def paysX (n:ℕ)(U:E → Config G f)(V:E → Config G c)(x:E)(X A:ℝ)(k:S.Choices):Prop:=(∀ i:Bond c,Allows n (fun y=>G.mat (tideX S k (V y) (U y) i)) x X)∧(∀ i,Allows n (fun y=>G.mat (U y i)) x A) ∧(∀ i, Allows n (fun y=>G.mat (V y i)) x A)
lemma bags (K:Teller G)(P:Patch)(n:ℕ)(hn:3 ≤ n)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind n)(p:P.Branches K.bind G)(C:ℝ)(hc:0 ≤ C):∃ D σ:ℝ,0<D ∧0<σ ∧ σ ≤ 1 ∧∀{c f:Side}(S:StepData c f)(T:Tube G S), K.Funds S T→ S.patch=P→∀ k:S.Choices,∀{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](F:E → Config G f)(H:E → Config G c), Uniform.Inputs F (n+1) C→ Uniform.Inputs H (n+1) C→ ∀ x:E, ‖x‖<σ→ paysX n F H x D C k:=by
 let R:=predictionRadius P G K.bind n W.lc C W.D W.δ W.r; let u:= composeCost n W.W (connectorCost P G n W.lc C); let Y:= max (2^n*C*u) 1
 refine ⟨Y,if 0<R then min R 1 else 1,zero_lt_one.trans_le (le_max_right ..),by split; exact lt_min (by assumption) zero_lt_one; exact zero_lt_one,by split; exact min_le_right ..; rfl,?_⟩
 intro c f S T hHp hu k E _ _ _ F H hF hH x hX
 have he:=prediction_radius_pos S hF (show 2≤ n by omega) W.exp W.log W.focus
 rw [hHp.knobs,hu] at he -- dep
 have hx:0<R:=he; rw [if_pos hx] at hX; have h(y):= (hH.2.2 y _ (hX.le.trans (min_le_right ..))).order (Nat.le_succ n)
 refine ⟨fun i=>?_,fun i=>(hF.2.2 i _ (hX.le.trans (min_le_right ..))).order (Nat.le_succ n), h⟩
 have hb : x∈ball 0 (predictionRadius S.patch G S.kernel n W.lc C W.D W.δ W.r):=mem_ball_zero_iff.mpr (by rw [hHp.knobs,hu]; exact hX.trans_le (min_le_left ..))
 have hv:= prediction_pay S hF (show 2 ≤ n by omega) W.exp W.log W.focus x hb k i
 exact ((h i).times (hv.inverse (f:=fun y=> S.prediction (F y) k i))).mono (le_trans (le_of_eq (by rw [hu])) (le_max_left ..)) -- ordering inverse
end YM.CF.Vol
