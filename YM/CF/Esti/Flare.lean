import YM.CF.Esti.Hills
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
open Next.Fluctuations (AgreeNear)
open Next.SectorChange Next.SectorChange.Rows
private def fundsV (G:Gauge)(C D:ℝ)(n:ℕ):=G.colorScale⁻¹*(2^n*(2^n*C*(G.colorScale*D))*C)
lemma shortened(q:Clip)(C:ℝ)(hs:0<s)(p:PaintSupply G n D)(h:0 ≤ A):∃ M v:ℝ,0<M∧0<v ∧∀ {c:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E → Config G c)(x:E), (∀ i, Allows n (fun y=>G.mat (U y i)) x A) →∀ {Y:ℝ}(R:PathData G), R.Bounds q s C Y→∀ r b:ℕ,0<b→∀ i, Allows n (fun y=>plotted R q r b (U y) i) x M:=by
 let g:=G.colorScale; obtain ⟨N,hN,h⟩:=travel_coupon G n A h (half_pos hs)
 let L:=curvatureCost G*travelCost G n 4 A; let M:=fundsV G N L n; let H:= Real.sqrt q.direct*L; let V:= max (max H (C*M)) 1
 refine ⟨V,1,lt_of_lt_of_le zero_lt_one (le_max_right ..),zero_lt_one,?_⟩
 intro c E _ _ U x hU Y R hp r b hb i; have ht(j:Cell c): Allows n (fun y=>G.curvature (faceValue (U y) j)) x L:= arc_b (U:=fun y=>G.mat (faceValue (U y) j)) (trekP _ U hU (square j.2.val.1 j.2.val.2) j.1 4 le_rfl); have hM:0 ≤ M:=by have hx:0≤L:=(ht i.1).nonneg; unfold M fundsV; have :=G.colorScale_pos; positivity
 unfold plotted; split
 · have he(U:Config G c)(x:Cell c) : shorten R r b U x=∑ z∈Stack.allShort (r/b), Stack.grouped R x.2 z • G.adjoint (travel U x.1 z.walk) (G.curvature (faceValue U (Work.F03.slotFace z x.1))):=by
       rw [← Stack.finite_price x (r/b) U (fun i=>G.curvature (faceValue U i)) hp, barrel_term]; unfold shorten; refine tsum_congr fun i=> ?_; simp [shortenTerm,Nat.le_div_iff_mul_le hb]
   simp_rw [he]; refine (allows_sum (s:=Stack.allShort (r/b)) (C:=fun z=>|Stack.grouped R i.1.2 z| *(Real.exp (s*z.length)*M)) (fun j _=>?_)).mono ?_
   · let X:=Real.exp (s/2*j.length); have hm:= (trekP _ U hU j.walk i.1.1 (j.length) (show j.walk.length ≤ j.length from Nat.le_add_right ..)).mono (h _)
     refine (((adjointQ (U:=fun y=> travel (U y) i.1.1 j.walk) hm (ht (Work.F03.slotFace j _))).smul _).mono (Eq.le ?_)); rw [show Real.exp (s*j.length) =X*X from by unfold X; rw [← Real.exp_add]; congr 1; ring]; unfold X M fundsV; ring
   simp_rw [← mul_assoc |Stack.grouped R _ _|, ← sum_mul]; exact (mul_le_mul_of_nonneg_right (Stack.grouped_le _ hp i.1.2) hM).trans ((le_max_right ..).trans (le_max_left ..))
 have he:= (ht i.1).smul (Real.sqrt q.direct); rw [abs_of_nonneg (Real.sqrt_nonneg _)] at he; exact he.mono ((le_max_left H (C*M)).trans (le_max_left ..))
end YM.CF.Esti