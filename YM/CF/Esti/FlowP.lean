import YM.CF.Esti.Axis
set_option autoImplicit false
noncomputable section
namespace YM.CF.Esti
open CF.Jet
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (PaintSupply travelCost)
open Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
section charge
local notation "ℰ"=>Real.exp
def tal(u:Cover)(s:ℝ):ℝ:=ℰ (-s*Laurent.size u)
lemma stipi {α β:Type}{P:Row α β}(p:P.strip s A)(i:α)(j:β)(u:Cover): |P i j u| ≤ tal u s*A:=by
 have hh:= p i j; have he:= ((hh.2.1.sum_le_tsum {u} (fun i _=>hh.1 i)).trans hh.2.2); rw [sum_singleton] at he; unfold tal; rw [neg_mul, Real.exp_neg]; exact (le_inv_mul_iff₀ (Real.exp_pos _)).2 he
variable {α β τ:Type} [Fintype α][Fintype β]
lemma flick (G:Gauge) (n:ℕ){D C A L:ℝ}(h:0<D)(hl:0<L)(ha:0 ≤ A)(hc:0 ≤ C):∃ V:ℝ, 0 ≤ V ∧∀ {f:Side}{E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (U:E → Config G f)(y:E), (∀ i, Allows n (fun x=>G.mat (U x i)) y C)  →  ∀ i:Cover,∀ w:Walk, (w.length:ℝ) ≤ L*(1+size i)  →  ∀ M:ℝ, |M|≤ tal i D * A  →  ∀ T v: E → G.Color, ∀ Y:ℝ,Allows n v y Y  → ∀ p:Site f,
 Allows n (fun x=> rated (U x) p w M (v x)) y (tal i (D/2)*(V*Y)) ∧ Allows n (fun x=> (rated (U x) p w M).adjoint (v x)) y (tal i (D/2)*(V*Y)):=by
 let d:=D/(4*L); have hd:0<d:=by unfold d; positivity
 obtain ⟨N,hn,hN⟩ := travel_coupon G n C hc hd; let T:=N*ℰ (D/4); have hp:0<T:=by unfold T; positivity
 let V:= A * (G.colorScale⁻¹*(2^n*(2^n*T*G.colorScale)*T))
 refine ⟨V,by unfold V; have := G.colorScale_pos; positivity,?_⟩
 intro f E _ _ U y hU i w hw a hv _ v Y hY p
 let y':= ℰ (D/4*(size i)); let J:=T*y'; have hh:N*ℰ (d*(w.length:ℝ)) ≤ J:=by
    unfold J T y'; rw [mul_assoc N,← Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hn.le; apply (mul_le_mul_of_nonneg_left hw hd.le).trans; unfold d; field_simp; linarith
 have hy:Allows n (fun z=> G.mat (travel (U z) p w)) y J:= (trekP _ U hU w p _ le_rfl).mono ((hN _).trans hh)
 have hz : |a| * (G.colorScale⁻¹*(2^n*(2^n*J*(G.colorScale*Y))*J)) ≤ tal i (D/2)*(V*Y):=by
    let X:=A * (G.colorScale⁻¹*(2^n*(2^n*T*(G.colorScale*Y))*T)); refine le_trans (mul_le_mul_of_nonneg_right hv (by have hk:=hY.nonneg; have hr:y'>0:=Real.exp_pos _; unfold J; have hh:=G.colorScale_pos; positivity)) ?_
    have hx :tal i D*y'*y'=tal i (D/2):= by unfold tal y'; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    rw [←hx]; exact Eq.le (by unfold J V; ring)
 exact ⟨((adjointQ hy hY).smul a).mono hz,by simp_rw [ConnectedActivityE6.Blaze.repel]; exact ((adjointQ (U:=fun x=>(travel (U x) p w)⁻¹) (gran (v:=fun x=>travel (U x) p w) hy) hY).smul a).mono hz⟩
end charge
end YM.CF.Esti
