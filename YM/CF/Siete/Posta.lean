/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Siete.Rents
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q M D v ε d r η t x:ℝ}{G:Gauge}{L:Side}(W:Web G)(B P:BudgetPoint)
structure Sum (Z : Foliage.Collar G n)(W:Web G)(L:Side)(B P: BudgetPoint)(x η w t Q u b ε:ℝ):Prop where
 tension:Tension W η Q ε x t (loom B (reach x) b) P.threshold
 lit:Foliage.Cube.Wire B (reach x) Z
 lamp: W.scale*(Q*loom B (reach x) b)^2 ≤ P.threshold/32
 caps: loom B (reach x) (Foliage.Cube.fee Z) ≤ u
 people:ε*P.threshold + clinicFee n Q*(loom B (reach x) b)^2 ≤ 2*(L.val:ℝ)⁻¹^3*P.threshold
 narrow {c f:Side}(S:StepData c f)(X:Support f)(o:Site f): S.patch.L=L → o∈X→ Short S P X→∀ e,Mom.needed X e→ width P o e ≤ 1
section burn
lemma towns {B₀:Foliage.Collar G n}(b:ℝ)(hB:Foliage.Cube.fee B₀ ≤ b)(ht:1≤Q)(p:0<t)(hL:0<r)(h:0<η)(hg:W.scale * ε ≤ 1/128)(hy:ε ≤ 1/2)(hz:ε ≤ (L.val:ℝ)⁻¹^3)(s:ℕ):∀ᶠ x in atTop, ∀ P B:BudgetPoint, P.threshold=temp x → B.threshold=fiery G x L → B.B ≤2*radiusB x→ P.power=s → B.power=s → Sum B₀ W L P B x η M t Q r b ε:=by
 let d:=G.slopeConstant * Real.log L.val
 let v:=Foliage.Cube.fee B₀; let U:=W.scale; have hW:1≤U:=W.cost; have hcU:=Foliage.Cube.fee_one B₀; change 1≤v at hcU; have hc:=hcU.trans hB; let z:=(L.val:ℝ)⁻¹; have hp:0< z ^3:= pow_pos (by unfold z; positivity) _
 have he(x:ℝ):0≤(1:ℝ)+6*(1+(radiusB x:ℝ))*L.val ∧(1:ℝ)+6*(1+(radiusB x:ℝ))*L.val≤ (1+6*(L.val:ℝ))*(1+(radiusB x:ℝ)):=by have hx:0≤(radiusB x:ℝ):=(by positivity); constructor <;> nlinarith only [hx,Nat.cast_nonneg (α:=ℝ) L.val, mul_nonneg hx (show 0 ≤ (L.val:ℝ) by positivity)]
 filter_upwards [Rebuild.geometry d,reachPays (K:=4*G.colorScale) (a:=0) B₀.pos s,reachPays (K:=v) (a:=0) hL s,reachPays (K:=b) (a:=0) p s,reachPays (K:=Q*b) (a:=0) (lt_min W.pos zero_lt_one) s,reachExpense η h s (2*U*b) (by positivity),reachPays (K:=U*4*(Q*b)^2) (a:=0) (show (0:ℝ)<1/256 by norm_num) (s*2),reachPays (K:=clinicFee n Q*b^2*2) (a:=0) hp (s*2), Heir.reserve (Eventually.of_forall he) d 1 s zero_lt_one 1] with x hx h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ P B hv hb hr hs hh
 simp_rw [add_zero, ←hv,pow_mul] at h₁ h₂ h₃ h₄ h₆ h₇
 let C:=loom P (reach x) b
 have H : P.threshold≤ C := le_trans (le_mul_of_one_le_left P.threshold_pos.le hc) (le_mul_of_one_le_right (by have := P.threshold_pos; positivity) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
 have hP:=P.threshold_pos.le; have hBP:=B.threshold_pos.le; have hV : 0 ≤ C:=hP.trans H; have hQ : C ≤ Q*C:=le_mul_of_one_le_left hV ht; have h0 :0≤temp x:= Work.E04.temp_nonneg x
 have hy' : B.threshold ≤2*P.threshold ∧ P.threshold ≤2*B.threshold :=by rw [hv,hb]; exact hx.2
 have hu:C < t:=by unfold C loom; rw [hs]; linarith only [h₃]
 have hc' :Q*C ≤ min W.radius 1:=by unfold C loom; rw [hs]; linarith only [h₄]
 have hq:W.scale*(Q*(temp x+C))^2 ≤ B.threshold/128:=by
    rw [←hv]; calc
      _ ≤ U*(Q*(C+C))^2:=by change U*_ ≤ _; gcongr
      _ ≤ _:=by unfold C loom; rw [hs]; nlinarith only [mul_le_mul_of_nonneg_right h₆.le hP,hy'.2]
 refine ⟨⟨hv ▸ hy'.2,hu,hc',hq,?_,?_,hg⟩,⟨?_,?_⟩,?_,?_,?_,?_⟩
 · unfold loom; rw [hs]; have he:=mul_le_mul (mul_le_mul_of_nonneg_right h₅ (by norm_num : 0 ≤ (2:ℝ))) hy'.2 hP (show 0 ≤ Real.exp _*2 by positivity); change U*_ ≤ _; nlinarith [mul_nonneg hBP (Real.exp_pos (η * radiusB x)).le]
 · exact le_trans (by nlinarith only [mul_le_mul_of_nonneg_right hy hBP,hy'.1]) H
 · unfold Foliage.Cube.moduleBill; rw [hs]; linarith only [h₁]
 · apply le_trans _ (hQ.trans (hc'.trans (min_le_right ..))); unfold C loom Foliage.Cube.moduleBill; gcongr ?_ * _; exact le_mul_of_one_le_left P.threshold_pos.le hc
 · have hu:W.scale*(Q*C)^2 ≤ W.scale*(Q*(temp x+C))^2 := by have hh:=W.cost; gcongr; try linarith -- tune
   apply (hu.trans hq).trans; linarith only [hBP]
 · change loom P _ v ≤ _; unfold loom; rw [hs]; linarith only [h₂]
 · have hu:P.threshold≤2*B.threshold:=hy'.2; let z':=(L.val:ℝ)⁻¹; refine le_trans (add_le_add (mul_le_mul_of_nonneg_right hz hBP) (d:=z'^3*B.threshold) ?_) (le_of_eq (by unfold z'; ring)); -- tune b corresponds eps term
   unfold loom z'; rw [hs]; nlinarith only [mul_le_mul_of_nonneg_right h₇.le hP,mul_le_mul_of_nonneg_left hu hp.le]
 intro c f S X o k y h i t; unfold Lyre.width; have he:separation i.1 o ≤ 6*(1+radiusB x)*S.patch.L.val:=(close_enough y (mem_union_left _ t.1)).trans (width_le h hr); rw [k] at he
 apply le_trans ?_ h₈.le; rw [hh,hb,one_mul]; change temp _ *_≤_; push_cast at *; gcongr; exact Work.E04.temp_nonneg _; exact le_rfl; exact_mod_cast he
end burn
end YM.CF.Siete
