import YM.CF.Siete.Ska
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Cooling
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q v x:ℝ}{G:Gauge}{L:Side}
-- rates including polynomials in both widths
abbrev feeI(x:ℝ)(l k:ℕ):ℝ:= (1+((7*(1+radiusB x)+(l+50)*radiusB x:ℕ):ℝ))^k -- parse casts
lemma feeM(l:ℕ)(x:ℝ): 1 ≤ feeI x l 1 ∧ feeI x l 1 ≤ (l+64:ℕ) *Scales.b x:=by
 simp only [feeI,Scales.b,pow_one]; constructor <;> push_cast <;> nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)] -- tune Nat cast
lemma spiritu(h:0<C)(G:Gauge)(L:Side): ∀ᶠ x in atTop, K*(tideF v x)^2 * feeI x l n ≤ C*fiery G x L:=by
 let A:= |K| * ( (2*|v| )^2)*(l+64:ℕ)^n -- n cast ?
 have hv := (flowering (G.slopeConstant*Real.log L.val) (10+n)).eventually (gt_mem_nhds (show 0< C/(A+1) by unfold A; positivity))
 filter_upwards [hv,(Appel.crush G L).eventually (ge_mem_nhds zero_lt_one), monitors G L] with x hL he hz
 let f:=fiery G x L; have hx : b x ≥ 1:= size ..; have ht : temp x≤ 2* f:=hz.2.2; have hf:=hz.1; have hp:0<f:=by linarith
 have hG: ‖tideF v x‖ ≤ 2*|v| *(Scales.b x)^5*f:=by unfold tideF blockF; rw [norm_mul,norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ ((↑(radiusB x):ℝ)^5)),Real.norm_of_nonneg hf.le,Real.norm_eq_abs]; calc
    _ ≤ |v| *(b x^5*(2*f)):=by unfold Scales.b; gcongr <;>try first| exact ht| linarith -- tune
    _= _:=by ring
 have hK:b x^(10+n)* f<C/(A+1):=hL; change _ ≤ C*f
 calc
   _ ≤ |K| *(2*|v| *b x^5*f)^2 * ((l+64:ℕ)*b x)^n:=by rw [←sq_abs (tideF v x)]; gcongr; exact le_abs_self _; exact hG; exact pow_le_pow_left₀ (by positivity : 0≤1+((7*(1+radiusB x)+(l+50)*radiusB x:ℕ):ℝ)) (by simpa [feeI] using (feeM l x).2) n
   _ = A*(b x^(10+n)*f)*f:=by unfold A; rw [pow_add, mul_pow _ _ n]; ring_nf
   _ ≤ _:= by
        apply mul_le_mul_of_nonneg_right _ hp.le; rw [lt_div_iff₀ (by unfold A; positivity)] at hK; nlinarith only [hK,show 0 ≤ Scales.b x^(10+n)*f by positivity]
abbrev gateX (G:Gauge)(L:Side)(l n:ℕ)(x:ℝ)(C:ℝ):ℝ:= C*(Scales.p G L x / feeI x l n)
lemma tune_up (Z W:ℝ)(G:Gauge)(L:Side) (h:0<W)(p:0 ≤ Z) (l n:ℕ) :∃ z:ℝ,0<z ∧∀ᶠ x in atTop, 0<gateX G L l n x z ∧∀ d:ℝ,y G L x/2 ≤ d → Z*|coupling d| *gateX G L l n x z *feeI x l n≤ W*fiery G x L:=by
 let w:=W/(2*(Z+1)); have hw:0<w:=by unfold w; positivity
 refine ⟨w,hw,?_⟩; filter_upwards [(year G L).eventually_gt_atTop 0] with x hx; have he:=pos G L x; have hk:0<feeI x l n:=by unfold feeI; positivity
 refine ⟨by unfold gateX; positivity,fun d hd=>?_⟩
 let f:= y G L x; let g:= coupling f; have h':0< f:=hx; have hβ:0<d:=by change f/2≤_ at hd; linarith; -- tune
 have hb: |coupling d| ≤2*g:=by
    unfold g; rw [abs_of_nonneg (coupling_pos hβ).le]; unfold coupling; rw [← div_eq_mul_inv,inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hβ),div_mul_eq_mul_div,le_div_iff₀ (Real.sqrt_pos.mpr h'), one_mul]; nlinarith [Real.sq_sqrt h'.le,Real.sq_sqrt hβ.le, Real.sqrt_nonneg d]
 rw [fi,show Scales.g G L x=g from rfl]; calc
    _ ≤ Z*(2*g)*gateX G L l n x w*feeI x l n:=by
       apply mul_le_mul_of_nonneg_right _ hk.le; apply mul_le_mul_of_nonneg_right _ (show 0≤gateX G L l n x w by unfold gateX; positivity); gcongr
    _ = (2*Z*w)*(g*Scales.p G L x):=by unfold gateX; field_simp
    _ ≤ _:=mul_le_mul_of_nonneg_right (by unfold w; field_simp; nlinarith) (mul_nonneg (coupling_pos h').le he.le)
end YM.CF.Siete
