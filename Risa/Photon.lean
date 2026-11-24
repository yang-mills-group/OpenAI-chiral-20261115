import LusterS.Rogue
import YM.SU5.Regis.Trophy
/-! # Sparse defect treatment under outer-threshold tree purchase -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
abbrev starFee (B:Z.Bounds q η C S)(P:Attached H Z)(r:Ratio c n)(A:Support c)(Dt:Finset (Cell n))(m:ℕ)(Y:fieldDir G n 1)(β:ℝ)(X:fieldDir G n 1):= (coupling β)⁻¹ • (tiler B P X + advent B P r Dt A m Y)
def weakWish (B:Z.Bounds q η C S)(P:Attached H Z)(T:Forest r)(F:Finset T.Free)(A:Support c)(Dt:Finset (Cell n))(m:ℕ)(Y:fieldDir G n 1)(β:ℝ)(W:Altar G n→ℝ)(t:ℝ) (x:LogArray G F):= scintillate Z q T F Dt A m Y β x * Real.exp (t* W (starFee B P r A Dt m Y β (stock T F x)))
open Module ProbabilityTheory Regis
variable (Dt:Finset (Cell n))
include B P L
set_option maxHeartbeats 220000 in -- adaptation Rounds
lemma at_weak (Y:fieldDir G n 1)(h:(cellM T F H).PosDef)(p:0<β)(W:Altar G n→ℝ)(a: ContDiff ℝ 1 W){b₁ b₂:ℝ}(h1:∀ x, |W x|≤ b₁)(h2:∀ x, ‖fderiv ℝ W x‖≤ b₂)(t:ℝ): let f:=weakWish B P T F A Dt m Y β W t; let K:= chartCost (prism T F H G)⁻¹ (coupling β); let E:= plumeCost B P W t + trend*b₂^2*t^2 + ((finrank ℝ (stamen B P n):ℝ) - (finrank ℝ (LinearMap.range (estate B P T F))))/2; Integrable f volume ∧ (∫ x,f x) ≤ K* Real.exp E:=by
 let Ψ:= (prism T F H G); let σ:= coupling β; have hf: Ψ.PosDef:= h.kronecker PosDef.one; let Φ:= tiler (n:=n) B P; let D:= advent B P r Dt A m Y; let V:= estate B P T F; let X:= LinearMap.range V; let g:= coupling_pos p; obtain ⟨a',ha,b,hb,he⟩:= X.exists_add_mem_mem_orthogonal D; obtain ⟨x,hx⟩:= ha; let c':= - x; have hE: D=a'+b:=he
 intro f K Q
 obtain ⟨hq,ht⟩:= at_price Ψ⁻¹ hf.inv g c' f
 let μ:=cloud Ψ⁻¹; let d:= σ⁻¹ • b; let L':= Real.exp (-β* (‖b‖^2/2)); let ξ: X→ℝ:= fun i=> Real.exp (t * W (i.val+d)); let T'(x:Prices G F):=Real.exp (force Ψ⁻¹ x/2) • f (displaced c' σ x)
 have he' : T'=fun x=> L'* ξ (V.rangeRestrict x):=by
    funext y; unfold T' f weakWish scintillate; rw [tiler_read B P]; let t':= displaced c' σ y
    have h : Φ (stock T F t')+D= σ • V y+b:=by
       rw [hE,←hx]; change V (-x+σ • y)+(V x+b)=_; rw [map_add,map_neg,map_smul]; abel
    rw [starFee,show (tiler B P) _ + _=_ from h,norm_add_sq_real (σ • V y) b,show inner ℝ (σ • V y) b=0 from ?_,mul_zero,add_zero]
    · rw [norm_smul,Real.norm_of_nonneg g.le,mul_pow]; let Y:=qpay Ψ y; have hv : ‖V y‖^2=Y:=Tape_price B P L y; rw [hv,show force Ψ⁻¹ y=Y from ?_, smul_eq_mul, ← mul_assoc, ← Real.exp_add]; swap; · unfold force; rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hf.isUnit)]; rfl
      congr 1
      · have hw:β*σ^2=1:=coupling_inter _ p; unfold L'; congr 1; linarith only [show β*σ^2 * Y =Y by rw [hw,one_mul]]
      unfold ξ; rw [smul_add, inv_smul_smul₀ g.ne']; rfl
    exact (Submodule.mem_orthogonal _ b).1 hb _ (X.smul_mem _ ⟨y,rfl⟩)
 let U:=stamen B P n; have hx:X≤U:=by intro x h; exact (LinearMap.range_comp_le_range ..).trans (LinearMap.range_comp_le_range ..) h -- tune
 have hw(X'): ‖V X'‖^2=qpay Ψ X':= Tape_price B P L _
 let κ:= stdGaussian X; let S:=V.rangeRestrict; have hs:MeasurePreserving S μ κ:= pew V hf hw
 have hi: Integrable ξ κ:= puff κ (fun y:X=> W (y.val+d)) t (a.continuous.comp (continuous_subtype_val.add continuous_const)|>.measurable) (fun i=> h1 _)
 have hp : ‖d‖^2= β*‖b‖^2:= by
    have hw:β*σ^2=1:=coupling_inter _ p; unfold d; rw [norm_smul,mul_pow,Real.norm_eq_abs,abs_of_nonneg (inv_pos.mpr g).le,inv_pow, inv_eq_of_mul_eq_one_left hw] -- tune
 have hy: (∫ x,T' x ∂μ) ≤ Real.exp Q:=by
    rw [he', integral_const_mul]; change L' * (∫ x, ξ (S x)∂μ)≤ Real.exp Q
    rw [← integral_map hs.aemeasurable (f:=ξ) (by unfold ξ; fun_prop (disch:=exact a.continuous)),hs.map_eq]
    refine (mul_le_mul_of_nonneg_left (swerve W t X U h1 a h2 hx d) (Real.exp_pos _|>.le)).trans_eq ?_; rw [←Real.exp_add,hp]; unfold Q U X plumeCost; congr 1; ring
 refine ⟨hq.mpr ?_,ht.trans_le ?_⟩; · change Integrable T' μ; rw [he']; exact (hs.integrable_comp_of_integrable hi).const_mul _
 exact mul_le_mul_of_nonneg_left hy (chartCost_pos _ hf.inv g|>.le)

#print axioms at_weak
end Risa
end YM.Gleam.Luster