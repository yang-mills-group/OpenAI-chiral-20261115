import YM.CF.Onyx.Tuft
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {D:ℝ}{x:Gaia}
def kiln(D:ℝ):ℝ:= (4*D^2)⁻¹
def gleamV(x:Gaia) : Peb:= minA*∑ i:Axis,(x i:ℂ) • gammaOp i
def sha(D:ℝ)(x p:Gaia):Peb:= (2*purr (kiln D) x p) • lash (river p)
def pencil(x:Gaia):Peb:= ((Real.pi^2*‖x‖^4)⁻¹:ℝ) • gleamV x
def dun(D:ℝ)(x:Gaia):Peb:= cartWeight • ∫ p:Gaia, sha D x p
lemma hue (h:0<D)(p:x≠0) : dun D x= (-cartWeight * dye (kiln D) x) • gleamV x:=by
 let u:=kiln D; have he:0<u:=by unfold u kiln; positivity
 let Z(a:Axis):= minA*gammaOp a
 let G(a:Axis)(y:Gaia):= nerve a u x y • Z a
 have ht(y: Gaia) : sha D x y= (-2:ℂ) • (∑ i,G i y):=by
    unfold sha lash zen G nerve; rw [Matrix.mul_sum,← sum_neg_distrib]; simp_rw [Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_
    simp only [Matrix.mul_smul,smul_neg,smul_smul, Z]; change -(_ • (minA*gammaOp i))= _; rw [← neg_smul]; congr 1 -- inspect
    change -(2*purr _ _ _*((y i:ℂ)*Complex.I))= _; unfold u; ring
 unfold dun; simp_rw [ht]; rw [integral_smul,integral_finsetSum univ (fun i _=> ((reek he i x).smul_const (Z i)))]; unfold Z; simp_rw [integral_smul_const (f:=nerve _ u x),say _ he p]; unfold gleamV; simp_rw [Finset.smul_sum,Matrix.mul_sum,Finset.smul_sum]; -- tune
 refine sum_congr rfl fun i _=>?_ ; rw [←BZ.ofReal_action, ← BZ.ofReal_action, Matrix.mul_smul]; simp only [smul_smul]; congr 1; push_cast; unfold u; ring
lemma wind_v (h:x≠0): Tendsto (fun D:ℝ=> dun D x) atTop (𝓝 (pencil x)) :=by
 let y:=fieldV x; let F(D:ℝ):= y/kiln D; have he:0<y:=fen h
 have ht:Tendsto F atTop atTop:=by
    have hh:Tendsto (fun D:ℝ=> D^2 * (y*4)) atTop atTop:= (tendsto_pow_atTop (by decide)).atTop_mul_const (by positivity) -- tune
    convert hh using 1; ext i; unfold F kiln; simp [div_eq_mul_inv]; ring
 have hz:Tendsto (fun D=>Real.exp (-F D)) atTop (𝓝 0):= (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).comp ht
 have hp:Tendsto (fun D=>Real.exp (-F D)*F D) atTop (𝓝 0):=by simpa only [Function.comp_def,pow_one,mul_comm] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht -- tune name
 have hx:= (((hz.add hp).sub_const 1).const_mul (Real.pi^2/y^2)).const_mul (-cartWeight)
 have hr:Tendsto (fun D=> (-cartWeight*dye (kiln D) x) • gleamV x) atTop (𝓝 (pencil x)):=by
    convert (hx.smul_const (gleamV x)) using 1 -- tune
    · ext1 i; unfold dye; simp only [elf,neg_div,F,y]; rw [mul_add (Real.exp _),mul_one]
    congr 2; unfold pencil y fieldV Stationary.cartWeight; congr 1; have hp:0<‖x‖:=norm_pos_iff.mpr h; field_simp <;> ring
 exact hr.congr' ((eventually_gt_atTop 0).mono fun _ e=> (hue e h).symm)
end YM.CF.Onyx
