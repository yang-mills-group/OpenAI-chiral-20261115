import Bay.D.Pinery
import Mathlib.Analysis.Calculus.Taylor
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

variable {E₁:Type}[NormedAddCommGroup E₁][NormedSpace ℝ E₁]{f:E₁→ℂ}{x:E₁}
abbrev pencil(x:E₁):ℝ→L[ℝ] E₁:= (ContinuousLinearMap.id ℝ ℝ).smulRight x

lemma tipLine (x:E₁) (v:ℝ) (k:ℕ)(p:ContDiffAt ℝ k f (pencil x v)):
    iteratedDeriv k (f ∘ pencil x) v=
     iteratedFDeriv ℝ k f (pencil x v) (fun _=>x):=by
 obtain ⟨s,h,g,w⟩:=_root_.mem_nhds_iff.mp (p.eventually (by simp))
 let z:=pencil x
 have hv:=g.preimage z.continuous
 have jt:= z.iteratedFDerivWithin_comp_right (show ContDiffOn ℝ k f s from fun t i=> (show ContDiffAt ℝ k f t from h i).contDiffWithinAt) g.uniqueDiffOn hv.uniqueDiffOn w (le_refl (k:ℕ∞ω))
 rw [iteratedFDerivWithin_of_isOpen _ hv (show _ from w),iteratedFDerivWithin_of_isOpen _ g w] at jt
 rw [iteratedDeriv_eq_iteratedFDeriv,jt,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 exact congrArg _ (funext fun _=>one_smul _ _)

def tremble(f:E₁→ℂ):E₁→L[ℝ]E₁→L[ℝ]ℂ:=
  (2⁻¹:ℝ) • fderiv ℝ (fderiv ℝ f) 0
def quiver(f:E₁→ℂ)(x:E₁):ℂ:=tremble f x x
lemma tremble_sym (g:ContDiffAt ℝ (2) f 0)(x y:E₁):tremble f x y=tremble f y x:=congrArg ((2⁻¹:ℝ) • ·) ((g.isSymmSndFDerivAt (minSmoothness_of_isRCLikeNormedField.le)).eq ..)
lemma trembling(k:ℝ): quiver f (k • x) = k^2 • quiver f x:=by unfold quiver;rw[map_smul, map_smul, smul_apply, smul_smul, ←sq]

lemma pencil_shiver (g:ContDiffAt ℝ 2 f 0) (x:E₁):
    (2⁻¹:ℝ) • iteratedDeriv 2 (f ∘ pencil x) 0=quiver f x:=by
 rw[tipLine x 0 2 (by rw[map_zero];exact g),map_zero,iteratedFDeriv_two_apply]
 rfl
structure Touch (f:E₁→ℂ)(r M:ℝ):Prop where
 paid (y):‖y‖≤r → Allows 3 f y M
 at_zero:fderiv ℝ f 0=0
namespace Touch
variable {M r:ℝ}
lemma step (p:Touch f r M)(h:‖x‖≤r):
 ‖f x-(f 0+quiver f x)‖≤ M*‖x‖^3/2 ∧ ‖f x-f 0‖≤ M*‖x‖^2:=by
 let S:=Set.Icc (0:ℝ) 1
 let U:= f ∘ pencil x
 have hz : (0:ℝ)∈ S:=Set.left_mem_Icc.mpr zero_le_one
 have hr (v)(u:v∈S):‖pencil x v‖ ≤ r:=by
   change ‖v • x‖≤_
   rw[norm_smul,Real.norm_of_nonneg u.1]; exact (mul_le_of_le_one_left (norm_nonneg _) u.2).trans h
 have he (i:ℕ) (y)(e:y∈S)(t:i ≤ 3) : ContDiffAt ℝ i U y:= ((p.paid _ (hr y e)).smooth.of_le (Nat.cast_le.mpr t)).comp y (pencil x).contDiff.contDiffAt

 have hw (i:ℕ)(t:i ≤ 3)(y)(e:y∈S): iteratedDerivWithin i U S y = iteratedDeriv i U y:=iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (he _ _ e t) e
 have hp:‖(0:E₁)‖≤r:=by rw[norm_zero];exact (norm_nonneg _).trans h
 have ht (k:ℕ)(t:k+1 ≤ 3) := taylor_mean_remainder_bound (n:=k) (C:=M*‖x‖^(k+1)) (f:=U)
    (b:=(1:ℝ)) (a:=0) zero_le_one (fun i hi=>by simpa only [Nat.cast_add,Nat.cast_one] using (he (k+1) i hi t).contDiffWithinAt) (Set.right_mem_Icc.mpr zero_le_one) (fun y u=> by
      rw [hw _ t y u]
      have hf:=p.paid _ (hr y u)
      rw [show U=f ∘ pencil x from rfl,tipLine x y (k+1) (hf.smooth.of_le (Nat.cast_le.mpr t))]
      have hg := (iteratedFDeriv ℝ (k+1) f (pencil x y)).le_opNorm_mul_prod_of_le (m:=fun _=>x) (b:=fun _=>‖x‖) (fun _=>le_rfl)
      exact hg.trans (by simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (hf.norm_le _ t) (by positivity)))
 have hi: iteratedDeriv 1 U 0=0:=by
   have h': ContDiffAt ℝ 1 f (pencil x 0):=by rw[map_zero]; exact (p.paid _ hp).smooth.of_le (by norm_num)
   unfold U; rw[tipLine x 0 1 h',map_zero,iteratedFDeriv_one_apply,p.at_zero];rfl

 have h0 : iteratedDeriv 0 U 0=f 0:=by rw[iteratedDeriv_zero]; unfold U; rw[Function.comp_apply,map_zero]
 have h1 : U 1=f x:=by change f ((1:ℝ) • x)=_;rw[one_smul]
 constructor
 · have e:= ht 2 le_rfl
   rw[taylor_within_apply,sum_range_succ,sum_range_succ,sum_range_one,
       hw 0 (by decide) _ hz, hw 1 (by decide) _ hz,hw 2 (by decide) _ hz,h0,hi,h1] at e
   norm_num [Nat.factorial] at e
   rw[←pencil_shiver ((p.paid _ hp).smooth.of_le (by norm_num:(2:ℕ∞ω)≤ (↑(3:ℕ):ℕ∞ω))) x]
   rw[Complex.real_smul, Complex.ofReal_inv,Complex.ofReal_ofNat,←one_div]
   exact e
 · have e:=ht 1 (by decide)
   rw[taylor_within_apply,sum_range_succ,sum_range_one,
       hw 0 (by decide) _ hz, hw 1 (by decide) _ hz,h0,hi,h1] at e
   simpa [Nat.factorial] using e


lemma self (p:Touch f r M)(h:0<r):
  ContDiffAt ℝ 2 f 0:=
  (p.paid 0 (by rw[norm_zero];exact h.le)).smooth.of_le (by norm_num)
lemma limit (p:Touch f r M) (h:0<r)(x:E₁):
  Tendsto (fun t:ℝ=> t⁻¹^2 • (f (t • x)-f 0)) (𝓝[>] 0) (𝓝 (quiver f x)):=by
 have hh: Tendsto (fun t:ℝ=>M*t*‖x‖^3/2) (𝓝[>] 0) (𝓝 0):=by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_; rw[show (0:ℝ)=M*0*‖x‖^3/2 by ring] -- rewrites nhds x
    simpa using (show ContinuousAt (fun t:ℝ=>M*t*‖x‖^3/2) 0 from by fun_prop).tendsto
 have hv:∀ᶠ y:ℝ in 𝓝 0, ‖y • x‖≤r:= (show ContinuousAt (fun y:ℝ=>‖y • x‖) 0 from by fun_prop).eventually (ge_mem_nhds (by simpa using h : ‖(0:ℝ) • x‖ < r))
 have hz : Tendsto (fun t:ℝ=> t⁻¹^2 • (f (t • x)-f 0)-quiver f x) (𝓝[>] 0) (𝓝 0):=by
   refine squeeze_zero_norm' ?_ hh
   filter_upwards [eventually_nhdsWithin_of_eventually_nhds hv, self_mem_nhdsWithin] with t u w

   have e:0<t:=w
   have hx:=mul_le_mul_of_nonneg_left (p.step u).1 (sq_nonneg (t⁻¹))
   have he:t⁻¹^2*t^2=1:=by rw [inv_pow, inv_mul_cancel₀ (by positivity)]
   rw [←Real.norm_of_nonneg (sq_nonneg (t⁻¹)), ← norm_smul] at hx
   rw[smul_sub, smul_add, trembling, smul_smul,he,one_smul, Real.norm_of_nonneg (sq_nonneg (t⁻¹))] at hx
   rw [norm_smul t, Real.norm_of_nonneg e.le] at hx
   rw[smul_sub,←sub_add_eq_sub_sub]; exact hx.trans_eq (by field_simp)
 simpa using hz.add_const (quiver f x)

end Touch
variable {N:Side}{d D r:ℝ}
lemma touch{F:Plank N d}{S:Sa N}{C:Toll (Single N)}
    (p:Twine 3 d D r)(g:Essay S C F):
 Touch (picL F) r (D*ledgerV C):=⟨fun x h=>(p.pay _ g x h).1,pic_grad g ((p.pay _ g 0 (by simp [p.rp.le])).1.smooth.differentiableAt (by norm_num))⟩

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.Touch.step
