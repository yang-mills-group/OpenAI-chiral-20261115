import Bay.D.Conifer
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

namespace C
open D hiding quiver
open Exterior Precision Nacre
open scoped ContDiff


variable {E₁:Type}[NormedAddCommGroup E₁][NormedSpace ℝ E₁]{f:E₁→ℂ}{x:E₁}

variable {T G r M:ℝ}{m:ℕ}

lemma swaying (p:∀ y,‖y‖≤r→Allows 2 f y M)(h:‖x‖≤r):
 ‖f x - (f 0+ (fderiv ℝ f 0) x)‖ ≤M*‖x‖^2:=by
 let S:=Set.Icc (0:ℝ) 1
 let U:= f ∘ pencil x
 have hz : (0:ℝ)∈ S:=Set.left_mem_Icc.mpr zero_le_one
 have hr (v)(u:v∈S):‖pencil x v‖ ≤ r:=by
   change ‖v • x‖≤_
   rw[norm_smul,Real.norm_of_nonneg u.1]; exact (mul_le_of_le_one_left (norm_nonneg _) u.2).trans h
 have he (i:ℕ) (y)(e:y∈S)(t:i ≤ 2) : ContDiffAt ℝ i U y:= ((p _ (hr y e)).smooth.of_le (Nat.cast_le.mpr t)).comp y (pencil x).contDiff.contDiffAt

 have hw (i:ℕ)(t:i ≤ 2)(y)(e:y∈S): iteratedDerivWithin i U S y = iteratedDeriv i U y:=iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (he _ _ e t) e
 have hp:‖(0:E₁)‖≤r:=by rw[norm_zero];exact (norm_nonneg _).trans h
 have ht (k:ℕ)(t:k+1 ≤ 2) := taylor_mean_remainder_bound (n:=k) (C:=M*‖x‖^(k+1)) (f:=U)
    (b:=(1:ℝ)) (a:=0) zero_le_one (fun i hi=>by simpa only [Nat.cast_add,Nat.cast_one] using (he (k+1) i hi t).contDiffWithinAt) (Set.right_mem_Icc.mpr zero_le_one) (fun y u=> by
      rw [hw _ t y u]
      have hf:=p _ (hr y u)
      rw [show U=f ∘ pencil x from rfl,tipLine x y (k+1) (hf.smooth.of_le (Nat.cast_le.mpr t))]
      have hg := (iteratedFDeriv ℝ (k+1) f (pencil x y)).le_opNorm_mul_prod_of_le (m:=fun _=>x) (b:=fun _=>‖x‖) (fun _=>le_rfl)
      exact hg.trans (by simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (hf.norm_le _ t) (by positivity)))
 have hi: iteratedDeriv 1 U 0=(fderiv ℝ f 0) x:=by
   have h': ContDiffAt ℝ 1 f (pencil x 0):=by rw[map_zero]; exact (p _ hp).smooth.of_le (by norm_num)

   unfold U; rw[tipLine x 0 1 h',map_zero,iteratedFDeriv_one_apply]
 have h0 : iteratedDeriv 0 U 0=f 0:=by rw[iteratedDeriv_zero]; unfold U; rw[Function.comp_apply,map_zero]
 have h1 : U 1=f x:=by change f ((1:ℝ) • x)=_;rw[one_smul]
 have e:=ht 1 (by decide)
 rw[taylor_within_apply,sum_range_succ,sum_range_one,
   hw 0 (by decide) _ hz, hw 1 (by decide) _ hz,h0,hi,h1] at e
 simpa [Nat.factorial] using e



lemma twig (k:0≤T)(u:0≤G)
 (p:∀ y,‖y‖≤T → Allows 2 f y M)
 (h:∀ y,‖y‖≤T → ‖f y‖ ≤ G*T^2) (b:0≤M):
 ‖T • fderiv ℝ f 0‖ ≤ (G*2+M)*T^2 :=by
 apply ContinuousLinearMap.opNorm_le_iff (by positivity) |>.mpr
 intro y
 by_cases hy:y=0
 · simp [hy]
 have v:=norm_pos_iff.mpr hy
 let x:=(T/‖y‖) • y
 have t:‖x‖=T:=by
   unfold x;rw [norm_smul,Real.norm_of_nonneg (div_nonneg k v.le),div_mul_cancel₀ _ v.ne']
 let z:=fderiv ℝ f 0
 have m0:‖(0:E₁)‖≤T:=norm_zero.trans_le k
 have hh:‖z x‖ ≤ (G*2+M)*T^2:=by
   have hn:z x = f x -f 0 - (f x-(f 0+z x)):=by abel
   rw[hn]
   exact (((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (h x t.le) (h _ m0)))
     ((swaying p t.le).trans_eq (by rw[t]))))).trans_eq (by ring)
 change ‖(T • z) y‖ ≤_
 rw [ContinuousLinearMap.smul_apply, show T • z y = ‖y‖ • z x by unfold x; rw [map_smul,smul_smul,mul_div_cancel₀ _ v.ne'],
 norm_smul,norm_norm,mul_comm]
 exact mul_le_mul_of_nonneg_right hh v.le

lemma swab {a:ℝ} (p:ContDiffAt ℝ m f 0) (x:Fin m→ E₁) :
 iteratedFDeriv ℝ m (fun y=> f (a • y)) 0 x=a^m • iteratedFDeriv ℝ m f 0 x:=by
 let z:E₁ →L[ℝ] E₁:=a • (ContinuousLinearMap.id ℝ _)
 obtain ⟨s,h,g,w⟩:=_root_.mem_nhds_iff.mp (p.eventually (by simp))
 have hv:=g.preimage z.continuous
 have hw:z 0∈s:=by rw[map_zero];exact w
 have jt:= z.iteratedFDerivWithin_comp_right (show ContDiffOn ℝ m f s from fun t i=> (show ContDiffAt ℝ m f t from h i).contDiffWithinAt) g.uniqueDiffOn hv.uniqueDiffOn hw (le_refl (m:ℕ∞ω))
 rw [iteratedFDerivWithin_of_isOpen _ hv hw,iteratedFDerivWithin_of_isOpen _ g hw,map_zero] at jt
 change iteratedFDeriv ℝ m (f ∘ z) _ x=_
 rw [jt,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 change iteratedFDeriv ℝ m f 0 (fun i=> (fun _:Fin m=>a) i • x i) =_
 rw [ContinuousMultilinearMap.map_smul_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma candy (k:0≤T)(v:T≤1)(u:0≤G)(a:2 ≤ m)
 (p:∀ y,‖y‖≤T → Allows m f y M)
 (h:∀ y,‖y‖≤T → ‖f y‖ ≤ G*T^2) (b:0≤M):
 Allows m (fun x=> f (T • x)) 0 ((G*2+M)*T^2):=by
 have m0:‖(0:E₁)‖≤T:=norm_zero.trans_le k
 have sm := p 0 m0
 refine ⟨(show ContDiffAt ℝ m f (T • (0:E₁)) by rw[smul_zero];exact sm.smooth).comp 0
    (contDiffAt_const.smul contDiffAt_id), fun n e=>?_⟩
 rw [show iteratedFDeriv ℝ n (fun x=>f (T • x)) 0 = T^n • iteratedFDeriv ℝ n f 0 from
    ContinuousMultilinearMap.ext fun y=>swab (sm.smooth.of_le (Nat.cast_le.mpr e)) y,
    norm_smul,Real.norm_of_nonneg (pow_nonneg k n)]
 match n with
 | 0 =>
    rw[pow_zero,norm_iteratedFDeriv_zero,one_mul]
    exact (h _ m0).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
 | 1 =>
    rw[pow_one,norm_iteratedFDeriv_one,←Real.norm_of_nonneg k, ←norm_smul,Real.norm_of_nonneg k]
    exact twig k u (fun y e=>⟨(p y e).smooth.of_le (Nat.cast_le.mpr a),fun i g=>(p y e).norm_le _ (g.trans a)⟩) h b
 | n+2 =>

    rw[mul_comm (G*2+M)]
    exact mul_le_mul (pow_le_pow_of_le_one k v (by omega)) ((sm.norm_le _ e).trans (by linarith)) (norm_nonneg _) (sq_nonneg _)
