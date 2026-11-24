import YM.SU5.FiniteGaugeData.ArchiveK.Ports
import Mathlib.LinearAlgebra.Vandermonde
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
attribute [local instance] opCStarAlgebra
open Violas LightK MeasureTheory.Measure
variable {D q w:ℕ} (p:Space3)
namespace Midway
section geometry
variable (D q w:ℕ)
abbrev hornC (D:ℕ):ℝ:= τ/D
abbrev Helix(D:ℕ): Set Space3:= suiteC Tang 0 (hornC D)
def hiveV(D:ℕ):= MeasureTheory.volume.restrict (Helix D)
def fleet (w:ℕ): Zpo w≃ Pix w := Fintype.equivOfCardEq (by simp [Pix,Zpo,Tang])
def frostT(j:Zpo w):Tang→ℤ:= 1+ ground (fleet w j)
def arrowX(i:Zpo w):Space3:= songQ (hornC D) (frostT w i)
abbrev lobby (D:ℕ):= (hornC D)^3
variable {D q w}
lemma first_frost : Injective (frostT w):= fun i j hv=> (fleet w).injective (ground_in (add_left_cancel hv)) -- note add_left_cancel vs right? tune
lemma horn_p(u:0<D) : 0< hornC D:=div_pos tau_pos (Nat.cast_pos.mpr u)
lemma lobby_p (u:0<D):0< lobby D:=pow_pos (horn_p u) _
lemma heist(u:0<D): IsFiniteMeasure (hiveV D):=by constructor; rw [hiveV, Measure.restrict_apply_univ,snowPay 0 _ (horn_p u)]; finiteness
lemma gem(u:0<D) : MeasureTheory.volume (Helix D)= ENNReal.ofReal (lobby D):=by rw [snowPay 0 _ (horn_p u)]; rfl -- card
lemma gem_r(u:0<D) : MeasureTheory.volume.real (Helix D)= lobby D:=by rw [Measure.real,gem u]; simp [ENNReal.toReal_ofReal (lobby_p u).le]
lemma verdant (u:0<D) : Injective (arrowX D w):= by
 intro i j p; apply first_frost; funext a; suffices h:( (frostT w i a:ℤ):ℝ) = ((frostT w j a:ℤ):ℝ) by exact_mod_cast h
 exact mul_left_cancel₀ (horn_p u).ne' (congrArg (fun p:Space3=> p a) p) -- tune
lemma budget_Q (u:0<D)(t:0<w)(h:p∈Helix D)(i:Zpo w): let q:=arrowX D w i; p+q ≠ 0 ∧ ‖p+q‖ ≤32*(w:ℝ)/D:=by
 intro q; obtain hp:=horn_p u; let s:=hornC D*((w:ℝ)+1); have he(i':Tang):0 < (p+q).ofLp i' ∧ (p+q).ofLp i' ≤ s:=by
    let k:=(fleet w i) i'; have ht:(k.val:ℝ)<w:= Nat.cast_lt.mpr k.isLt; have hr:(k.val:ℝ)+1≤w:= by exact_mod_cast (Nat.succ_le_of_lt k.isLt);
    have hz:= (in_snow ..|>.mp h) i'; change 0< p i'+hornC D*↑(1+(k.val:ℤ):ℤ) ∧ _ ≤_; push_cast; have hw:0≤ p i' ∧ p i' < 0+hornC D:= hz; change _ ∧ p i'+hornC D*((↑(1+(k.val:ℤ):ℤ)):ℝ) ≤_; push_cast; unfold s; constructor; nlinarith only [hw.1,hp, mul_nonneg hp.le (Nat.cast_nonneg (α:=ℝ) k.val)]; nlinarith only [hw.2,mul_le_mul_of_nonneg_left hr hp.le]
 have hs:0≤s:=by unfold s; positivity
 refine ⟨fun h=> (he 0).1.ne (by rw [h]; rfl) |>.elim, ?_⟩; -- ne expects 0=v
 have hx: ‖p+q‖ ≤2*s:=by rw [←sq_le_sq₀ (norm_nonneg _) (by positivity),EuclideanSpace.real_norm_sq_eq]; apply (sum_le_sum (g:=fun _=> s^2) (fun i _=>pow_le_pow_left₀ (he i).1.le (he i).2 2)).trans; simp [SpaceAxis]; nlinarith [sq_nonneg s]
 apply hx.trans; have hy: τ ≤ 8:=(by unfold τ; linarith [Real.pi_lt_four]); have hm:0<(D:ℝ):=Nat.cast_pos.mpr u; have hk:1 ≤ (w:ℝ):=Nat.one_le_cast.mpr t; unfold s hornC; field_simp; nlinarith only [hy,hk,mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg (α:=ℝ) w)] -- tune
-- ae distinct energies of different aliases. hyperplane.Price.
lemma branches (x y:Space3)(t:x≠y): ∀ᵐ p:Space3, ‖p+x‖≠‖p+y‖ := by
 let f:= innerSL ℝ (x-y); let Uq:= (MeasureTheory.volume : Measure Space3); let u:Space3:=(2:ℝ)⁻¹ • (x+y); let g(p:Space3):= p+u; let T:= (LinearMap.ker f.toLinearMap); have hv:( x-y:Space3) ≠ 0:= sub_ne_zero.mpr t
 have ht:∀ᵐ p ∂Uq,p∉T:=by
    rw [ae_iff]; simp only [not_not]; apply Measure.addHaar_submodule (s:=T) Uq; intro h; have hx:x-y∈ T:=by rw [h]; trivial
    change inner ℝ (x-y) (x-y)=0 at hx; exact hv (inner_self_eq_zero.mp hx)
 have hh: ∀ᵐ p ∂Uq,g p∉T:=(measurePreserving_add_right Uq u).quasiMeasurePreserving.ae ht; refine hh.mono fun p t e=>t ?_; unfold T; change inner ℝ (x-y) (p+u)=0; unfold u; have hz:= congrArg (·^2) e; rw [norm_add_sq_real, norm_add_sq_real] at hz; rw [inner_add_right,real_inner_smul_right, inner_add_right,inner_sub_left,inner_sub_left,inner_sub_left, real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]; -- sym.B
    nlinarith only [hz, real_inner_comm x p, real_inner_comm y p, real_inner_comm x y]
lemma budget_K (v:0<D) (p:0<w) : ∃ Z:Set Space3,Z⊆Helix D∧ IsCompact Z∧ lobby D*(3/4:ℝ)≤ MeasureTheory.volume.real Z∧ ∀ x∈Z,Injective (fun i:Zpo w=> ‖x+ arrowX D w i‖):=by
 let U:=Helix D; let V(i j:Zpo w):= {p:Space3| ‖p+arrowX D w i‖ ≠ ‖p+arrowX D w j‖}; let T:=⋂ i:Zpo w,⋂ j:Zpo w, ⋂ (_:i≠j), V i j
 have hv:∀ᵐ p:Space3,p∈T:=by simp only [T,Set.mem_iInter]; exact ae_all_iff.mpr fun a => ae_all_iff.mpr fun b=> ae_all_iff.mpr fun h=> branches _ _ ((verdant v).ne h)
 have hV:MeasurableSet T:= MeasurableSet.iInter (fun i=>MeasurableSet.iInter (fun j=>MeasurableSet.iInter (fun p=> (isOpen_ne_fun (by fun_prop) (by fun_prop)).measurableSet))); let Z:=U∩T; have hz: MeasureTheory.volume Z=ENNReal.ofReal (lobby D):= (measure_congr (μ:=MeasureTheory.volume) (s:=Z) (t:=U) (hv.mono fun x hx=> propext (and_iff_left hx))).trans (gem v); have he:MeasurableSet Z:= (snowC 0 (hornC D)).inter hV; obtain ⟨z,h,p,h'⟩:= he.exists_lt_isCompact_of_ne_top (μ:=MeasureTheory.volume) (by rw [hz]; finiteness) (r:= ENNReal.ofReal (lobby D * (3/4:ℝ))) (by rw [hz, ENNReal.ofReal_lt_ofReal_iff (lobby_p v)]; nlinarith only [lobby_p v]); -- order tune
 refine ⟨z,h.trans Set.inter_subset_left,p, ?_, fun t g i j v=>by by_contra k; exact (Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp (h g).2 i) j) k) v⟩
 unfold Measure.real; exact (ENNReal.ofReal_le_iff_le_toReal (p.measure_lt_top.ne)).1 h'.le
-- harmonic tag. σ.R.
local notation "∆"=> ‖p‖
variable {x:Set Space3}
def aim (D:ℕ)(j:Tang→ℤ)(p:Space3): ℂ:=coastE (inner ℝ p (songQ (D:ℝ) j)) -- = songT (hornC D)...
lemma aim_eq (u:0<D) (Z:Tang→ℤ) : aim D Z p=songT (hornC D) Z p:= by unfold aim songT hornC; rw [show τ/(τ/↑D)= (D:ℝ) from (by have he:=tau_pos; have ht:0<(D:ℝ):=Nat.cast_pos.mpr u; field_simp)]
@[simp] lemma aim_cash (D:ℕ)(Z:Tang→ℤ): ‖aim D Z p‖=1:=coast_pay _
@[fun_prop] lemma aim_c(D:ℕ)(Z:Tang→ℤ) : Continuous (aim D Z):= by unfold aim; fun_prop
lemma aimed (D:ℕ)(Y Z:Tang→ℤ) : aim D Y p*star (aim D Z p)= aim D (Y-Z) p:= by
 unfold aim; rw [coast_inv,← coast_add]; refine congrArg _ ?_; rw [show songQ (D:ℝ) (Y-Z)= songQ (D:ℝ) Y - songQ D Z from ?_, inner_sub_right]; ring; apply PiLp.ext; intro; simp [songQ, mul_sub]
local notation "δ"=> hornC D
lemma turner (i:Zpo w) (h:0<D)(Z:Tang→ℤ): aim D Z (p+arrowX D w i) = aim D Z p:=by
 unfold aim; rw [inner_add_left,coast_add]; suffices h: coastE (inner ℝ (arrowX D w i) (songQ (D:ℝ) Z))=1 by simp [h];
 let v:= frostT w i; let k:=∑ i:Tang,v i*Z i; have he: inner ℝ (arrowX D w i) (songQ (D:ℝ) Z)=τ*k:=by
    unfold arrowX; rw [PiLp.inner_apply]; unfold k songQ; push_cast; rw [mul_sum]; apply sum_congr rfl; intro j _; change inner ℝ (δ*(v j)) ((D:ℝ)* Z j)= _; unfold hornC; simp only [RCLike.inner_apply]; have hm:starRingEnd ℝ ((τ / (D:ℝ))*v j)=(τ / D)*v j:=rfl; rw [hm]; have hx:0<(D:ℝ):= Nat.cast_pos.mpr h; field_simp
 rw [he]; apply Complex.exp_eq_one_iff.mpr; refine ⟨k,?_⟩; unfold τ; push_cast; ring
-- Vandermonde on Good.
def basset (D:ℕ)(p:Space3):ℝ:= Real.exp (-(D:ℝ)*‖p‖)
@[fun_prop] lemma basset_c : Continuous (basset D):=by unfold basset; fun_prop
def WicketL (D w:ℕ)(p:Space3):Op (Zpo w):= Matrix.vandermonde (fun i:Zpo w=> ((basset D (p+arrowX D w i)):ℂ))
#check continuous_matrix
lemma wicket_c : Continuous (WicketL D w):= by apply continuous_matrix; intro i j; unfold WicketL; simp_rw [Matrix.vandermonde_apply]; fun_prop
lemma wicket_Z (h:0<D)(t:Injective (fun i:Zpo w=>‖p+arrowX D w i‖)): (WicketL D w p).det≠0:= by
 refine Matrix.det_vandermonde_ne_zero_iff.mpr fun i j e=>t (mul_left_cancel₀ (a:= -(D:ℝ)) (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr h.ne')) (Real.exp_injective (Complex.ofReal_injective e)))
lemma wicket_pay (H:IsCompact x)(u:0<D)(h:∀ p∈x,Injective (fun i:Zpo w=>‖p+arrowX D w i‖)): ∃ c:ℝ,0<c∧∀ p∈x,∀ v:Ket (Zpo w),c*‖v‖ ≤ ‖ract (WicketL D w p) v‖:=by
 let f:=WicketL D w; have hi: ContinuousOn (fun x=> (f x)⁻¹) x:= by intro p hp; let A:= f p; exact ((continuousAt_matrix_inv A (by rw [show Ring.inverse (M₀:=ℂ)=Inv.inv from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ (wicket_Z _ u (h p hp)))).comp (wicket_c (D:=D) (w:=w)).continuousAt).continuousWithinAt; -- tune name
 obtain ⟨q,H⟩:=(H.image_of_continuousOn hi).isBounded.exists_norm_le; let c:= |q|+1; have hb:0<c:= by unfold c; positivity
 refine ⟨c⁻¹,inv_pos.mpr hb,fun p hp v=>?_⟩; have hk : (f p)⁻¹ *f p=1:= Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (wicket_Z p u (h p hp))); have ht:‖(f p)⁻¹‖ ≤ c:= le_trans (H _ (Set.mem_image_of_mem _ hp)) ((le_abs_self q).trans (le_add_of_nonneg_right zero_le_one)); have hm:‖v‖ ≤ c*‖ract (f p) v‖:=by refine le_trans (le_of_eq ?_) (le_trans (R_cost ((f p)⁻¹) (ract (f p) v)) (mul_le_mul_of_nonneg_right ht (norm_nonneg _))); rw [←Largo.R_mul,hk,R_one]
 exact (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hb.le)).trans_eq (inv_mul_cancel_left₀ hb.ne' _)
#print axioms wicket_pay
end geometry
end Midway
end YM.CF.Window.ArchiveK
