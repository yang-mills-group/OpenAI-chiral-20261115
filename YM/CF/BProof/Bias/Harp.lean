import YM.CF.BProof.Bias.Muse
/-! Local choice of two momenta, no ultraviolet or period purchases in the aperture.
 Quantitative version of nonrepresentability of pole by the putative split under
 eq:nogapz. Any polynomial degree dependent on (fixed) D. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {s c C:ℝ} {j:ℕ}(h:1≤j)
lemma sample (v:0<s)(u:2*s<π) : ∃ k:ℕ,∀ N:Side,k≤N.val→∃ x:Per N,s ≤ principal x ∧ principal x ≤ 2*s:=by
 -- pick floor then ceil sampler index
 obtain ⟨k,r⟩:= exists_nat_gt (4*π/s); refine ⟨k,fun N g=>?_⟩; let n:ℝ:= N.val; have he := r.trans_le (show (k:ℝ)≤n from Nat.cast_le.mpr g); let i:=⌈s*n/(2*π)⌉₊; have hk:0<n:=nPos N; have hx:= Real.pi_pos; have hh:s*n/(2*π) ≤ ↑i:= Nat.le_ceil _; have hp:(i:ℝ) < s*n/(2*π)+1:= Nat.ceil_lt_add_one (by positivity)
 have hL:s ≤ (2*(i:ℝ)+1)*π/n:= by rw [le_div_iff₀ (by positivity)]; rw [div_le_iff₀ (by positivity:0<2*π)] at hh; nlinarith only [hh,hx]
 have hU: (2*(i:ℝ)+1)*π/n ≤ 2*s:=by rw [div_le_iff₀ hk]; rw [← sub_lt_iff_lt_add,lt_div_iff₀ (by positivity:0<2*π)] at hp; rw [div_lt_iff₀ v] at he; nlinarith only [hp,he,hx]
 have hi:(i:ℝ)<n:= by apply lt_of_mul_lt_mul_right _ hx.le; -- tune
                              have hp:=div_lt_iff₀ hk |>.1 (hU.trans_lt u); nlinarith only [hp,hx, Nat.cast_nonneg (α:=ℝ) i,mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) hx.le] -- i*n orientation
 have hW:winding (i:Per N)= (2*(i:ℝ)+1)*π/n:=by unfold winding; rw [ZMod.val_natCast_of_lt (by unfold n at hi; exact_mod_cast hi)]; unfold n; ring
 refine ⟨i,?_⟩; rw [Lat.principal,hW,if_pos (hU.trans u.le)]; exact ⟨hL,hU⟩
variable {K:ℝ}
def Scale(j:ℕ)(K:ℝ):Prop:=1 ≤ K ∧ ∀ {N:Side}(M:Male)(x:Site N), (‖pm x‖/K)^2 ≤ hat j M x ∧ hat j M x≤ (K* ‖pm x‖)^2
include h
lemma scaleP : ∃ K:ℝ,Scale j K:=by
 obtain ⟨c,C,e,f,Q⟩:=Fig.feed h; obtain ⟨K,k,k1,k2⟩ :∃ K:ℝ,1≤K ∧ (sqrt c)⁻¹ ≤ K∧ sqrt C≤ K:=⟨max (max 1 ((sqrt c)⁻¹)) (sqrt C),(le_max_left ..).trans (le_max_left ..),(le_max_right ..).trans (le_max_left ..),le_max_right ..⟩; have hp:=one_pos.trans_le k; refine ⟨K,k,?_⟩; intro N M x; let z:=‖pm x‖; have hv:0≤z:=norm_nonneg _
 constructor
 · rw [div_eq_mul_inv]; apply le_trans ?_ (Q x M).2.2 -- tune
   have hk:K⁻¹≤sqrt c:=by have ht:= inv_anti₀ (by positivity:0<(sqrt c)⁻¹) k1; rwa [inv_inv] at ht -- tune
   apply (pow_le_pow_left₀ (mul_nonneg hv (inv_nonneg.mpr hp.le)) (mul_le_mul_of_nonneg_left hk hv) 2).trans; rw [mul_pow,sq_sqrt e.le]; exact le_of_eq (mul_comm ..)
 apply (Q x M).2.1.trans; rw [mul_pow]; exact mul_le_mul_of_nonneg_right ((sq_sqrt f.le).symm.le.trans (pow_le_pow_left₀ (sqrt_nonneg _) k2 _)) (sq_nonneg _)
omit h in
lemma Scale.p {x:ℝ}(S:Scale j x): 0<x:= one_pos.trans_le S.1
lemma Scale.slice {q:ℝ}(u: Scale j K)(p:0<q){N:Side}(M:Male)(x:Site N)(g:q≤ ‖pm x‖): (q/K)^2≤hat j M x∧ ‖zag j M x‖≤K/q:=by
 have he:= one_pos.trans_le u.1; have ht: (q/K)^2 ≤ hat j M x:= (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right g he.le) 2).trans (u.2 M x).1
 refine ⟨ht,(sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_⟩; rw [zag_norm j M h x]; apply (sub_le_self _ zero_le_one).trans; refine (inv_anti₀ (by positivity) ht).trans ?_; rw [←inv_pow,inv_div]
lemma Scale.flare {q:ℝ}(u:Scale j K)(p:0<q){N:Side}(M:Male)(x:Site N)(t: ‖pm x‖ ≤ q): (K*q)⁻¹-1 ≤ ‖zag j M x‖:=by
 rw [sub_le_iff_le_add]; have hp:= one_pos.trans_le u.1; have he:hat j M x ≤ (K*q)^2:=by apply (u.2 M x).2.trans; gcongr
 apply (sq_le_sq₀ (by positivity) (by positivity)).1; rw [inv_pow]; nlinarith only [zag_norm j M h x,norm_nonneg (zag j M x), inv_anti₀ (hat_p j M h x) he]
end YM.CF.BProof.Bias
