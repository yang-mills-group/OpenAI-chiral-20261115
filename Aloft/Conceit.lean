import Aloft.Stair
set_option autoImplicit false
noncomputable section
namespace Zippy
open MeasureTheory Function Set Filter
open scoped Topology BigOperators ComplexConjugate Classical InnerProductSpace
variable {H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H][CompleteSpace H]
variable (K:Submodule ℂ H)(z:ℕ→H)
local notation "D"=> Submodule.orthogonal K
local notation "ζ"=> ContinuousLinearMap.id ℂ H
variable (A B:ℕ→ H→L[ℂ] H)(aA:∀i,‖A i‖ ≤1) (aB:∀i,‖B i‖ ≤1)(pA:∀u:H,Tendsto (fun i=>A i u) atTop (𝓝 u))(pB:∀u:H,Tendsto (fun i=>B i u) atTop (𝓝 u))
abbrev outΩ(i:ℕ):ℝ:=‖inner ℂ (z i) (A i (z i))‖
variable (tk:FiniteDimensional ℂ K) (v:Tendsto (fun i=>(Submodule.orthogonal K).starProjection (z i)) atTop (𝓝 0))
include aA pA tk v
lemma costumes {x:ℝ}(h:0<x):∀ᶠ d:ℕ in atTop, ‖A d (z d)-z d‖ ≤ x*‖z d‖ + 2*x:=by
 let F(i):=A i- (ζ)
 have hF(i):‖F i‖ ≤2:=by apply (norm_sub_le ..).trans; linarith only [aA i, ContinuousLinearMap.norm_id_le (𝕜:=ℂ) (E:=H)]
 have ht(u:H): Tendsto (fun d=> F d u) atTop (𝓝 0):=by change Tendsto (fun d=>A d u-u) atTop (𝓝 0); simpa only [sub_self] using (pA u).sub_const u
 filter_upwards [elevator F 2 zero_le_two hF ht K x h,v.norm.eventually (ge_mem_nhds ((show ‖(0:H)‖=(0:ℝ) from norm_zero).trans_lt h))] with d k t
 have he : z d= K.starProjection (z d)+(D).starProjection (z d):=by rw [Submodule.starProjection_orthogonal]; simp
 change ‖F d (z d)‖≤ _; rw [he,map_add]
 calc _ ≤ ‖F d (K.starProjection (z d))‖ + ‖F d ((D).starProjection (z d))‖:= norm_add_le ..
      _ ≤ x* ‖K.starProjection (z d)‖+2*‖(D).starProjection (z d)‖ :=add_le_add (k _ (Submodule.starProjection_apply_mem K _)) (((F d).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF d) (norm_nonneg _)))
      _ ≤ x* ‖z d‖+2*x:= by gcongr; exact Submodule.norm_starProjection_apply_le K _
      _ = _:=by rw [←he]
lemma distant {x:ℝ}(h:0<x) : ∀ᶠ i:ℕ in atTop, ‖inner ℂ (z i) (A i (z i))-((‖z i‖^2:ℝ):ℂ)‖ ≤ x*(‖z i‖^2+2*‖z i‖):=by
 filter_upwards [costumes K z A aA pA tk v h] with i he
 have hx:inner ℂ (z i) (z i)=((‖z i‖^2:ℝ):ℂ):=by rw [Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K _
 rw [← hx,← inner_sub_right]; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring))
lemma shape {x C:ℝ}(h:0<x)(hc:∀ᶠ i:ℕ in atTop, outΩ z A i ≤ C):∀ᶠ i:ℕ in atTop, ‖z i‖ ≤ 4+|C|:=by
 filter_upwards [distant K z A aA pA tk v (show 0 < (1:ℝ)/4 by norm_num),hc] with i he hp
 let z':=(z i); let y:=(inner ℂ z' (A i z')); let sx:=‖z'‖
 have ht:= norm_sub_norm_le ((sx^2:ℝ):ℂ) y; rw [norm_sub_rev,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg sx)] at ht
 change ‖z'‖ ≤ _; change ‖y-↑(sx^2)‖ ≤ 1/4*(sx^2+2*sx) at he; change ‖y‖ ≤ C at hp
 change sx ≤ _
 apply le_of_not_gt; intro hv
 nlinarith only [he,ht,hp,show 0 ≤ sx from norm_nonneg _,le_abs_self C, mul_nonneg (abs_nonneg C) (sq_nonneg sx), hv] -- need multiplication to dominate s² maybe `sq_pos_of_pos ..`
include aB pB
lemma curls (C:ℝ)(hc:∀ᶠ i:ℕ in atTop, outΩ z A i ≤ C): ∀x:ℝ,0<x → ∀ᶠ i:ℕ in atTop, |outΩ z A i - outΩ z B i| ≤x:=by
 let s:=4+|C|; have hs:0<s:=by unfold s; linarith only [abs_nonneg C]
 intro x h; let b:=s^2+2*s; have hb:0<b:=by unfold b; positivity
 let ξ:=x/(2*b); have hξ:0<ξ:=by unfold ξ; positivity
 filter_upwards [shape K z A aA pA tk v h hc,distant K z A aA pA tk v hξ,distant K z B aB pB tk v hξ] with i c k g
 let y:= ‖z i‖; let r:=((y^2:ℝ):ℂ); let p:=inner ℂ (z i) (A i (z i)); let q:=inner ℂ (z i) (B i (z i)); have he:y^2+2*y ≤ b:=by unfold b; gcongr    -- tune
 exact (abs_norm_sub_norm_le p q).trans ((norm_sub_le_norm_sub_add_norm_sub p r q).trans (by rw [norm_sub_rev r]; change ‖p-r‖ ≤ ξ*(y^2+2*y) at k; change ‖q-r‖ ≤ ξ*(y^2+2*y) at g; have hx:2*(ξ*b)=x:=(by unfold ξ; field_simp); linarith only [k.trans (mul_le_mul_of_nonneg_left he hξ.le),g.trans (mul_le_mul_of_nonneg_left he hξ.le),hx]))
#print axioms curls
#check inner_self_eq_norm_sq_to_K
end Zippy
