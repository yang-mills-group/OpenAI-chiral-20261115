import Aloft.Conceit
import Preen.Travel
set_option autoImplicit false
noncomputable section
namespace NeedleW
open Function Filter Set Zippy
open scoped Topology NNReal Classical InnerProductSpace
variable {H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H][CompleteSpace H]
abbrev line (x:H):= Submodule.span ℂ ({x}:Set H)
abbrev clean (x:H):H→L[ℂ]H:= (Submodule.orthogonal (line x)).starProjection
lemma passive (x:H):‖clean x‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=>by rw [one_mul]; exact Submodule.norm_starProjection_apply_le _ _)
lemma projector (x:H)(y:H)(h:y∈line x): clean x y=0:= Submodule.starProjection_orthogonal_apply_eq_zero h
abbrev compL(x:H):H→L[ℂ]H:= (line x).starProjection
lemma line_member(x y:H):∃ c:ℂ,c • x=compL x y:= by
 have h:compL x y∈ line x:= Submodule.starProjection_apply_mem ..
 exact (Submodule.mem_span_singleton (R:=ℂ)).mp h
lemma line_added(x y:H): y=compL x y+clean x y:= by unfold clean compL; rw [Submodule.starProjection_orthogonal]; simp
variable (v x:ℕ→H)(k:H)(hv:Tendsto v atTop (𝓝 k))(p:k≠0)(h:Tendsto (fun i=>clean (v i) (x i)) atTop (𝓝 0))
variable (A B:ℕ→H→L[ℂ] H)(aA:∀ i,‖A i‖ ≤ 1)(aB:∀ i,‖B i‖ ≤1)(pA:∀k:H,Tendsto (fun i=> A i k) atTop (𝓝 k))(pB:∀k:H,Tendsto (fun i=> B i k) atTop (𝓝 k))
include hv p h pA aA
lemma err_linear(ε:ℝ)(e:0<ε): ∀ᶠ i:ℕ in atTop, ‖A i (x i)-x i‖ ≤ ε *‖x i‖ + 2* ε:=by
 let F(i):=A i-ContinuousLinearMap.id ℂ H
 have hF(i): ‖F i‖≤2:=by have u:=norm_sub_le (A i) (ContinuousLinearMap.id ℂ H); exact u.trans ((add_le_add (aA i) ContinuousLinearMap.norm_id_le).trans (by norm_num))
 have ht:Tendsto (fun i=>F i k) atTop (𝓝 (0:H)):=by change Tendsto (fun i=>A i k-k) atTop (𝓝 0); simpa only [sub_self] using (pA k).sub_const k
 have hD: Tendsto (fun i=> F i (v i)) atTop (𝓝 (0:H)):= rest F _ _ hF hv ht
 have ht₁:0< (‖k‖/2)*ε:=mul_pos (half_pos (norm_pos_iff.mpr p)) e -- half_pos simp? tune
 have hf:‖k‖/2 < ‖k‖:= by have hs:0<‖k‖:=norm_pos_iff.mpr p; linarith
 filter_upwards [hv.norm.eventually (le_mem_nhds hf),hD.norm.eventually (ge_mem_nhds (show ‖(0:H)‖ < _ from norm_zero.trans_lt ht₁)),h.norm.eventually (ge_mem_nhds (show ‖(0:H)‖ < _ from norm_zero.trans_lt e))] with i hv hA he
 let y:=v i; let z:=x i; obtain ⟨c,hc⟩:=line_member y z
 have hu:‖F i (compL y z)‖ ≤ ε*‖compL y z‖:=by
    rw [←hc,map_smul,norm_smul,norm_smul]; exact (mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_right hv e.le)) (norm_nonneg _)).trans_eq (by unfold y; ring)
 have hb:‖F i (clean y z)‖ ≤ 2 * ε:= ((F i).le_opNorm _).trans (mul_le_mul (hF i) he (norm_nonneg _) zero_le_two)
 change ‖F i z‖ ≤ ε*‖z‖+2*ε
 refine (le_of_eq (congrArg (fun w:H=>‖F i w‖) (line_added y z))).trans ?_
 rw [map_add]; exact (norm_add_le ..).trans (add_le_add (hu.trans (mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le (line y) z) e.le)) hb)
where rest(F:ℕ→H→L[ℂ]H)(v:ℕ→H)(k:H)(u:∀i,‖F i‖≤ 2)(t:Tendsto v atTop (𝓝 k))(r:Tendsto (fun i=>F i k) atTop (𝓝 0)):Tendsto (fun i=> F i (v i)) atTop (𝓝 0):=by
       have hz:Tendsto (fun i=> F i (v i-k)) atTop (𝓝 0):=by
          apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun i=> 2*‖v i-k‖) (fun i=> ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (u i) (norm_nonneg _))) (by simpa only [mul_zero] using (tendsto_iff_norm_sub_tendsto_zero.mp t).const_mul (2:ℝ))
       simp_rw [map_sub] at hz
       simpa only [zero_add,sub_add_cancel] using hz.add r
lemma err_dist {y:ℝ}(h₀:0<y) : ∀ᶠ i:ℕ in atTop, ‖inner ℂ (x i) (A i (x i))-((‖x i‖^2:ℝ):ℂ)‖ ≤ y*(‖x i‖^2+2*‖x i‖):=by
 filter_upwards [err_linear v x k hv p h A aA pA _ h₀] with i he
 have hx:inner ℂ (x i) (x i)=((‖x i‖^2:ℝ):ℂ):=by rw [Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K _
 rw [←hx, ←inner_sub_right]; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring))
#check @err_linear
#print axioms err_dist
lemma boundPort {y₀ C:ℝ}(h0:0<y₀)(hc:∀ᶠ i:ℕ in atTop, outΩ x A i ≤ C):∀ᶠ i:ℕ in atTop, ‖x i‖ ≤ 4+|C|:=by
 filter_upwards [err_dist v x k hv p h A aA pA (show 0 < (1:ℝ)/4 by norm_num),hc] with i he hp
 let x':=(x i); let y:=(inner ℂ x' (A i x')); let sx:=‖x'‖
 have ht:= norm_sub_norm_le ((sx^2:ℝ):ℂ) y; rw [norm_sub_rev,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg sx)] at ht
 change ‖x'‖ ≤ _; change ‖y-↑(sx^2)‖ ≤ 1/4*(sx^2+2*sx) at he; change ‖y‖ ≤ C at hp
 change sx ≤ _
 apply le_of_not_gt; intro hv
 nlinarith only [he,ht,hp,show 0 ≤ sx from norm_nonneg _,le_abs_self C, mul_nonneg (abs_nonneg C) (sq_nonneg sx), hv] -- need multiplication to dominate s² maybe `sq_pos_of_pos ..`
include aB pB
lemma curlV (C:ℝ)(hc:∀ᶠ i:ℕ in atTop, outΩ x A i ≤ C): ∀y₀:ℝ,0<y₀ → ∀ᶠ i:ℕ in atTop, |outΩ x A i - outΩ x B i| ≤y₀:=by
 let s:=4+|C|; have hs:0<s:=by unfold s; linarith only [abs_nonneg C]
 intro y₀ h0; let b:=s^2+2*s; have hb:0<b:=by unfold b; positivity
 let ξ:=y₀/(2*b); have hξ:0<ξ:=by unfold ξ; positivity
 filter_upwards [boundPort v x k hv p h A aA pA h0 hc,err_dist v x k hv p h A aA pA hξ,err_dist v x k hv p h B aB pB hξ] with i c k g
 let y:= ‖x i‖; let r:=((y^2:ℝ):ℂ); let p:=inner ℂ (x i) (A i (x i)); let q:=inner ℂ (x i) (B i (x i)); have he:y^2+2*y ≤ b:=by unfold b; gcongr    -- tune
 exact (abs_norm_sub_norm_le p q).trans ((norm_sub_le_norm_sub_add_norm_sub p r q).trans (by rw [norm_sub_rev r]; change ‖p-r‖ ≤ ξ*(y^2+2*y) at k; change ‖q-r‖ ≤ ξ*(y^2+2*y) at g; have hx:2*(ξ*b)=y₀:=(by unfold ξ; field_simp); linarith only [k.trans (mul_le_mul_of_nonneg_left he hξ.le),g.trans (mul_le_mul_of_nonneg_left he hξ.le),hx]))

#print axioms curlV
end NeedleW
