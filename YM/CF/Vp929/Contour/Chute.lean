import YM.CF.Vp929.Analysis.Shooting
import YM.CF.Vp929.Contour.Gradient
import YM.CF.Vp929.Contour.Form
/-! Internal fixed point in wave max norm. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Set Topology Bornology
open scoped NNReal ContDiff ComplexConjugate
variable {E : Type*}[NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V:Set (Pair E)}{G:Pair E→ Pair E}{K:ℝ≥0}{r d:ℝ}{s:Set ℂ} (hr:0<r)
namespace Chute
abbrev linF (z:ℂ)(x:Pair E):Pair E := (z.re • x.1-z.im • x.2,z.re • x.2+z.im • x.1)
@[simp] lemma linF_zero (x:Pair E) : linF 0 x=0:=by simp [linF]
@[simp] lemma linF_one (x:Pair E) : linF 1 x=x:=by simp [linF]
lemma blades (z:ℂ)(x:Pair E): ‖linF z x‖≤ 2*‖z‖*‖x‖:=by
 have he(u:E)(t:ℝ)(q:‖u‖≤‖x‖)(g:|t|≤‖z‖): ‖t • u‖≤ ‖z‖*‖x‖:=by rw [norm_smul,Real.norm_eq_abs]; gcongr
 have hf:= norm_fst_le x; have ht:=norm_snd_le x; have hp:= Complex.abs_re_le_norm z; have hd:= Complex.abs_im_le_norm z; apply max_le; exact (norm_sub_le ..).trans ((add_le_add (he _ _ hf hp) (he _ _ ht hd)).trans_eq (by ring)); exact (norm_add_le ..).trans ((add_le_add (he _ _ ht hp) (he _ _ hf hd)).trans_eq (by ring))
abbrev prism (p:E→L[ℝ]ℝ):Pair E →L[ℝ] ℂ := by
 let A:= (Complex.ofRealCLM.comp p).comp (ContinuousLinearMap.fst ℝ E E); let B:= (Complex.ofRealCLM.comp p).comp (ContinuousLinearMap.snd ℝ E E); exact A + Complex.I • B
lemma prism_eta (p:E→L[ℝ]ℝ)(X:Pair E):prism p X=probing p X:=rfl
lemma east_p {p:E→L[ℝ]ℝ}(w:‖p‖≤1)(x:Pair E): ‖prism p x‖ ≤ 2*‖x‖:=by
 have hp(y:E)(a:‖y‖≤‖x‖):‖(p y:ℂ)‖≤‖x‖:=by rw [Complex.norm_real]; exact ((p.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) w)).trans a
 refine (norm_add_le ..).trans (le_trans (b:=‖x‖+‖x‖) ?_ (le_of_eq (by ring))); refine add_le_add (hp _ (norm_fst_le x)) ?_; change ‖Complex.I • (p x.2:ℂ)‖ ≤ ‖x‖; rw [norm_smul,Complex.norm_I,one_mul]; exact hp _ (norm_snd_le x)
lemma entry0 (x:Pair E)(h:∀ p:E→L[ℝ]ℝ, ‖p‖≤1→‖prism p x‖≤ d): ‖x‖ ≤ d:=by
 obtain ⟨p,hp,z⟩:= exists_dual_vector'' ℝ x.1; obtain ⟨q,hq,v⟩:= exists_dual_vector'' ℝ x.2; change p x.1=‖x.1‖ at z; change q x.2=‖x.2‖ at v; have ht:= Complex.abs_re_le_norm (prism p x); have hx:= Complex.abs_im_le_norm (prism q x); rw [prism_eta,prob_re,z,abs_of_nonneg (norm_nonneg _)] at ht; rw [prism_eta,prob_im,v,abs_of_nonneg (norm_nonneg _)] at hx; exact max_le (ht.trans ((by rw [←prism_eta]; exact h p hp))) (hx.trans ((by rw [←prism_eta]; exact h q hq)))
abbrev runV (u v:Pair E)(z:ℂ): Pair E:= u+linF z v
lemma paid (u v: Pair E) : Form s (runV u v) := (form_const s u).add ((form_const s v).scale differentiableOn_id)
variable {x y:Pair E}(h:∀ x∈ ball (0:Pair E) r,‖G x‖≤ r/128)
include hr h
local notation "Vh"=> closedBall (0:Pair E) (r/2)
lemma littleV : MapsTo G Vh Vh := fun _ p=> mem_closedBall_zero_iff.mpr ((h _ (closedBall_subset_ball (by linarith:r/2<r) p)).trans (by linarith))
lemma contract_form (A:∀ (Z:Set ℂ) (u:ℂ→ Pair E),IsOpen Z→MapsTo u Z (ball 0 r)→ Form Z u → Form Z (G ∘ u)): LipschitzOnWith (1/2:ℝ≥0) G Vh:=by
 apply LipschitzOnWith.of_dist_le_mul; intro x px y py
 push_cast; rw [dist_eq_norm, dist_eq_norm]
 by_cases b:x=y
 · subst x; simp
 let ξ:= ‖x-y‖; have hb:0<ξ:=norm_pos_iff.mpr (sub_ne_zero.mpr b)
 let R:=r/(4*ξ); have hh:0<R:=by unfold R; positivity
 let T:=r/(8*ξ); have ht:0<T:=by unfold T; positivity
 let u:=runV y (x-y); let X:=ball (0:ℂ) R
 have H : MapsTo u X (ball 0 r):=by
    intro z t; have hp:= mem_ball_zero_iff.mp t; refine mem_ball_zero_iff.mpr (lt_of_le_of_lt (norm_add_le ..) ?_); have ht':2*‖z‖*ξ<r/2:=by apply lt_of_lt_of_le (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hp (by norm_num : (0:ℝ)<2)) hb); unfold R; field_simp; norm_num
    exact (add_lt_add_of_le_of_lt (mem_closedBall_zero_iff.mp py) ((blades z (x-y)).trans_lt ht')).trans_eq (by ring)
 by_cases p':r/16≤ξ
 · apply (norm_sub_le ..).trans; exact (add_le_add (h x (closedBall_subset_ball (by linarith:r/2<r) px)) (h y (closedBall_subset_ball (by linarith:r/2<r) py))).trans (by change _≤1/2*ξ; linarith only [hr,p'])
 refine entry0 _ fun p t=>?_ ; rw [map_sub]; let F(z:ℂ):=prism p (G (u z)); have hm:(1:ℂ)∈ball 0 T:= mem_ball_zero_iff.mpr (show ‖(1:ℂ)‖ < T from (by
   rw [norm_one]; apply (lt_div_iff₀ (mul_pos (by norm_num) hb : 0 < 8*ξ)).mpr; push_neg at p'; linarith))
 have ht':‖F 1-F 0‖ ≤ 2*(r/128)/T * ‖(1:ℂ)-0‖:= pay_diff (A X u isOpen_ball H (paid y (x-y)) p) (fun z a=> (east_p t (G (u z))).trans (mul_le_mul_of_nonneg_left (h _ (H a)) (by norm_num))) (mem_ball_self ht) hm ht (by unfold T R; field_simp; ring_nf; first|linarith|skip)
 unfold F u at ht'; simp [runV,show y+(x-y)=x from by abel] at ht'; refine ht'.trans ?_; change _≤ 1/2*ξ; unfold T; field_simp; linarith
omit hr h
variable [CompleteSpace E] {x: Pair E}{F: ℂ→ Pair E→ Pair E}(hm : ∀ z ∈ s, MapsTo (F z) V V) (l : ∀ z ∈ s,LipschitzOnWith K (F z) V) (hk:K < 1)(hv:x∈ V)
include hk hv hm l
lemma fix_form (hs : IsOpen s) (hc : IsClosed V) (hb : Bornology.IsBounded V)
    (hd : ∀ g : ℂ → Pair E, MapsTo g s V → Form s g → Form s (fun z=> F z (g z))) :
    ∃ g : ℂ → Pair E, Form s g ∧ ∀ z ∈ s, g z ∈ V ∧ IsFixedPt (F z) (g z) ∧
         (∀ w ∈ V, IsFixedPt (F z) w → w = g z) ∧ Tendsto (fun i : ℕ=> (F z)^[i] x) atTop (𝓝 (g z)) := by
  classical
  let X : V := ⟨x,hv⟩; letI : Nonempty V := ⟨X⟩; letI : CompleteSpace V := hc.completeSpace_coe
  let G (z : s) (y : V) : V := ⟨F z y, hm z z.prop y.prop⟩
  have Y (z : s) : ContractingWith K (G z) := ⟨hk, LipschitzWith.of_dist_le_mul fun x y=> (l z z.prop).dist_le_mul _ x.prop _ y.prop⟩
  let g (z : ℂ) := if e : z ∈ s then ((Y ⟨z,e⟩).fixedPoint (G ⟨z,e⟩)).val else x
  let φ (n : ℕ) (z : ℂ) := (F z)^[n] x
  have hx (z : s) (n) : φ n z = ((G z)^[n] X : Pair E) := by
    unfold φ; induction n with | zero=> rfl | succ n ih=> rw [iterate_succ_apply',iterate_succ_apply',ih]
  have hd' (n : ℕ) : Form s (φ n) := by
    induction n with
    | zero => exact form_const _ _
    | succ n ih => unfold φ; simp only [iterate_succ_apply']; exact hd (φ n) (fun z p => (hm z p).iterate _ hv) ih
  have hU : TendstoUniformlyOn φ g atTop s := by
    simp_rw [Metric.tendstoUniformlyOn_iff]
    let b:= diam V; have l':= NNReal.coe_lt_coe.mpr hk
    have he : Tendsto (fun i:ℕ=> b * (K:ℝ)^i / (1-(K:ℝ))) atTop (𝓝 0) := by
      simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one K.prop l').const_mul b).div_const (1-(K:ℝ)))
    intro ε hp; filter_upwards [he.eventually (gt_mem_nhds hp)] with i p z h; rw [dist_comm, hx ⟨z,h⟩ i]
    have H:= (Y ⟨z,h⟩).apriori_dist_iterate_fixedPoint_le X i; unfold g; rw [dif_pos h]
    refine lt_of_le_of_lt (H.trans ?_) p; change _ ≤ b*_/(1-K:ℝ); gcongr
    · exact dist_le_diam_of_mem hb hv (G ⟨z,h⟩ X).prop
  refine ⟨g,fun p=> ((prism p).uniformContinuous.comp_tendstoUniformlyOn hU|>.tendstoLocallyUniformlyOn).differentiableOn (Eventually.of_forall (fun n=>(hd' n p))) hs,fun z p=> ⟨?_,?_,?_,hU.tendsto_at p⟩⟩
  all_goals simp only [g,p,↓reduceDIte]
  · exact Subtype.prop _
  · exact congrArg Subtype.val (show G ⟨z,p⟩ _ = _ from (Y ⟨z,p⟩).fixedPoint_isFixedPt)
  intro w hw P; exact congrArg Subtype.val ((Y ⟨z,p⟩).fixedPoint_unique (show IsFixedPt (G ⟨z,p⟩) ⟨w,hw⟩ from Subtype.ext P))
end Chute
end YM.CF.Py.Rate
