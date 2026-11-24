import YM.SU5.Selected.Cylinder
/-! Vector preparations on the compact ABI of phase selection. Proof uses concrete representation supporting χ internally, not selecting a positive probability event from X. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Emplacement
open Function Set Filter NormedSpace CStarAlgebra Spectral OS
open scoped InnerProductSpace NNReal ENNReal BigOperators ComplexOrder Classical Topology
variable {H : Hilbert} {B:StarSubalgebra ℂ H.Op}[StarOrderedRing B][IsClosed (B : Set H.Op)] (χ : B →⋆ₐ[ℂ] ℂ)
private lemma diagonal (T:Finset B) {ε:ℝ}(p:0<ε)(w:H)(u:‖w‖=1): ∃ v:H, ‖v‖=1∧∀ a∈T, ‖(a:B).val v-(χ a) • v‖ ≤ ε:=by
 classical
 let f(a:B): B:=a-(χ a) • 1
 let K(a:B):=star (f a)*f a; let e:B:=(ε:ℂ) • 1; let z:= ∑ a ∈ T,K a
 have he: χ z=0:= by simp [z,K,f]
 have hc:¬ star e * e ≤ z:= by
   intro h; have hp: χ (star e*e) ≤ χ z:= OrderHomClass.mono χ h
   rw [he,map_mul,map_star] at hp; have hx:χ e=(ε:ℂ):=by rw [show e=(ε:ℂ) • (1:B) from rfl,map_smul,map_one, smul_eq_mul,mul_one]
   rw [hx] at hp; simp only [Complex.star_def,Complex.conj_ofReal, ← Complex.ofReal_mul] at hp
   exact not_le.mpr (mul_pos p p) (Complex.le_def.mp hp).1
 have hw(a:B)(v:H):(f a).val v=a.val v-(χ a) • v:=rfl
 have hz(v:H) : inner ℂ (z.val v) v= ((∑ a ∈ T,‖(f a).val v‖^2:ℝ):ℂ) := by
    have hd(a:B) : inner ℂ ((K a).val v) v= ((‖(f a).val v‖^2:ℝ):ℂ):= by
      change inner ℂ ((f a).val.adjoint ((f a).val v)) v = _
      rw [ContinuousLinearMap.adjoint_inner_left,inner_self_eq_norm_sq_to_K]; norm_cast
    unfold z
    rw [show (↑(∑ a∈T,K a):H.Op)=∑ a∈T,(K a).val from map_sum (B.subtype) _ _] -- tune
    simp_rw [ContinuousLinearMap.sum_apply, sum_inner, hd,Complex.ofReal_sum]
 have hs : ∃ x:H, ∑ a∈T,‖(f a).val x‖^2 < ‖e.val x‖^2 := by
    by_contra! h
    apply hc; change (star (e:H.Op))*(e:H.Op) ≤ z.val
    refine (ContinuousLinearMap.le_def ..|>.mpr ?_)
    have hv : IsSelfAdjoint (z.val) := (show IsSelfAdjoint z from (by unfold IsSelfAdjoint z; simp_rw [star_sum]; exact Finset.sum_congr rfl fun a _=> IsSelfAdjoint.star_mul_self (f a))).map (B.subtype)
    refine ⟨(hv.sub (.star_mul_self (e:H.Op))).isSymmetric,fun x=>?_⟩
    change 0 ≤ RCLike.re (inner ℂ (z.val x-e.val.adjoint (e.val x)) x)
    rw [inner_sub_left,hz,ContinuousLinearMap.adjoint_inner_left,map_sub,inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (h x)
 obtain ⟨x,hx⟩:=hs; have ht:x ≠ 0:= by rintro rfl; simp at hx
 have hd: 0 < (‖x‖:ℝ):= norm_pos_iff.mpr ht
 let t:ℂ:= (‖x‖⁻¹:ℝ); let v:= t • x; have h:‖t‖=‖x‖⁻¹:= by rw [show t=((‖x‖⁻¹:ℝ):ℂ) from rfl,Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
 have hy: ‖e.val x‖= ε * ‖x‖:= by change ‖(ε:ℂ) • x‖=_; rw [norm_smul,Complex.norm_real, Real.norm_eq_abs, abs_of_pos p]
 refine ⟨v,by rw [show v=t • x from rfl,norm_smul,h]; exact inv_mul_cancel₀ hd.ne',fun a ha=>?_⟩
 rw [←hw, show v=t • x from rfl,map_smul,norm_smul,h,inv_mul_le_iff₀ hd]
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
 rw [mul_comm ‖x‖, ←hy] -- tune order
 exact (Finset.single_le_sum (fun (i:B) (_:i∈T)=>sq_nonneg (‖(f i).val x‖:ℝ)) ha).trans hx.le

lemma compactAsk {X:Set B}(q:IsCompact X) {ε:ℝ}(p:0<ε)(w:H)(u:‖w‖=1): ∃ v:H, ‖v‖=1∧∀ a∈X, ‖inner ℂ v ((a:B).val v)-χ a‖ ≤ ε:=by
 let d:= ε/3; have hd : 0<d:= by unfold d; positivity
 obtain ⟨S,s,h,t⟩:= finite_cover_balls_of_compact q hd -- tune name
 obtain ⟨v,hv,g⟩:= diagonal χ h.toFinset hd w u
 refine ⟨v,hv,fun a r=>?_⟩; obtain ⟨b,e,k⟩:= mem_iUnion₂.mp (t r)
 have he:= g b (h.mem_toFinset.mpr e)
 have oneX : inner ℂ v v=1 := by rw [inner_self_eq_norm_sq_to_K,hv]; norm_num
 have hc: inner ℂ v (a.val v)-χ a= inner ℂ v (b.val v-χ b • v) + inner ℂ v ((a-b).val v)- χ (a-b):= by rw [map_sub,inner_sub_right,inner_smul_right, oneX,mul_one,show (a-b).val v=a.val v-b.val v from rfl,inner_sub_right]; abel
 have hw: ‖a-b‖≤d:= (dist_eq_norm a b) ▸ (Metric.mem_ball.mp k).le
 have hu: ‖inner ℂ v (b.val v-χ b • v)‖ ≤ d:= by
   refine (norm_inner_le_norm ..).trans ?_; rw [hv,one_mul]; exact he
 have hm:‖inner ℂ v ((a-b).val v)‖ ≤ d := by
   refine (norm_inner_le_norm ..).trans ?_; rw [hv,one_mul]; refine ((a-b).val.le_opNorm v).trans ?_; rw [hv,mul_one]; exact hw
 rw [hc]; exact (norm_sub_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add hu hm)) ((NonUnitalStarAlgHom.norm_apply_le χ _).trans hw)).trans_eq (by unfold d; ring))
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Emplacement
