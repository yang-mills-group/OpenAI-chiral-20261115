import YM.CF.Vp929.Analysis.Pivot
import YM.CF.Jet.Stokes
import Mathlib.Analysis.Calculus.TaylorIntegral

/- Holomorphy of charged jets: no differentiating jointly over the hidden rough variables,
no topping up the order. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.VolumeRate
open Metric Set Function Complex Filter Topology
open scoped ContDiff
lemma normal_limit {F:ℕ→ℂ→ℂ}{G:ℂ→ℂ}{S:Set ℂ}{M:ℝ}(h:IsOpen S)(hq:0≤ M)(v:∀ᶠ n in atTop,DifferentiableOn ℂ (F n) S ∧ ∀ z∈ S, ‖F n z‖ ≤ M)(t:∀ z∈S,Tendsto (fun n=> F n z) atTop (𝓝 (G z))): DifferentiableOn ℂ G S:=by
 intro z p; obtain ⟨r,hr,b⟩:=Metric.mem_nhds_iff.mp (h.mem_nhds p); let T(a:ℂ):=z+a; have hu: Differentiable ℂ T:= (differentiable_const _).add differentiable_id; have hx: MapsTo T (ball 0 r) S:=by intro k x; apply b; simpa [T,Metric.mem_ball,dist_eq_norm] using x
 have hv:= normal_subseq (half_lt_self hr) (fun (_:Unit) n=> F n ∘ T) (fun _=> M) (fun _ => hq) (fun _=> v.mono fun n a=> ⟨a.1.comp hu.differentiableOn hx,fun z t=> a.2 _ (hx t)⟩)
 obtain ⟨φ,v',H⟩:= hv; obtain ⟨g,tg,ug,-⟩:=H (); let L:=ball (0:ℂ) (r/2); have ht:DifferentiableOn ℂ (G ∘ T) L:= ug.congr fun x k => tendsto_nhds_unique ((t (T x) (hx (ball_subset_ball (half_le_self hr.le) k))).comp v'.tendsto_atTop) (tg.tendsto_at (ball_subset_closedBall k))
 let e:= ht.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))
 have H:DifferentiableAt ℂ G z:= by
    conv in G => rw [show G= (G ∘ T) ∘ (fun x=> -z+x) from funext (fun x=>by simp only [comp_apply,T,add_neg_cancel_left])]
    apply DifferentiableAt.comp _ _ ((differentiable_const _).add differentiable_id|>.differentiableAt); simpa using e
 exact H.differentiableWithinAt
/- note shifted line witnesses buy `rank_pi`, uniform `lime`. -/
lemma jet_p {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f:ℂ→E→ℂ}{S:Set ℂ}{L:Set E}{C:ℝ}{n:ℕ}(hs:IsOpen S)(hl:IsOpen L)(hc:0≤C)(h:∀ x∈L,DifferentiableOn ℂ (fun z=> f z x) S)(p:∀ z∈S,∀ x∈L,Jet.Allows n (f z) x C) (j:ℕ)(A:j≤n)(x:E)(hx:x∈L)(v:Fin j→E): DifferentiableOn ℂ (fun z=> iteratedFDeriv ℝ j (f z) x v) S:=by
 classical
 induction j generalizing x with
 | zero=> simpa using h x hx
 | succ i ih=>
    let G(z:ℂ)(w:ℝ):= iteratedFDeriv ℝ i (f z) (x+w • v 0) (Fin.tail v)
    let H(z:ℂ)(w:ℝ):= iteratedFDeriv ℝ (i+1) (f z) (x+w • v 0) v
    have e:Differentiable ℝ (fun w:ℝ=> x+w • v 0):= by fun_prop
    obtain ⟨s,hs',q⟩:=Metric.mem_nhds_iff.mp ((hl.preimage e.continuous).mem_nhds (show (0:ℝ)∈(fun w:ℝ=>x+w • v 0)⁻¹' L from by simp only [mem_preimage,zero_smul,add_zero,hx]))
    let D:= C*∏ k: Fin (i+1), ‖v k‖; have hd:0≤D:=by unfold D; positivity
    have he(w)(t:w∈ball (0:ℝ) s)(z)(tz:z∈ S): HasDerivAt (G z) (H z w) w:=by
       let hp:= (p z tz _ (q t)).smooth.differentiableAt_iteratedFDeriv (m:=i) (by exact_mod_cast A)
       have hh:= ((hp.continuousMultilinear_apply_const (Fin.tail v)).comp w (e.differentiableAt (x:=w)))
       refine hh.hasDerivAt.congr_deriv ?_; unfold comp; rw [(hp.continuousMultilinear_apply_const _).deriv_comp_add_smul]; exact hp.iteratedFDeriv_succ_apply_left'.symm
    obtain ⟨φ,pφ⟩:= Filter.exists_seq_tendsto (𝓝[>] (0:ℝ))
    let F(n:ℕ):= fun z:ℂ=> slope (G z) 0 (φ n)
    refine (normal_limit hs hd (F:=F) ?_ ?_: DifferentiableOn ℂ (fun z=>H z 0) S).congr (fun z _=> by simp [H])
    · filter_upwards [pφ (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℝ) hs')),pφ self_mem_nhdsWithin] with j p0 pj
      have p₁:0 < φ j:= pj; change φ j ∈ ball (0:ℝ) s at p0; have h₀: (0:ℝ)∈ball (0:ℝ) s:=mem_ball_self hs'; have hb: Icc 0 (φ j) ⊆ ball (0:ℝ) s:= (convex_ball (0:ℝ) s).ordConnected.out h₀ p0
      refine ⟨(((ih (by omega) _ (q p0) (Fin.tail v)).sub (ih (by omega) _ (q h₀) (Fin.tail v))).const_smul _), fun z t=>?_⟩
      have h:= norm_image_sub_le_of_norm_deriv_le_segment' (fun x k=>(he x (hb k) z t).hasDerivWithinAt) (fun x k=> (((iteratedFDeriv ℝ (i+1) (f z) _ ).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((p z t _ (q (hb (Ico_subset_Icc_self k)))).norm_le _ A) (by positivity)): ‖H z x‖ ≤ D)) _ (right_mem_Icc.mpr p₁.le)
      unfold F slope; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact (inv_mul_le_iff₀ (sub_pos.mpr p₁)).mpr (h.trans_eq (mul_comm ..))
    intro z t; exact (he 0 (mem_ball_self hs') z t|>.tendsto_slope).comp ((nhdsWithin_mono _ (show Set.Ioi (0:ℝ) ⊆ {(0:ℝ)}ᶜ from fun x p=> (show x ≠ 0 from (Set.mem_Ioi.mp p).ne'))) |> pφ.mono_right)
end YM.CF.VolumeRate
