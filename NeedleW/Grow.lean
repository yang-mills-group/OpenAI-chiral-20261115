import Preen.Travel
set_option autoImplicit false
noncomputable section
namespace NeedleW
open Function Filter Set YM
open scoped Topology NNReal Classical InnerProductSpace
variable{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(v:H)
-- E-inner
lemma drift(t:ℝ≥0)(y z:H)(h:S.E t z=y):(‖y‖^2:ℝ) ≤ (inner ℂ y z).re:=by
 let x:=S.E (t/2) z
 have hx: S.E t z= S.E (t/2) x:=by
    have he:=S.time (t/2) (t/2); rw [add_halves] at he; exact DFunLike.congr_fun he z
 have hu:‖y‖ ≤ ‖x‖:= h ▸ hx.symm ▸ (((S.E (t/2)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))) -- tune
 rw [←h,hx,S.swing,show inner ℂ x (S.E (t/2) z)=inner ℂ x x from rfl,inner_self_eq_norm_sq_to_K]
 change ‖S.E (t/2) x‖^2 ≤ _
 have he: (( (↑‖x‖:ℂ) ^ 2).re:ℝ)=‖x‖^2:=by rw [←Complex.ofReal_pow,Complex.ofReal_re]
 exact (pow_le_pow_left₀ (norm_nonneg _) (show ‖_‖ ≤ ‖x‖ from (hx ▸ h.symm ▸ hu)) 2).trans_eq he.symm
lemma preview(t:ℝ≥0)(y z:H)(h:S.E t z=y): ‖z-y‖^2 ≤ ‖z‖^2 - ‖y‖^2:=by
 have hp:=drift S t y z h
 have he:=norm_sub_sq (𝕜:=ℂ) y z
 rw [norm_sub_rev,he]; change (‖y‖^2-(2:ℝ)*(inner ℂ y z).re+‖z‖^2) ≤ _; linarith only [hp]
#check norm_sub_sq
#print axioms preview
-- Property backwards monotone norm while τ decreases
variable (τ:ℕ→ℝ≥0)(V:ℕ→H)(hf:∀ i j,τ i ≤ τ j→ S.E (τ j-τ i) (V i)=V j)(hs: ∀ i,0<τ i)(hz:Tendsto τ atTop (𝓝 0))
include hf
lemma norm_post{a b:ℕ}(e:τ b ≤ τ a): ‖V a‖ ≤ ‖V b‖:= (le_of_eq (congrArg norm (hf b a e).symm)).trans (((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)))
lemma norm_clip(i j:ℕ):‖V j-V i‖^2 ≤ |‖V j‖^2 -‖V i‖^2|:=by
 rcases le_total (τ i) (τ j) with h|h;
 · rw [norm_sub_rev]; exact (preview S _ (V j) (V i) (hf i _ h)).trans ((le_abs_self _).trans_eq (abs_sub_comm (‖V i‖^2) _))
 exact (preview S _ (V i) (V j) (hf j _ h)).trans (le_abs_self _)
include hs hz
lemma forwardLimit (c:ℝ)(g:∃ᶠ i in atTop,‖V i‖ ≤ c):∃ L:H, Tendsto V atTop (𝓝 L):=by
 -- get BddAbove full.True
 have p:∀i,‖V i‖ ≤ c:=by
    intro i
    obtain ⟨j,e,r⟩:= (g.and_eventually (hz.eventually (ge_mem_nhds (hs i)))).exists -- ordering e,r
    exact (norm_post S τ V hf r).trans e
 let Y:=Set.range (fun i=>‖V i‖^2)
 let k:= sSup Y
 have hY:Set.Nonempty Y:=⟨_,0,rfl⟩
 have hb:BddAbove Y:=⟨c^2,by rintro _ ⟨i,rfl⟩; exact pow_le_pow_left₀ (norm_nonneg _) (p i) _⟩
 -- eventual large.
 have ht:Tendsto (fun i=>‖V i‖^2) atTop (𝓝 k):=tendsto_order.mpr ⟨fun a h=>?_,fun b e=>?_⟩
 · exact cauchySeq_tendsto_of_complete (inscr V (norm_clip S τ V hf) k ht)
 · obtain ⟨_,⟨i,rfl⟩,t⟩:= exists_lt_of_lt_csSup hY h
   filter_upwards [hz.eventually (ge_mem_nhds (hs i))] with j e
   exact t.trans_le (pow_le_pow_left₀ (norm_nonneg _) (norm_post S τ V hf e) _)
 filter_upwards with i; exact lt_of_le_of_lt (show _ ≤ k from le_csSup hb (mem_range_self i)) e
where inscr(V:ℕ→H)(h:∀i j,‖V j-V i‖^2 ≤ |‖V j‖^2 -‖V i‖^2|)(s:ℝ)(e:Tendsto (fun i=>‖V i‖^2) atTop (𝓝 s)):CauchySeq V:=by
       apply Metric.cauchySeq_iff.mpr; intro d hd
       obtain ⟨a,r⟩:= Metric.cauchySeq_iff.mp e.cauchySeq (d^2) (pow_pos hd _)
       refine ⟨a,fun k p i q=>?_⟩
       have ht:= (h i k).trans_lt (show |‖V k‖ ^2-‖V i‖^2|< d^2 from r k p i q)
       rw [dist_eq_norm]; nlinarith only [ht,hd,norm_nonneg (V k-V i)]
#print axioms forwardLimit
end NeedleW
