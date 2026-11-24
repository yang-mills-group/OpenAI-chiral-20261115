import YM.CF.BProof.Charge.Boss

/-! severe weights: uniform suppression. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Form Angular Angular.Yard AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {s:Side} (Y:Yard s)(M:ℕ)(l:Tile s)(Z:Finset Y.Col)
variable (U:Config G s)(b:Y.Col)

private lemma range_cost {i:TAxis} (d:ℕ)(r:ℝ)(h:∀ c:Fin Y.short, cd G (U (Y.side (b,c,i))) (U (Y.inter (b,c,i))) ≤ r)(k:d≤Y.short):
    cd G (U (horiz (Y.dEnd b.1) b.2 i)) (U (horiz (Y.atD b.1 d) b.2 i))≤d*r:= by
 induction d with
 | zero=> rw [atD_zero,cd_self,Nat.cast_zero,zero_mul]
 | succ d ih=>
   apply le_trans (cd_triangle G _ (U (horiz (Y.atD b.1 d) b.2 i)) _); exact (add_le_add (ih (by omega)) (h ⟨d,k⟩)).trans_eq (by push_cast; ring)
abbrev lower (d:ℕ)(κ:ℝ) := κ/(2*d)
lemma lower_pos {d:ℕ}(k:0<d){κ:ℝ}(h:0<κ): 0<lower d κ:=by unfold lower; positivity
variable {κ y:ℝ}{S:Hall s}{F:Y.FaceS}
lemma bridge (v:b∈Y.severe κ y U)(u:2*xi y≤ κ*thresh y)(e:Y.Climate y S U F): ∃ i:Y.Apt, lower Y.short κ * thresh y< SU.group.chord (faceValue U (Y.rise (b,i))) := by
 obtain ⟨⟨j,i⟩,h⟩:= (Y.wind κ y U b).1 v; let a:=b.1; let p:=b.2; let z:=U (horiz (Y.dEnd a) p i); have hp: cd G (bg y i) z≤xi y := by
   unfold z dEnd; split<;>rename_i H
   · exact haven Y y S U F e a H (horiz (Y.v a) p i) ((wet_h _ _).2 (Y.u_in a).le)
   exact haven Y y S U F e (a+1) ((Y.next _).2 H) (horiz (Y.u (a+1)) p i) ((wet_h _ _).2 (by simp))
 let r:=lower Y.short κ * thresh y; have ht:0<thresh y:= coin_pos ..; have hk: 0<κ:= pos_of_mul_pos_left (by linarith [show 0<xi y from coin_pos ..] : 0<κ*thresh y) ht.le -- tune
 have hr:0<r:=mul_pos (lower_pos Y.short_pos hk) ht; by_contra! H
 have hv(l:Fin Y.short): cd G (U (Y.side (b,l,i))) (U (Y.inter (b,l,i)))≤r:=by rw [cd_symm, ← rise_h Y (b,l,i) U e.flat]; exact H (l,i)
 have hx:=range_cost Y U b (j.val+1) r hv j.isLt
 have hu : Y.short*r=κ*thresh y/2:=by have ht:0<(Y.short:ℝ):=Nat.cast_pos.mpr Y.short_pos; unfold r lower; field_simp
 apply h.not_ge; unfold scaleD; have he : cd G z (U (Y.inter (b,j,i))) ≤ κ*thresh y/2:= le_trans hx ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr j.isLt) hr.le).trans_eq hu)
 rw [inter,mag_h]; refine (cd_triangle G _ z _).trans ((add_le_add hp he).trans ?_); linarith

variable (p:BudgetPoint)(T:PathData G)(c:Clip)(β:ℝ)(h:0≤β)
def plash (c:Clip)(D:ℕ)(κ:ℝ) := min (c.direct*(lower D κ)^2/2) (c.linear*lower D κ)
lemma plash_pos (d:ℕ)(p:0<d)(k:0<κ):0<plash c d κ:=by have := lower_pos p k; have := c.tail_pos; have := c.quadratic_pos; unfold plash; rw [lt_min_iff]; constructor <;>positivity
include h
lemma strength (x:Room Y M)(v:b∈Y.severe κ y U)(p':p.threshold=thresh y)(hκ:0<κ)(u:2*xi y≤κ*thresh y)(e:Y.Climate y S U F):
    plash c Y.short κ * (β*(thresh y)^2) ≤ ∑ a∈ packs Y M (Y.severe κ y U) b,heavy c p T M β U a:=by
 obtain ⟨i,hi⟩:= bridge Y U b v u e; let a:=Y.rise (b,i); let x':= SU.group.chord (faceValue U a); let t:=thresh y; let k:=lower Y.short κ; have ht:0<t:=coin_pos ..; have hk:0<k:= lower_pos Y.short_pos hκ
 apply le_trans (b:=heavy c p T M β U (.inl a)) _ (single_le_sum (fun i _=> heavy_pos c p T M β U i h) (severe_rise Y M (Y.severe κ y U) x (b,i) v)); change _≤β* PathData.clipped c p.threshold x'; have hv := c.quadratic_pos; have hp:= c.tail_pos; change k*t<x' at hi
 rw [PathData.clipped,p']; split
 · apply le_trans _ (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi.le 2) hv.le) (by norm_num)) h); apply le_trans (mul_le_mul_of_nonneg_right (min_le_left ..) (by unfold t at ht; positivity)) (le_of_eq ?_); ring -- tune
 apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi.le (mul_nonneg hp.le ht.le)) h); apply le_trans (mul_le_mul_of_nonneg_right (min_le_right ..) (by unfold t at ht; positivity)) (le_of_eq ?_); ring
end YM.CF.BProof.Charge
