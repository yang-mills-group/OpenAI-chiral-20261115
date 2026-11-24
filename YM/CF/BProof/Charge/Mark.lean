import YM.CF.BProof.Charge.Own

/- Sup cost of gauge factor of eq:B-Mcost (without angular ball densities). Estimate before
schedule purchase; use P≤y and `weak` licenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Push.AbsoluteSums Work Micro Moment MeasureTheory Angular Angular.Yard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}{G:Gauge} (Y:Yard s)(i:Y.Index)(c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(β:ℝ)(U : Config G s)
variable {W C Λ r K:ℝ}
lemma tomb_card : (tomb Y i).card ≤ (Y.band i).card*Fintype.card PlaqAxes:= by
 apply (card_le_card (t:=Y.band i ×ˢ (univ:Finset PlaqAxes)) (fun x (h:x∈tomb Y i)=> mem_product.mpr ⟨(mem_filter.mp h).2 (four_self _),mem_univ _⟩)).trans; simp
lemma tower_card : (steeple Y i M).card≤ (Fintype.card Signed)*(Fintype.card PlaqAxes*(Y.band i).card):=by
 apply (card_le_card (t:=(univ: Finset Signed)×ˢ(univ:Finset PlaqAxes)×ˢ Y.band i) (fun x (h:x∈ steeple Y i M)=> ?_)).trans (by simp)
 obtain ⟨h,h'⟩:= (mem_filter.mp h).2; refine mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨mem_univ _,?_⟩⟩; rw [← h']; apply mem_strip.mpr; exact (Y.margin (4*M) _ h).1
lemma stable_cost (B:Bill s G)(h:B.fine r K)(hp:0≤r) : ‖∑ x∈stable Y i,B.tax x U‖≤ (Y.band i).card*K:=by
 apply (norm_sum_le ..).trans; apply (sum_le_sum (fun x hx=> B.enough x U)).trans
 apply le_trans (b:= ∑ x∈stable Y i,∑ y∈Y.band i,hit id B.amount r y x)
 · apply sum_le_sum; intro x hx; obtain ⟨⟨y,hy⟩,g⟩:= (mem_filter.mp hx).2; apply le_trans (b:=hit id B.amount r y x) _ (single_le_sum (fun z hz=> (h.pays z).1 x) (g hy)); unfold hit; simp only [id_eq,if_pos hy]; exact le_mul_of_one_le_left (B.amount_p x) (Real.one_le_exp (by positivity))
 rw [sum_comm]; apply le_trans (sum_le_sum (fun x hx=> budget_sum (h.pays x) (stable Y i))) (Eq.le ?_); simp

def mCost (c:Clip)(C β K:ℝ)(l:ℕ) : ℝ:= (l+1)*((Fintype.card PlaqAxes:ℝ)*(β*(c.direct*2))+ ((Fintype.card Signed:ℝ)*Fintype.card PlaqAxes)*(β*share*((C*2)^2/2))+K)
lemma outlay_cost (B:Bill s G)(v:0≤β)(hp:p.threshold ≤ 1)(k:T.Bounds c W C Λ)(a:0≤r)(b:B.fine r K) :
    ‖outlay Y i c p T M β U B‖ ≤ mCost c C β K Y.long*(s.val:ℝ)^3:=by
 have H : ‖∑ x∈tomb Y i,directQ c p β U x‖≤ ((Y.band i).card:ℝ)*Fintype.card PlaqAxes*(β*(c.direct*2)):=by
    have hh(x:Cell s):‖directQ c p β U x‖≤ β*(c.direct*2):= by rw [Real.norm_of_nonneg (direct_pos c p β U x v)]; exact direct_cost c p β U _ v hp
    apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=>hh i)).trans; rw [sum_const,nsmul_eq_mul]; gcongr; have := c.quadratic_pos; positivity; exact_mod_cast tomb_card Y i
 let u:= β*share*((C*2)^2/2)
 have H' : ‖∑ x∈steeple Y i M,higher c p T M β U x‖≤ ((Fintype.card Signed:ℝ)*(Fintype.card PlaqAxes:ℝ)*(Y.band i).card)*u:=by
    have hh(x:Lam s):‖higher c p T M β U x‖≤ u:=by rw [Real.norm_of_nonneg (higher_pos c p T M β U x v)]; exact higher_cost c p T M β U k x v
    apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=>hh i)).trans; rw [sum_const,nsmul_eq_mul,mul_assoc (↑(Fintype.card Signed):ℝ) (↑(Fintype.card PlaqAxes):ℝ) ((Y.band i).card:ℝ)]; gcongr; have := share_pos; unfold u; positivity; exact_mod_cast tower_card Y i M
 unfold outlay; apply (norm_add_le ..).trans; refine le_trans (add_le_add ((norm_add_le ..).trans (add_le_add H H')) (stable_cost Y i U B b a)) ?_; rw [show (Y.band i).card=(Y.long+1)*s.val^3 from strip_card _ (Y.long_lt.trans Y.count_lt)]; push_cast; apply le_of_eq; unfold u mCost; ring
end YM.CF.BProof.Charge
