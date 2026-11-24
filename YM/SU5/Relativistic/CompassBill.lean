import YM.SU5.Relativistic.Quintile
/-! signs: if backwards quadrant cert, match of budget -/
set_option autoImplicit false
noncomputable section
namespace YM.Signs
open Filter Function MeasureTheory Metric Set InnerProductSpace
open scoped Topology NNReal InnerProductSpace ComplexOrder
open CF.Buffered.Afterglow.Tower.Vacancy
variable {H H':Hilbert}{K:ℤ→ℤ→ℂ}
noncomputable def revW (P:Rolls H): Rolls H where
 wind s:=P.wind (-s)
 small s:= P.small _
 along r t:=by rw [P.along]; congr 1; omega
 nil:=by rw [neg_zero,P.nil]
lemma neg_quadrant (P:Rolls H) (a b:H) (z:Stock K P a b) (Q:Rolls H') (c d:H')(hp:Stock (fun m n=> K n (-m)) Q c d)(a' b':H)(hh:Stock (fun i j'=> K (-i) (-j')) P a' b') : Tendsto (fun t:ℕ×ℕ=> K (- (t.1:ℤ)) (- (t.2:ℤ))) atTop (𝓝 (inner ℂ a (P.calm b))) :=by
 have hx:= aftB P _ a b _ _ z hp
 have hy:= aftB Q P c d a' b' hp hh
 have hP: Stock (fun n m : ℤ=> (fun i j':ℤ=> K j' (-i)) m n) (revW P) a b := by
    intro ε e; apply (z ε e).mono; intro n i r; exact i (-r)
 have hu:= quadrant Q (revW P) c d a b hp hP
 have hd:Tendsto (Prod.swap:ℕ×ℕ→ℕ×ℕ) atTop atTop:= by
    rw [Filter.tendsto_atTop]; intro (i,m); filter_upwards [eventually_ge_atTop (m,i)] with w ht; exact ⟨ht.2,ht.1⟩
 have hZ:Tendsto (fun i:ℕ×ℕ=> K i.1 (-(i.2:ℤ))) atTop (𝓝 (inner ℂ c (Q.calm d))):= hu.comp hd
 rw [tendsto_nhds_unique hx hZ]; exact hy.comp hd
lemma eqneg(z:ℂ)(h:z= -z): z=0:= CharZero.eq_neg_self_iff.mp h
end YM.Signs
