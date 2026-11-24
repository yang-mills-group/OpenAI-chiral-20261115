import YM.CF.Buffered.Applause
/-! parameter dependencies. Receipts in terms of the nonlinear clock do impose inequalities
on its sizes. Here arithmetic on choosing θ and finally buying at large printed counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter Lattice Wilson RG Pressure Burn
open scoped Topology BigOperators
variable (B q:Side)
def priceθ : ℝ := Real.log 2/(2*((3/2:ℝ)^4)*( (Vale.cell q B B 0).val:ℝ)^4)
lemma priceθ_p : 0<priceθ B q:=by unfold priceθ; positivity
lemma authorize (a b:ℝ): ∀ᶠ w:Side in atTop, (3/2:ℝ)^4*(priceθ B q*((Vale.cell q B B 0).val:ℝ)^4*w.val^4+a) ≤ Real.log 2*w.val^4 ∧ b ≤ (2:ℝ)^(w.val^4) := by
 rw [eventually_atTop]; have hR:0<Real.log 2:=Real.log_pos (by norm_num)
 obtain ⟨n,u⟩:= exists_nat_gt (2*(3/2)^4*a/Real.log 2); obtain ⟨t,v⟩:= exists_nat_gt b
 refine ⟨⟨n+t+1,by omega⟩,fun x h=>?_⟩; let w:= x.val; have hx:n+t+1≤w:=h; have hp:w ≤ w^4:=by nth_rw 1 [←pow_one w]; exact pow_le_pow_right₀ x.property (by omega)
 constructor
 · unfold priceθ; rw [show Real.log 2/(2*(3/2:ℝ)^4*_) * ((Vale.cell q B B 0).val:ℝ)^4= Real.log 2/(2*(3/2:ℝ)^4) by field_simp]; have he : (n:ℝ)≤(x.val:ℝ)^4:=by exact_mod_cast (show n≤ x.val^4 by change n≤ w^4; omega)
   have hu:= (div_lt_iff₀ hR).1 u; norm_num1 at u hu ⊢; nlinarith only [hu,mul_le_mul_of_nonneg_right he hR.le]
 have ht:(t:ℝ) ≤ (↑(x.val^4):ℝ) := by exact_mod_cast (le_trans (show t≤w by omega) hp)
 refine v.le.trans (ht.trans ?_); generalize x.val^4=k; have he:= one_add_mul_le_pow (show -2 ≤ (1:ℝ) by norm_num) k; norm_num at he; linarith

variable {K:Calibration}{P:SpanCal K}{e:ℝ}
lemma authorization (p: Venue P e)(J:Tiling K)(t:p.θ=priceθ K.B J.d')(x: ((Filter.eventually_atTop.mp (authorize K.B J.d' (plusV p) (creditA p+1))).choose≤ J.qcount K.q)) : (3/2:ℝ)^4 * season p J ≤ Real.log 2*(clicks J K.q) ∧ creditA p+1 ≤ (2:ℝ)^(clicks J K.q) := by
 obtain ⟨s,v⟩:= (Filter.eventually_atTop.mp (authorize K.B J.d' (plusV p) (creditA p+1))).choose_spec (J.qcount K.q) x; refine ⟨?_,v⟩; unfold season; rw [t]; convert s using 1
 · rw [mul_assoc (priceθ ..)]; rw [←mul_pow]; congr 4; have hp :  (K.c K.q).val=(Vale.cell J.d' K.B K.B 0).val*(J.qcount K.q).val:=by unfold Calibration.c Vale.cell Cube.CSide Vale.mesh; simp [Cube.More]; nth_rw 1 [J.ruler K.q (big_one K)]; simp; ring
   exact_mod_cast hp
 simp only [clicks,Nat.cast_pow]
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.authorization
