import YM.CF.Cubes.Thick

/-! Actual uniform interpolation, global conditions needed for positivity. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U : Bkg (Domain m B)} {e d : ℝ}
abbrev DenseA (N : Side) := Site N → Vect

def paintV (m B : Side) (U : Bkg (Domain m B)) (s : ArrayF m) (q : Sq) : DenseA (Domain m B) := fun z=> ren (paint m B U s q z)
def enoughV (B : Side) (e d : ℝ) := pot B e*7≤low/2 ∧
    4/low * (14*(1/(width B:ℝ) + 3*pot B e)) < d
lemma turn_ren (g : E) (x : Vect) : turn g (ren x)=ren (turn g x) := by rw [ren, turn_mul,ren,turn_norm]
lemma ren_near {x y : Vect} (hx : low/2≤‖x‖) (hy : low/2≤‖y‖) : ‖ren x-ren y‖≤4/low * ‖x-y‖ := by
  have hl := low_p
  have hs : 0<‖x‖ := by linarith
  have ht : 0<‖y‖ := by linarith
  let i := ‖x‖; let j := ‖y‖
  have h : ‖ren x-ren y‖ ≤ (‖x-y‖ + |j-i|)/i := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (i⁻¹ • y) _).trans
    change ‖i⁻¹ • x-i⁻¹ • y‖ + ‖i⁻¹ • y-j⁻¹ • y‖≤_
    rw [←smul_sub,←sub_smul,norm_smul,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hs).le,Real.norm_eq_abs]
    have H : i>0 := hs; have G : j>0 := ht
    rw [show i⁻¹-j⁻¹=(j-i)/(j*i) by field_simp, abs_div, abs_of_nonneg (mul_nonneg G.le H.le)]
    change i⁻¹ * ‖x-y‖ + _*j≤_
    apply le_of_eq; field_simp
  have he := abs_norm_sub_norm_le y x; rw [norm_sub_rev] at he
  apply h.trans; rw [div_le_iff₀ hs]
  apply le_trans (show _ ≤ ‖x-y‖+‖x-y‖ from add_le_add_right he _)
  have hm : 0 ≤ 4/low*‖x-y‖ := by positivity
  apply le_trans _ (mul_le_mul_of_nonneg_left hx hm); apply le_of_eq; field_simp; ring
lemma paint_unit {s : ArrayF m} {q : Sq} (g : prob q) (he : 0≤e) (h : Guard U e) {r : Finset Row}
    (hv : Verified m B margin U s r) (hs : ∀ i∉r, q i=0) (hc : enoughV B e d) (z) : ‖paintV m B U s q z‖=1 :=
  ren_norm _ (norm_pos_iff.mp ((half_pos low_p).trans_le (prism_nonzero s g he h hv hs hc.1 z)))
lemma paint_slow {s : ArrayF m} {q : Sq} (g : prob q) (he : 0≤e) (h : Guard U e) {r : Finset Row}
    (hv : Verified m B margin U s r) (hs : ∀ i∉r, q i=0) (hc : enoughV B e d) : Slow U (paintV m B U s q) d := by
  intro z i; have H := prism_nonzero s g he h hv hs hc.1
  unfold paintV; rw [turn_ren]
  apply lt_of_le_of_lt _ hc.2
  have hx : 0 ≤ 4/low := by have H := low_p; positivity
  exact (ren_near (by rw [turn_norm]; apply H) (H z)).trans (mul_le_mul_of_nonneg_left (paint_gap m B s g z he h _) hx)
lemma scalable (d : ℝ) (hd : 0<d) : ∃ o : ℕ, ∀ (B : Side), o ≤ B.val → ∃ a : ℝ, 0<a ∧ ∀ e:ℝ, e≤a → enoughV B e d := by
  have H := low_p
  obtain ⟨j,hj⟩ := exists_nat_gt (112/(d*low)); refine ⟨j+1,?_⟩; intro B hb
  have ho : 112/(d*low) < 2*(width B:ℝ) := lt_of_lt_of_le hj (by exact_mod_cast le_trans (by omega : j≤B.val) (width_big B))
  -- check 4*14=56, /width
  have he : 4/low*(14*(1/(width B:ℝ))) < d := by
    have hw : 0 < (width B:ℝ) := Nat.cast_pos.mpr (width_pos B)
    rw [div_lt_iff₀ (by positivity)] at ho; field_simp; linarith -- tune
  let f := fun a:ℝ => pot B a * 7; let g := fun a:ℝ => 4/low * (14*(1/(width B:ℝ) + 3*pot B a))
  have hf : Continuous f := by unfold f pot; fun_prop
  have hg : Continuous g := by unfold g pot; fun_prop
  have h0 : ∀ᶠ i in 𝓝[>] (0:ℝ), f i < low/2 ∧ g i < d := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    apply Filter.Eventually.and
    · exact hf.continuousAt (gt_mem_nhds (show f 0 < low/2 by simp [f,pot,H]))
    · exact hg.continuousAt (gt_mem_nhds (show g 0 < d by simpa [g,pot] using he))
  obtain ⟨a,⟨q,t⟩,u⟩ := (h0.and self_mem_nhdsWithin).exists
  have hm : Monotone (pot B) := fun x y h=>mul_le_mul_of_nonneg_left h (show 0≤320*(B.val:ℝ)^2 from by positivity)
  refine ⟨a,u,fun e k=>⟨le_trans (mul_le_mul_of_nonneg_right (hm k) (by norm_num)) q.le,?_⟩⟩
  apply lt_of_le_of_lt _ t; unfold g; gcongr; apply hm k

lemma paint_cont (m B : Side) : Continuous (fun u : Bkg (Domain m B)×ArrayF m×Sq => paint m B u.1 u.2.1 u.2.2) := by
  apply continuous_pi; intro z; unfold paint; apply continuous_finsetSum; intro i _
  have hf : Continuous (fun t : Bkg (Domain m B)×ArrayF m×Sq=> (t.1,t.2.1 i)) := continuous_fst.prodMk ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have hx : Continuous (fun t : Bkg (Domain m B)×ArrayF m×Sq=>cash m B z t.2.2 i) := (cash_cont m B z i).comp (continuous_snd.comp continuous_snd)
  let f := fun t : Bkg (Domain m B)×ArrayF m×Sq => (t.1,t.2.1 i)
  let A := fun t : Bkg (Domain m B)×ArrayF m×Sq => cash m B z t.2.2 i
  let Bx := fun t : Bkg (Domain m B) × Ballot => freight m B t.1 z i.1 t.2
  change Continuous (A • (Bx ∘ f)); exact (show Continuous A from hx).smul ((show Continuous Bx from freight_cont m B z i.1).comp (show Continuous f from hf))
lemma paintV_agree (s t : ArrayF m) (q : Sq) (h : ∀ i : Spot m, q i.2≠0 → s i=t i) (U : Bkg (Domain m B)) : paintV m B U s q=paintV m B U t q := by
  funext z; unfold paintV paint; congr 1; apply sum_congr rfl; rintro ⟨x,i⟩ _; by_cases g:q i=0
  · rw [empty_cash g, zero_smul,zero_smul]
  rw [h]; exact g
lemma paintV_at {s : ArrayF m} {q : Sq} (g : prob q) (he : 0≤e) (h : Guard U e) {r : Finset Row}
    (hv : Verified m B margin U s r) (hs : ∀ i∉r, q i=0) (hc : enoughV B e d) :
    ContinuousAt (fun u : Bkg (Domain m B)×ArrayF m×Sq=> paintV m B u.1 u.2.1 u.2.2) (U,s,q) := by
  apply continuousAt_pi.mpr; intro z
  let f := fun u : Bkg (Domain m B)×ArrayF m×Sq=>paint m B u.1 u.2.1 u.2.2 z
  have hy : f (U,s,q) ≠0 := norm_pos_iff.mp ((half_pos low_p).trans_le (prism_nonzero s g he h hv hs hc.1 z))
  exact (ren_cont _ hy).comp (show ContinuousAt f _ from ((continuous_apply z).comp (paint_cont m B)).continuousAt)
end YM.CF.Cube
