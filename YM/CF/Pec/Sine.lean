/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Pec.Kent
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

section wire
open scoped Classical
variable {n : Side} {ι E F : Type} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {p : Positions ι} {N : ℕ} {y : Site n} {a α K C D : ℝ} {l : ι → Site n}
    {f g : Positions ι → E}
theorem allow_b {s : Set (Positions ι)} {r : ℕ} (h : Jet.Allows N f p C)
    (hr : Requests s f l y r) (hp : s∈𝓝 p) (ha : 0 ≤ a) : Beacon l a N f y p (C*Real.exp (a*(N*r:ℕ))) := by
  intro k hk q
  by_cases he : ∀ i, separation y (l (q i)) ≤ r
  · have hz : spanSites l y q ≤ N*r := (Finset.sum_le_sum (g:=fun _ => r) (fun j _ => he j)).trans
      (by simp [Nat.mul_le_mul_right r hk])
    rw [mul_assoc, ← Real.exp_add]
    refine ((entry_bound q).trans (h.norm_le _ hk)).trans (le_mul_of_one_le_right h.nonneg (Real.one_le_exp ?_))
    have ht : (spanSites l y q:ℝ) ≤ ((N*r:ℕ):ℝ) := by exact_mod_cast hz
    linarith [mul_le_mul_of_nonneg_left ht ha]
  push Not at he
  obtain ⟨i,hi⟩ := he
  rw [hr.zero hp (h.smooth.of_le (by exact_mod_cast hk)) q i (not_le.mpr hi), norm_zero]; have := h.nonneg; positivity


lemma beacon_b (hf : ContDiffAt ℝ N f p) (hg : ContDiffAt ℝ N g p) (h : Beacon l a N f y p C) (h' : Beacon l a N g y p D) :
    Beacon l a N (fun x => f x + g x) y p (C+D) := by
  intro k hk q
  rw [show Push.Uniform.entry (fun x => f x+g x) p q = Push.Uniform.entry f p q+Push.Uniform.entry g p q from by
    unfold Push.Uniform.entry; rw [show (fun x => f x+g x) = f+g from rfl, iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk))]; rfl,add_mul]
  exact (norm_add_le ..).trans (add_le_add (h _ hk _) (h' _ hk _))

lemma beacon_S {α:Type} {s : Finset α} {C : α → ℝ} {f : α → Positions ι → E}
    (h : ∀ i∈s, Beacon l a N (f i) y p (C i)) (he : ∀ i∈s, ContDiffAt ℝ N (f i) p) : Beacon l a N (fun z => ∑ i∈s, f i z) y p (∑ i∈s, C i) := by
  induction s using Finset.induction with
  | empty => intro k hk q; simp [Push.Uniform.entry]
  | insert i s hi ih =>
    have ht j (hj : j∈s) := he j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi]
    exact beacon_b (he i (Finset.mem_insert_self ..)) (ContDiffAt.sum ht) (h i (Finset.mem_insert_self ..)) (ih (fun _ hj => h _ (Finset.mem_insert_of_mem hj)) ht)

end wire
section
variable {ι σ τ π : Type} [Fintype ι] [Fintype τ]
    {n : Side} {N k K : ℕ} {p : Positions τ}
    {l : ι → Site n} {m : τ → Site n} {a r C D : ℝ}

lemma beacon_g {g : Positions ι → Positions τ} {x : Positions ι} {u : Site n} {f : Positions τ → ℝ}
    (hF : ContDiffAt ℝ N f (g x)) (hg : ContDiffAt ℝ N g x) (ha : 0<a) (hr : 0<r) (hc : 0 ≤ C) (hd : 0 ≤ D)
    (h : Beacon m a N f u (g x) C) (H : Envelope l m r N g x D) (hm : Multiplicity m K) :
    Beacon l (litSpan N r a) N (f ∘ g) u x (C * machinist N K D a) := by
  intro k hk q
  let F := ftaylorSeries ℝ f (g x)
  let P := ftaylorSeries ℝ g x
  let v (j : Fin k) := Push.Uniform.bolt (q j)
  let R := glaze l u q (litSpan N r a)
  let Z := D*((K:ℝ)*countCost (a/2))
  have hZ : 0 ≤ Z := by have ht := count_pos (half_pos ha); unfold Z; positivity
  have he (s : OrderedFinpartition k) : ‖(F.compAlongOrderedFinpartition P s) v‖ ≤ C * (1+Z)^N * R := by
    have hu := wire_cost (p:=x) (f:=g) (g:=f) q s hk ha hr hc hd u hm
      (fun i (hi:i≤k) t => h i (hi.trans hk) t)
      (fun i j => H _ (s.partSize_pos i).ne' ((s.partSize_le i).trans hk) _ j)
    apply hu.trans; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hc) (Real.exp_pos _).le
    exact (pow_le_pow_left₀ hZ (le_add_of_nonneg_left zero_le_one) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right hZ) (s.length_le.trans hk))
  unfold Push.Uniform.entry; rw [iteratedFDeriv_comp hF hg (by exact_mod_cast hk), FormalMultilinearSeries.taylorComp,_root_.sum_apply]
  refine le_trans ((norm_sum_le ..).trans (Finset.sum_le_sum (fun j _ => he j))) ?_
  rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
  have hh : (Fintype.card (OrderedFinpartition k):ℝ) ≤ partitionsBill N := Finset.single_le_sum
    (f:=fun i => (Fintype.card (OrderedFinpartition i):ℝ)) (fun i _ => Nat.cast_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_add_one_of_le hk))
  apply (mul_le_mul_of_nonneg_right hh (mul_nonneg (by positivity) (Real.exp_pos _).le)).trans_eq
  unfold Z machinist; ring

lemma beacon_complex {g : Positions ι → Positions τ} {x : Positions ι} {u : Site n} {f : Positions τ → ℂ}
    (hF : ContDiffAt ℝ N f (g x)) (hg : ContDiffAt ℝ N g x) (ha : 0<a) (hr : 0<r) (hc : 0 ≤ C) (hd : 0 ≤ D)
    (h : Beacon m a N f u (g x) C) (H : Envelope l m r N g x D) (hm : Multiplicity m K) :
    Beacon l (litSpan N r a) N (f ∘ g) u x (2*(C * machinist N K D a)) := by
 have he(i:Bool): Beacon m a N (matte i ∘ f) u (g x) C:=by
    intro k hk q; apply le_trans (b:=‖Push.Uniform.entry f (g x) q‖) _ (h k hk q); unfold Push.Uniform.entry; rw [(matte i).iteratedFDeriv_comp_left hF (by exact_mod_cast hk)]; let z:=Push.Uniform.entry f (g x) q; change ‖matte i z‖≤‖z‖; cases i; exact Complex.abs_im_le_norm _; exact Complex.abs_re_le_norm _
 have hp(i:Bool):= beacon_g ((matte i).contDiff.contDiffAt.comp _ hF) hg ha hr hc hd (he i) H hm; intro k hk q; let z:= Push.Uniform.entry (f∘g) x q; have he(i):Push.Uniform.entry (matte i ∘f ∘g) x q=matte i z:=by unfold Push.Uniform.entry; rw [(matte i).iteratedFDeriv_comp_left (hF.comp x hg) (by exact_mod_cast hk)]; rfl
 apply (show ‖z‖ ≤ ‖matte true z‖+‖matte false z‖ from Complex.norm_le_abs_re_add_abs_im _).trans; rw [←he true,←he false]; apply (add_le_add (hp true k hk q) (hp false k hk q)).trans_eq; ring
end
end YM.CF.Pec
