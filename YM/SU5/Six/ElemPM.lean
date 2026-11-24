import YM.SU5.Six.PM

/-!
# Elementary spectral multipliers

Keep track of a term in (indicators of) measurable sets in `X`
together with the corresponding term in projections.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Spectral.PVM
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ComplexConjugate

variable {H : Hilbert} {X : Type*} [MeasurableSpace X]
         {f g : X → ℂ} {T U : H.Op} {P : PVM H X}

inductive Elementary (P : PVM H X) : (X → ℂ) → H.Op → Prop where
  | ind {s : Set X} (hs : MeasurableSet s) :
      Elementary P (s.indicator fun _ => 1) (P.region s)
  | plus {f g T U : _} (h : Elementary P f T) (k : Elementary P g U) :
      Elementary P (f+g) (T+U)
  | scale {f T : _} (c : ℂ) (h : Elementary P f T) :
      Elementary P (c•f) (c•T)

namespace Elementary

lemma represents (h : P.Elementary f T) : P.Represents f T := by
  induction h with
  | ind hs => exact represents_indicator P _ hs
  | plus _ _ A B => exact A.add B
  | scale _ _ A => exact A.smul _

lemma zero_elem (P : PVM H X) : P.Elementary 0 0 := by
  have h : P.Elementary _ (P.region ∅) := ind .empty
  rw [P.none, indicator_empty] at h; exact h


lemma minus (h : P.Elementary f T) : P.Elementary (-f) (-T) :=
  neg_one_smul ℂ T ▸ neg_one_smul ℂ f ▸ scale (-1) h
lemma diff (h : P.Elementary f T) (k : P.Elementary g U) : P.Elementary (f-g) (T-U) := by
  rw [sub_eq_add_neg f g, sub_eq_add_neg T U]
  exact plus h k.minus

lemma mul_ind (h : P.Elementary f T) {s : Set X} (hs : MeasurableSet s) :
    P.Elementary (f*(s.indicator fun _ => 1)) (T*(P.region s)) := by
  induction h with
  | @ind a ha =>
    let j(t : Set X) := t.indicator fun _ => (1:ℂ)
    have he : j a*j s=j (a∩s) := by ext x; by_cases p:x∈a <;> by_cases q:x∈s <;> simp [j,p,q]
    change P.Elementary (j a * j s) ((P.region a).comp _)
    rw [he,P.joins ha hs]
    exact ind (ha.inter hs)
  | plus _ _ A B => rw [_root_.add_mul,_root_.add_mul]; exact plus A B
  | scale _ _ A => rw [smul_mul_assoc,smul_mul_assoc]; exact scale _ A
lemma mul (h : P.Elementary f T) (k : P.Elementary g U) : P.Elementary (f*g) (T*U) := by
  induction k with
  | ind hs => exact mul_ind h hs
  | plus _ _ A B => rw [mul_add,mul_add]; exact plus A B
  | scale _ _ A => rw [mul_smul_comm,mul_smul_comm]; exact scale _ A

private lemma conj_any (h : P.Elementary f T) : ∃ U, P.Elementary (fun x => conj (f x)) U := by
  induction h with
  | @ind s hs =>
    let j := s.indicator fun _ => (1:ℂ)
    have he : (fun x => conj (j x)) = j := by ext x; by_cases p:x∈s <;> simp [j,p]
    change ∃ _, P.Elementary (fun x => conj (j x)) _
    rw [he]; exact ⟨_, ind hs⟩
  | @plus f g _ _ _ _ A B =>
    obtain ⟨T,A⟩ := A; obtain ⟨U,B⟩ := B
    have he : (fun x => conj ((f+g) x)) = ((fun x => conj (f x))+(fun x => conj (g x))) :=
      funext fun _ => map_add _ _ _
    rw [he]; exact ⟨_, plus A B⟩
  | @scale f _ c _ A =>
    obtain ⟨T,A⟩ := A
    have he : (fun x => conj ((c•f) x)) = (conj c) • (fun x => conj (f x)) :=
      funext fun _ => map_mul _ _ _
    rw [he]; exact ⟨_,scale _ A⟩

lemma conjugate (h : P.Elementary f T) : P.Elementary (fun x => conj (f x)) T.adjoint := by
  obtain ⟨U,a⟩ := conj_any h
  rw [h.represents.conjugate.unique a.represents]; exact a
lemma sum {ι : Type*} (s : Finset ι) (f : ι → X → ℂ) (T : ι → H.Op)
    (h : ∀ i ∈ s, P.Elementary (f i) (T i)) :
    P.Elementary (∑ i ∈ s, f i) (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero_elem P
  | insert i s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact plus (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

lemma norm_le (h : P.Elementary f T) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC fun x => ?_
  have hi : ‖inner ℂ x ((T.adjoint*T) x)‖ = ‖T x‖^2 := by
    change ‖inner ℂ x (T.adjoint (T x))‖ = _
    rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
    simp
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [← hi,(h.conjugate.mul h).represents.on_diag, _root_.mul_pow,
      ← show (P.diagonal x).real Set.univ = ‖x‖^2 by rw [P.same .univ,P.all]; rfl]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun i => ?_)
  simpa only [Pi.mul_apply, norm_mul, Complex.norm_conj, ← sq] using
    (pow_le_pow_left₀ (norm_nonneg (f i)) (hf i) 2)

end Elementary
end YM.Spectral.PVM
