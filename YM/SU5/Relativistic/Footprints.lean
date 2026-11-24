import YM.SU5.Selected.Freeze
import YM.SU5.FiniteGaugeData.Tower.Polity
-- Lattice no-alias estimate uniform all the way up the actual tower.

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction

open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open SU Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L" => Λ.R.L.val

/-- Max source coordinate radius. -/
private def large (S : Finset Cover) : ℕ := S.sup fun i => Finset.univ.sup fun a : Axis => (i a).natAbs

private lemma large_bounds (S : Finset Cover) {x : Cover} (p : x ∈ S) (a : Axis) :
    |x a| ≤ (large S : ℤ) := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast le_trans (Finset.le_sup (s:=Finset.univ) (f:=fun j : Axis => (x j).natAbs) (Finset.mem_univ a))
    (Finset.le_sup (f:=fun i : Cover => Finset.univ.sup fun a : Axis => (i a).natAbs) p)

private lemma sites_bound (Λ : Preparation) (l : ℕ) (S : Finset Cover) (n : ℕ) {x : Cover}
    (t : x ∈ volumeAround Λ l n S) (a : Axis) :
    |x a| ≤ (Λ.R.L.val : ℤ)^n * (large S + reserve Λ l : ℕ) := by
  obtain ⟨y,h,e⟩ := Tower.shield Λ l S n t
  specialize e a
  have hL : (0:ℤ) ≤ (Λ.R.L.val:ℤ)^n := by positivity
  simp only [Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.pow_apply,
    Pi.natCast_apply, Nat.cast_pow] at e
  set A : ℤ := (Λ.R.L.val:ℤ)^n with hA
  have he : - (large S : ℤ) ≤ y a ∧ y a ≤ (large S : ℤ) := abs_le.mp (large_bounds S h a)
  have ht : |x a-A*y a| ≤ A * (reserve Λ l : ℤ) := by
    rw [hA]; have hx : (0:ℤ) ≤ reserve Λ l := Nat.cast_nonneg _; linarith
  obtain ⟨hu,hv⟩ := abs_le.mp ht
  nth_rw 1 [show ((large S + reserve Λ l : ℕ):ℤ)=(large S:ℤ)+ reserve Λ l from Nat.cast_add ..]
  rw [abs_le]
  have hA₀ : 0 ≤ A := by rw [hA]; positivity
  constructor <;> nlinarith only [hu,hv,mul_le_mul_of_nonneg_left he.1 hA₀,mul_le_mul_of_nonneg_left he.2 hA₀]

private lemma tip_bound (Λ : Preparation) (l : ℕ) (S : Finset Cover) (n : ℕ) {x : Cover}
    (t : x ∈ tips (volumeAround Λ l n S)) (a : Axis) :
    |x a| ≤ (Λ.R.L.val : ℤ)^n * (large S + reserve Λ l + 1 : ℕ) := by
  let D : ℤ := (Λ.R.L.val:ℤ)^n
  have hD : 0 < D := pow_pos (by exact_mod_cast Λ.R.L.property) n
  have hk (x' : Cover) (p : x' ∈ volumeAround Λ l n S) : |x' a| + 1 ≤ D * (large S + reserve Λ l + 1 : ℕ) := by
    have ht := (show |x' a| ≤ D * (large S + reserve Λ l : ℕ) from sites_bound Λ l S n p a)
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] at ht ⊢
    omega
  rcases Finset.mem_union.mp t with z | z
  · exact le_trans (show |x a| ≤ |x a| + 1 by omega) (hk x z)
  obtain ⟨y,u,h⟩ := Finset.mem_biUnion.mp z
  obtain ⟨j,_,rfl⟩ := mem_image.mp h
  rw [Pi.add_apply, step_apply]
  specialize hk y u
  change _ ≤ D * _
  split_ifs
  · simpa only [abs_one] using (le_trans (_root_.abs_add_le (y a) (1:ℤ)) (by simpa only [abs_one] using hk))
  simp only [add_zero]; omega

/-- A host for *all* resolutions from `s` with no ambiguity even for differences.
This strengthens e.g. the `Tivoli` part of `pirouette`. -/
structure Host (i s : ℕ) (S : Finset Cover) : Prop where
  usable (n : ℕ) : Tivoli (volumeAround Λ l n S) ((tent Y H).c (momentm Y i (s+n)))
  distances (n : ℕ) (x y : Cover) (p : x ∈ tips (volumeAround Λ l n S))
    (q : y ∈ tips (volumeAround Λ l n S)) :
    Lattice.lift (wrap (More (side Y i (s+n))) x - wrap (More (side Y i (s+n))) y)=x-y

lemma eventually_host (s : ℕ) (S : Finset Cover) : ∀ᶠ i in atTop, Host Y H i s S := by
  let r := large S + reserve Λ l + 1
  filter_upwards [(SlabMark.goes Y H s).eventually (eventually_gt_atTop (4*r))] with i hi
  have hp(n : ℕ) : (4:ℤ) * ((Λ.R.L.val:ℤ)^n * r) < (More (side Y i (s+n))).val := by
    have ht : 4*r < (side Y i s).val := hi
    have h' : 4*r * L^n < (side Y i s).val * L^n := Nat.mul_lt_mul_of_pos_right ht (pow_pos Λ.R.L.property _)
    have he : 4*(L^n*r) < (More (side Y i (s+n))).val := by
      change _ < (side Y i (s+n)).val * 2
      rw [refine_side Y i s n, show (4:ℕ)*(L^n*r)=(4*r)*L^n by ring, Nat.mul_comm (L^n) (side Y i s).val]
      omega
    exact_mod_cast he
  constructor
  · intro n
    rw [terrain Y H (Y.ir i) (s+n)]
    refine ⟨⟨(wrap_injOn _).mono ?_⟩⟩
    intro x h a
    obtain ⟨hx,hx'⟩ := abs_le.mp (show |x a| ≤ (L:ℤ)^n * r from tip_bound Λ l S n h a)
    have hv:=hp n
    constructor <;> linarith
  intro n x y p q
  refine Lattice.lift_eq_iff.mpr ⟨(map_sub ..).symm, fun j=>?_⟩
  obtain ⟨hx,hx'⟩ := abs_le.mp (show |x j| ≤ (L:ℤ)^n * r from tip_bound Λ l S n p j)
  obtain ⟨hy,hy'⟩ := abs_le.mp (show |y j| ≤ (L:ℤ)^n * r from tip_bound Λ l S n q j)
  have hv := hp n
  simp only [Pi.sub_apply]; constructor <;> linarith

lemma tips_mono {S T : Finset Cover} (p : S ⊆ T) : tips S ⊆ tips T := by
  intro x h
  rcases Finset.mem_union.mp h with a|b
  · exact tips_here T (p a)
  obtain ⟨v,k,w⟩:= Finset.mem_biUnion.mp b
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,p k,w⟩)
lemma around_mono (Λ : Preparation) (l : ℕ) {S T : Finset Cover} (h : S ⊆ T) (n : ℕ) :
    volumeAround Λ l n S ⊆ volumeAround Λ l n T := by
  induction n with
  | zero => exact h
  | succ n ih => exact wingspan_mono ih
lemma Host.shrink {s i : ℕ} {S T : Finset Cover} (p : S ⊆ T) (h : Host Y H i s T) :
    Host Y H i s S := by
  have ht(n:ℕ) : tips (volumeAround Λ l n S) ⊆ tips (volumeAround Λ l n T) := tips_mono (around_mono Λ l p n)
  constructor
  · intro n
    exact ⟨⟨(h.usable n).tips_x.seat_.mono (ht n)⟩⟩
  intro n x y v w
  exact h.distances n x y (ht n v) (ht n w)

/-- Crossing product estimate, with the SAME threshold for every stage up to the bare horizon (alias issues matter). -/
lemma Host.far {s i : ℕ} {S T : Finset Cover} (p : Detached Λ l S T) (h : Host Y H i s (S ∪ T))
    (n : ℕ) : ∀ x ∈ Satin.region (volumeAround Λ l n S) (side Y i (s+n)),
      ∀ y ∈ Satin.region (volumeAround Λ l n T) (side Y i (s+n)),
        2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)< separation x y := by
  intro x u y v
  obtain ⟨x,hx,rfl⟩:= Finset.mem_image.mp u
  obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp v
  by_contra! ht
  rw [separation_comm] at ht
  have he := YM.Work.E08.lift_mem_box ht
  rw [h.distances n x y (tips_here _ (around_mono Λ l subset_union_left n hx))
    (tips_here _ (around_mono Λ l subset_union_right n hy))] at he
  exact (Around_detaches Λ l p n).act Λ l _ hx _ hy he

lemma wingspan_union (Λ : Preparation) (l : ℕ) (S T : Finset Cover) : wingspan Λ l (S∪T)=wingspan Λ l S∪wingspan Λ l T := by
  unfold wingspan liner; rw [Finset.image_union, Finset.union_biUnion]

lemma volume_union (Λ : Preparation) (l n : ℕ) (S T : Finset Cover) : volumeAround Λ l n (S∪T)=volumeAround Λ l n S∪volumeAround Λ l n T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [volumeAround,ih]; exact wingspan_union ..
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.eventually_host
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Host.far
