import YM.CF.Phase.Design

/-! Face parameters and admissibility of close-point log bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Finset
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}
lemma cross_scale : ∃ r : ℝ, 0<r ∧ ∀ v w:Ballot, ‖v.val-w.val‖ < r → ‖localPair v.val-localPair w.val‖ ≤ 1/4 := by
  let f : Ballot→Op (SpinIdx×Slot) := fun x=> localPair x.val
  have h : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous (localPair_cont.comp continuous_subtype_val)
  obtain ⟨r,H,G⟩ := Metric.uniformContinuous_iff.mp h _ (show 0 < (1:ℝ)/4 by norm_num)
  refine ⟨r,H,fun v w he=>?_⟩
  have g := G (a:=v) (b:=w) (by rw [Subtype.dist_eq, dist_eq_norm]; exact he)
  rw [dist_eq_norm] at g; exact g.le

def Dangle := cross_scale.choose
lemma angle_pos : 0<Dangle := cross_scale.choose_spec.1
def way (B : Side) : ℕ := ⌈2*variations B/Dangle⌉₊+1
lemma way_pos (B : Side) : 0 < way B := Nat.succ_pos _
lemma way_room (B : Side) : variations B*(2/(way B:ℝ)) < Dangle := by
  have h : 0 < (way B:ℝ) := by exact_mod_cast way_pos B
  have ht : 2*variations B/Dangle < (way B:ℝ) := lt_of_le_of_lt (Nat.le_ceil _) (by unfold way; push_cast; linarith)
  rw [div_lt_iff₀ angle_pos] at ht; rwa [←mul_div_assoc,mul_comm,div_lt_iff₀ h,mul_comm Dangle] -- tune
abbrev stick (i : Row) : Sq := Pi.single i 1
lemma stick_in {r : Zone} (i : Row) (h : i∈r) : stick i ∈ zone r :=
  ⟨dirac_prob i,fun j g=> by have he : j≠i := fun e=>g (e ▸ h); simp [stick,he]⟩
lemma cube_path (r : Zone) : Convex ℝ (zone r) := by
  intro x hx y hy a b ha hb h
  have H : prob x := hx.1; have G : prob y := hy.1
  refine ⟨⟨fun i=> by simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul]; exact add_nonneg (mul_nonneg ha (H.1 _)) (mul_nonneg hb (G.1 _)),?_⟩,fun i g=>?_⟩
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_add_distrib,←mul_sum,H.2,G.2,mul_one,h]
  have hp : x i=0 := hx.2 i g; have hk : y i=0 := hy.2 i g; simp [hp,hk]
lemma norm_zone {r q} (h : q∈zone r) : ‖q‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i
  have H : prob q := h.1; rw [Real.norm_of_nonneg (H.1 i)]
  exact (single_le_sum (fun i _=>H.1 i) (mem_univ i)).trans H.2.le
def increment (B : Side) (k : ℕ) (q t : Sq) : Sq := let i : ℝ := k/way B; (1-i) • q+i • t
lemma inc_zero (B q t) : increment B 0 q t=q := by simp [increment]
lemma inc_last (B q t) : increment B (way B) q t=t := by simp [increment, (show way B≠0 from (way_pos B).ne')]
lemma inc_same (B k q) : increment B k q q =q := by unfold increment; dsimp only; rw [←add_smul, sub_add_cancel,one_smul]
lemma inc_in {r u v} (h : u∈zone r) (g : v∈zone r) {k : ℕ} (B : Side) (hk : k≤way B) : increment B k u v∈zone r := by
  unfold increment; dsimp only; apply cube_path r h g _ (by positivity) (by ring)
  rw [sub_nonneg,div_le_one (Nat.cast_pos.mpr (way_pos B))]; exact_mod_cast hk
lemma inc_gap {r u v} (h : u∈zone r) (g : v∈zone r) (B : Side) (k : ℕ) :
    ‖increment B (k+1) u v-increment B k u v‖≤2/(way B:ℝ) := by
  have he : ‖v-u‖≤2 := (norm_sub_le ..).trans ((add_le_add (norm_zone g) (norm_zone h)).trans (by norm_num))
  unfold increment; dsimp only; push_cast; rw [add_div,add_sub_add_comm, ← sub_smul, ← sub_smul,add_sub_cancel_left,
    show 1-((k:ℝ)/way B + 1/way B)-(1-(k:ℝ)/way B)= -(1/(way B:ℝ)) by ring,neg_smul,neg_add_eq_sub,←smul_sub,
    norm_smul,Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (le_of_eq (by ring))
lemma short (c : Part m B) {e : ℝ} {U : Skin m B} (b : Room B e) (h : Guard U e) {s : ArrayF m} {r q t}
    (V : Verified m B margin U s r) (x : q∈zone r) (y : t∈zone r) (g : ‖t-q‖≤2/(way B:ℝ)) :
    ‖relay (lens m B c U) (bow m B U s q) (bow m B U s t)-1‖ < 1 := by
  let N := CSide m B; let A := grain m B U s t; let C := grain m B U s q
  have ht (i) : ‖A i-C i‖ < Dangle := by
    apply (variations_le s t q y.1 x.1 b.1 h V y.2 x.2 b.2.2 _).trans_lt
    exact (mul_le_mul_of_nonneg_left g (variation_pos B).le).trans_lt (way_room B)
  have H : ‖bow m B U s t-bow m B U s q‖≤1/4 := by
    unfold bow Cfield; rw [← jump_sub]; apply jump_bound _ _ (by norm_num); intro i
    have hA : A i ∈ Sphere := by simp [Sphere,show ‖A i‖=1 from grain_unit b h V y i]
    have hC : C i ∈ Sphere := by simp [Sphere,show ‖C i‖=1 from grain_unit b h V x i]
    exact cross_scale.choose_spec.2 ⟨A i,hA⟩ ⟨C i,hC⟩ (ht i)
  apply (relay_gap (lensP c b h) (bow_ok c b h V x).2 (bow_ok c b h V x).1).trans_lt
  linarith
end YM.CF.Phase
