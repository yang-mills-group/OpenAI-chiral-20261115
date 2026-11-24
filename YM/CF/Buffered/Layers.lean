import YM.CF.Support.Pulse

/-!
# A fixed-geometry Lie product formula

For the layers of the slab proof. Can spend this in the *uniform norm on fields*, not uniform
in system sizes. Adaptation of `Support/Pulse` Euler/power comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Trotter
open scoped Topology
open Filter NormedSpace
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]


def LinearLayer (L : ℝ → A) (a : A) : Prop :=
  ∃ K ≥ (0:ℝ), ∀ t ∈ Set.Icc (0:ℝ) 1, ‖L t - 1 - t • a‖ ≤ t^2*K

namespace LinearLayer
lemma exponential (a : A) : LinearLayer (fun t : ℝ => exp (t • a)) a := rest_near a
omit [CompleteSpace A] [NormOneClass A] in
lemma euler (a : A) : LinearLayer (fun t : ℝ => 1 + t • a) a :=
  ⟨0, le_rfl, fun t _ => by simp⟩
omit [CompleteSpace A] [NormOneClass A] in
lemma multiply {L M : ℝ → A} {a b : A} (h : LinearLayer L a) (g : LinearLayer M b) :
    LinearLayer (fun t => L t * M t) (a + b) := by
  obtain ⟨c,hc,u⟩ := h; obtain ⟨d,hd,v⟩ := g
  refine ⟨c + d + (‖a‖+c)*(‖b‖+d), by positivity, fun t ht => ?_⟩
  have ht₀ := ht.1; have ht₁ := ht.2
  have hs : t^2 ≤ t := by nlinarith
  have H (a l : A) (c : ℝ) (hc : 0 ≤ c) (h : ‖l - 1 - t • a‖ ≤ t^2*c) :
      ‖l-1‖ ≤ t*(‖a‖+c) := by
    have he := norm_add_le (l - 1 - t • a) (t • a)
    rw [sub_add_cancel,norm_smul,Real.norm_of_nonneg ht₀] at he
    linarith only [he,h,mul_le_mul_of_nonneg_right hs hc]
  have hh := add_le_add (add_le_add (u t ht) (v t ht))
    ((norm_mul_le (L t-1) (M t-1)).trans (mul_le_mul (H _ _ c hc (u t ht)) (H _ _ d hd (v t ht)) (norm_nonneg _) (by positivity)))
  change ‖L t*M t- _ - _‖≤_
  rw [show L t * M t - 1 - t • (a+b) = (L t - 1 - t • a) + (M t - 1 - t • b) + (L t - 1)*(M t - 1) from by rw [smul_add]; noncomm_ring]
  refine (norm_add_le ..).trans ((add_le_add (norm_add_le ..) (le_refl _)).trans (hh.trans_eq ?_)); ring

local notation "λ₀" => fun (i : ℕ) => (i+1:ℝ)⁻¹

lemma iterate {L : ℝ → A} {a : A} (h : LinearLayer L a) :
    Tendsto (fun i:ℕ => (L (λ₀ i))^(i+1)) atTop (𝓝 (exp a)) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨b,hb,Hb⟩ := h
  obtain ⟨c,hc,H⟩ := exponential a
  let C := ‖a‖+b+c; have hc' : 0≤C := by unfold C; positivity
  let f := λ₀
  have hp : ∀ i, f i ∈ Set.Icc (0:ℝ) 1 := fun i=> ⟨by unfold f; positivity,
    inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg i (α:=ℝ))])⟩
  let r := Real.exp C
  have hk (i : ℕ) : ‖L (f i) ^ (i+1)-exp a‖ ≤ f i *(r*(b+c)) := by
    let t := f i; let R := Real.exp (C*t); let Q := exp (t • a)
    have he := H _ (hp i); have he' := Hb _ (hp i); have ht : 0≤t := (hp i).1; have hB : t≤1 := (hp i).2
    have hz : t^2 ≤ t := by nlinarith
    have hy : 1+C*t≤R := by simpa [add_comm] using Real.add_one_le_exp (C*t)
    have HW (p : A) (g : ‖p-1-t • a‖ ≤ t^2*(b+c)) : ‖p‖ ≤ R := by
      calc
        _ ≤ ‖1 + t • a‖ + ‖p - 1 - t • a‖ := by
          nth_rw 1 [show p = 1 + t • a + (p - 1 - t • a) from by abel]
          exact norm_add_le ..
        _ ≤ ‖(1:A)‖ + ‖t • a‖ + t^2*(b+c) := add_le_add (norm_add_le ..) g
        _ ≤ R := by
          rw [norm_smul,norm_one,Real.norm_of_nonneg ht]
          apply le_trans _ hy; unfold C; nlinarith [mul_le_mul_of_nonneg_right hz (show 0≤b+c by positivity)]
    have hh : Q^(i+1)=exp a := by
      unfold Q; rw [←exp_nsmul]; apply congrArg exp
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,show (↑(i+1):ℝ)*t=1 by unfold t f; push_cast; field_simp,one_smul]
    have hX : ‖L t‖ ≤ R := HW (L t) (he'.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hc) (by positivity)))
    have hv : ‖Q‖≤R := HW Q (he.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hb) (by positivity)))
    have hx : ‖L t-Q‖ ≤ t^2*(b+c) := by
      rw [show L t - Q = (L t - 1 - t • a) - (Q - 1 - t • a) from by abel,mul_add]
      exact (norm_sub_le ..).trans (add_le_add he' he)
    rw [← hh]; apply (power_le_press i R _ (Real.exp_pos _).le hX hv hx).trans
    have hi : 1 ≤ R := Real.one_le_exp (mul_nonneg hc' ht)
    have hu : (i+1:ℝ)*t=1 := by unfold t f; field_simp
    have hV : R^(i+1)=r := by unfold R r; rw [←Real.exp_nat_mul]; apply congrArg Real.exp; push_cast; rw [mul_left_comm,hu,mul_one]
    calc
      _ ≤ (i+1:ℝ)*r*(t^2*(b+c)) := by rw [←hV]; gcongr; omega
      _ = _ := by change _=t * _; calc
                    _ = ((i+1:ℝ)*t)*(t*(r*(b+c))) := by ring
                    _ = _ := by rw [hu,one_mul]
  rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero (fun _=>norm_nonneg _) hk
  have hu : Tendsto f atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simpa only [zero_mul] using hu.mul_const (r*(b+c))

end LinearLayer
-- both seams, first nonwrap then wrap, slab factors first
def layer (a b c d : A) (t : ℝ) :=
  exp (t • a) * exp (t • b) * (1+t • c) * (1+t • d)
def evolution (a b c d : A) (n : ℕ) := (layer a b c d (n+1:ℝ)⁻¹)^(n+1)
lemma evolution_limit (a b c d : A) : Tendsto (evolution a b c d) atTop (𝓝 (exp (a+b+(c+d)))) := by
  rw [← add_assoc (a+b) c d]
  exact ((((LinearLayer.exponential a).multiply (.exponential b)).multiply (.euler c)).multiply (.euler d)).iterate

end YM.CF.Buffered.Trotter
