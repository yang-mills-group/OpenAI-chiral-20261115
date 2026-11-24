import ExactRunning.Final.OakRecord
import ExactRunning.Dyne.Telescope

/-!
# Uniform estimate for Gold paths
-/
noncomputable section
namespace ExactRunning

open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset
open scoped BigOperators Topology
open Precision Wilson Exterior Tree
open CF.Vale CF

local notation "G5" => SU.group
variable {K : Pressure.Teller G5} {P : Patch} {R : ChartRatio G5} {W : Hom.Postal}

lemma gold_error (B : Gold K P R W) (localChart : LocalRatio R) :
    ∃ C : ℝ, ∀ j k : ℕ, |∑ r∈range k,(B.charge (j+r) + owes G5 P.L)| ≤ C := by
  obtain ⟨F,e,a,b,ha,hb,t⟩ := gold_ep B
  let A : Arch G5 P.L B.charge := ⟨goldPylon B F e,
    fun j=> by
      obtain ⟨x,g,f⟩ := gold_blockTie B F e localChart j
      exact ⟨x,f,g⟩⟩
  let i : SU.group.ColorIndex := Classical.choice (colorAvail _ Thera.yet_one)
  exact ⟨_,A.error i ha hb t⟩

lemma gold_reverse (B : Gold K P R W) (localChart : LocalRatio R) :
    ∃ C : ℝ, ∀ N j k : ℕ, j+k ≤ N →
      |-(∑ d∈range k,B.charge (N-1-(j+d))) - k * owes G5 P.L| ≤ C := by
  obtain ⟨C,h⟩ := gold_error B localChart
  refine ⟨C, fun N j k w => ?_⟩
  calc
    _ = |∑ d∈range k,(B.charge (N-1-(j+d))+owes G5 P.L)| := by
      rw [←abs_neg (_-_ : ℝ),sum_add_distrib]; simp [add_comm]
    _ = |∑ d∈range k,(B.charge ((N-(j+k))+d)+owes G5 P.L)| := by
      rw [←sum_range_reflect]
      congr 1
      refine sum_congr rfl fun d hd=>?_
      have := mem_range.mp hd
      congr 2; omega
    _ ≤ C := h ..

lemma ratio_exact {k g ε C x : ℝ} (d : 0<k*g)
    (h : |x-k*g| ≤ C) (c : C < k*(g*(3/55*ε))) :
    |55/3*x/(k*g) - 55/3| < ε := by
  rw [abs_le] at h
  rw [abs_lt,lt_sub_iff_add_lt,lt_div_iff₀ d,sub_lt_iff_lt_add,div_lt_iff₀ d]
  constructor <;> linarith only [c,h.1,h.2]

lemma gold_ratio (B : Gold K P R W) (localChart : LocalRatio R) (hp : 0 < owes G5 P.L)
    (ε : ℝ) (hε : 0<ε) :
    ∃ l : ℕ, 1≤l ∧ ∀ (N j k : ℕ), l≤k → j+k ≤ N →
      |55/3 * (-(∑ d∈range k,B.charge (N-1-(j+d))))/(k*owes G5 P.L) - 55/3| < ε := by
  obtain ⟨C,h⟩ := gold_reverse B localChart
  have hd : 0<owes G5 P.L * (3/55*ε) := by positivity
  obtain ⟨k,e⟩ := exists_nat_gt (C/(owes G5 P.L * (3/55*ε)))
  exact ⟨max k 1, le_max_right ..,
    fun N j m hm he =>
      ratio_exact (mul_pos (Nat.cast_pos.mpr ((le_max_right k 1).trans hm)) hp)
        (h _ _ _ he)
        ((div_lt_iff₀ hd).mp (e.trans_le (Nat.cast_le.mpr ((le_max_left k 1).trans hm))))⟩

end ExactRunning
