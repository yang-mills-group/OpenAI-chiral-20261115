import GaugeFieldConstruction.Orbit
/-! Computable enumeration for the finite certificate. -/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Certificate
open Function
open scoped BigOperators

def axes : List Axis := [0,1,2,3]
lemma mem_axes (i : Axis) : i∈axes := by fin_cases i <;> decide

def perm4 : List (Equiv.Perm Axis) :=
  [⟨![0,1,2,3],![0,1,2,3],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![0,1,3,2],![0,1,3,2],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![0,2,1,3],![0,2,1,3],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![0,2,3,1],![0,3,1,2],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![0,3,1,2],![0,2,3,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![0,3,2,1],![0,3,2,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![1,0,2,3],![1,0,2,3],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![1,0,3,2],![1,0,3,2],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![1,2,0,3],![2,0,1,3],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![1,2,3,0],![3,0,1,2],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![1,3,0,2],![2,0,3,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![1,3,2,0],![3,0,2,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![2,0,1,3],![1,2,0,3],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![2,0,3,1],![1,3,0,2],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![2,1,0,3],![2,1,0,3],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![2,1,3,0],![3,1,0,2],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![2,3,0,1],![2,3,0,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![2,3,1,0],![3,2,0,1],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![3,0,1,2],![1,2,3,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![3,0,2,1],![1,3,2,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![3,1,0,2],![2,1,3,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![3,1,2,0],![3,1,2,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![3,2,0,1],![2,3,1,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩,
    ⟨![3,2,1,0],![3,2,1,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩]

lemma nodup : perm4.Nodup := by decide
lemma perm4_fin : perm4.toFinset=Finset.univ := Finset.eq_univ_of_card _ (by
  rw [List.toFinset_card_of_nodup nodup, Fintype.card_perm]; decide)
lemma mem_perm (p : Equiv.Perm Axis) : p∈perm4 := by
  rw [← List.mem_toFinset, perm4_fin]; exact Finset.mem_univ _
theorem sum_perm {K : Type*} [AddCommMonoid K] (f : Equiv.Perm Axis → K) :
    (perm4.map f).sum = ∑ p, f p := by rw [← perm4_fin, List.sum_toFinset _ nodup] -- check

end YM.GaugeFieldConstruction.Certificate
