import YM.CF.Lattice.Frame
import YM.Lattice.Foliation

/-! Transport bound on the cover from the cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open YM.Lattice Lat
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {I K : Type*} [Group K] [Fintype I] [DecidableEq I]

variable (R : K →* UNI I)
def cmp (x y : K) := ‖(R x).val-(R y).val‖
lemma cmp_sym (x y : K) : cmp R y x=cmp R x y := norm_sub_rev ..
lemma cmp_triangle (x y z : K) : cmp R x z ≤ cmp R x y+cmp R y z := norm_sub_le_norm_sub_add_norm_sub ..
lemma cmp_id (x : K) : cmp R x x=0 := by simp [cmp]
lemma cmp_left (x y z : K) : cmp R (z*x) (z*y)=cmp R x y := by
  unfold cmp; simp_rw [map_mul]
  change ‖(R z).val*_ - (R z).val*_‖=_; rw [←mul_sub,CStarRing.norm_coe_unitary_mul]
lemma cmp_right (x y z : K) : cmp R (x*z) (y*z)=cmp R x y := by
  unfold cmp; simp_rw [map_mul]
  change ‖_*(R z).val - _*(R z).val‖=_; rw [←sub_mul,CStarRing.norm_mul_coe_unitary]
lemma cmp_g (g h : K) : cmp R g h=cmp R (g*h⁻¹) 1 := by rw [←cmp_right R g h h⁻¹,mul_inv_cancel]
section
variable {R} {U : Links ℤ K} {e : ℝ}
def Covered (R : K →* UNI I) (U : Links ℤ K) (e : ℝ) := ∀ x i j, i ≠ j → cmp R (travel U x (square i j)) 1 ≤ e
def compareW (R : K →* UNI I) (U : Links ℤ K) (x : Cover) (a b : Walk) := cmp R (travel U x a) (travel U x b)
def Flip (R : K →* UNI I) (U : Links ℤ K) (e : ℝ) (i j : Step) := ∀ x, compareW R U x [i,j] [j,i] ≤ e
lemma flip_sym {i j : Step} (h : Flip R U e i j) : Flip R U e j i := by intro x; unfold compareW; rw [cmp_sym]; exact h x
lemma flip_pos {i j : Axis} (he : 0≤e) (h : Covered R U e) : Flip R U e (posDir i) (posDir j) := by
  intro x; by_cases g:i=j
  · subst j; rw [compareW,cmp_id]; exact he
  unfold compareW; rw [cmp_g]; convert h x i j g using 2
  let A := [posDir i,posDir j]; let B := [posDir j,posDir i]
  change _=travel U x (A++reverse B)
  have ht : stop x A=stop x B := by simp [A,B,stop,add_right_comm]
  rw [travel_append,ht,travel_reverse]
lemma flip_rev {i j : Step} (h : Flip R U e i j) : Flip R U e i.rev j := by
  intro x; let z : Cover := x-i.vec
  have hi := h z; unfold compareW at *; simp only [travel,stop,mul_one,Step.vec_rev] at *
  have he : z+i.vec=x := sub_add_cancel ..
  rw [he] at hi
  let a := i.read U z; let b := j.read U z
  let c := i.read U (z+j.vec); let d := j.read U x
  have hz : x+j.vec=z+j.vec+i.vec := by rw [add_right_comm,he]
  rw [show i.rev.read U x=a⁻¹ by nth_rw 1 [← he]; exact Step.read_rev ..,
     show x + -i.vec=z from (sub_eq_add_neg ..).symm,hz,Step.read_rev]
  apply le_trans (le_of_eq _) hi
  change cmp R (a⁻¹*b) (d*c⁻¹)=cmp R (a*d) (b*c)
  rw [← cmp_right R (a⁻¹*b) (d*c⁻¹) c,← cmp_left R ((a⁻¹*b)*c) ((d*c⁻¹)*c) a]
  rw [show a*(a⁻¹*b*c)=b*c by group,show a*(d*c⁻¹*c)=a*d by group,cmp_sym]
lemma flipSteps (he : 0≤e) (h : Covered R U e) (i j : Step) : Flip R U e i j := by
  rcases i with ⟨i,q|q⟩ <;> rcases j with ⟨j,q|q⟩
  · exact flip_pos he h
  · have h₁ := flip_pos (i:=j) (j:=i) he h
    have h₂ := @flip_rev _ _ _ _ _ R U e (posDir j) (posDir i) h₁
    exact @flip_sym _ _ _ _ _ R U e (negDir j) (posDir i) h₂
  · exact @flip_rev _ _ _ _ _ R U e (posDir i) (posDir j) (flip_pos he h)
  · have h₁ := flip_pos (i:=j) (j:=i) he h
    have h₂ := @flip_rev _ _ _ _ _ R U e (posDir j) (posDir i) h₁
    have h₃ := @flip_sym _ _ _ _ _ R U e (negDir j) (posDir i) h₂
    exact @flip_rev _ _ _ _ _ R U e (posDir i) (negDir j) h₃
lemma slide (he : 0≤e) (h : Covered R U e) (x : Cover) (l : Walk) (i : Step) :
    compareW R U x (i::l) (l++[i]) ≤ l.length * e := by
  induction l generalizing x with
  | nil => simp [compareW,cmp_id]
  | cons j l ih =>
    let d := travel U x (j::i::l)
    apply (cmp_triangle R _ d _).trans
    have ht : cmp R (travel U x (i::j::l)) d ≤ e := by
      unfold d
      change cmp R (travel U x ([i,j]++l)) (travel U x ([j,i]++l))≤_
      rw [travel_append,travel_append,show stop x [i,j]=stop x [j,i] from add_right_comm ..,cmp_right]
      exact flipSteps he h i j x
    have he : cmp R d (travel U x ((j::l)++[i])) ≤ l.length*e := by
      unfold d; rw [show (j::l)++[i]=j::(l++[i]) from rfl,travel,show travel U x (j::(l++[i]))=j.read U x*travel U (x+j.vec) (l++[i]) from travel.eq_2 _ _ _ _,cmp_left]
      exact ih _
    rw [List.length_cons]; push_cast; linarith
end
end YM.CF.Cube
