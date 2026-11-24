import SatinStress.Internal.FlavorBlocks
/-!
# The 3-generation group(s) for this proof

Use copies separately on 10 and bar5 sectors. Implement the little group of
orientation-preserving signed permutations (again **real**). All determinant and unitary
claims here literal on matrix reps.
-/
set_option autoImplicit false
namespace YM.CF.SatinStressData
open Matrix Finset Function SU
open scoped Matrix Kronecker BigOperators

-- multiplication convention: act on columns. modeled after YM.Space.Index (Signed4).
@[ext] structure Menu where
  perm : Equiv.Perm Age
  flip : Age → Bool
  deriving DecidableEq
namespace Menu
instance : Fintype Menu := Fintype.ofEquiv (Equiv.Perm Age × (Age→Bool))
  { toFun x := ⟨x.1,x.2⟩, invFun x := (x.perm,x.flip), left_inv _ := rfl, right_inv _ := rfl }
instance : One Menu := ⟨⟨Equiv.refl _,fun _ => false⟩⟩
instance : Mul Menu := ⟨fun a b => ⟨a.perm*b.perm,fun i => (a.flip (b.perm i)).xor (b.flip i)⟩⟩
instance : Inv Menu := ⟨fun a => ⟨a.perm⁻¹,fun i => a.flip (a.perm.symm i)⟩⟩
@[simp] lemma perm_step (a b : Menu) (i) : (a*b).perm i = a.perm (b.perm i) := rfl
@[simp] lemma flip_step (a b : Menu) (i) : (a*b).flip i = (a.flip (b.perm i)).xor (b.flip i) := rfl
@[simp] lemma back_perm (a : Menu) (i) : a⁻¹.perm i = a.perm.symm i := rfl
@[simp] lemma back_flip (a : Menu) (i) : a⁻¹.flip i = a.flip (a.perm.symm i) := rfl
@[simp] lemma base_perm (i) : (1 : Menu).perm i=i := rfl
@[simp] lemma base_flip (i) : (1 : Menu).flip i=false := rfl
instance : Group Menu where
  one_mul a := Menu.ext (by ext; simp) (by funext; simp)
  mul_one a := Menu.ext (by ext; simp) (by funext; simp)
  mul_assoc a b c := Menu.ext (by ext; simp) (by funext; simp)
  inv_mul_cancel a := Menu.ext (by ext; simp) (by funext; simp)

-- all `choose` in normed representation will use only the proper subgroup, shown
-- below. Here don't let perm determinant get stuck on noncomputable choices.
def bit (a : Bool) : ℤ := if a then -1 else 1
def price (a : Menu) : Matrix Age Age ℤ := Matrix.of fun i j => if a.perm j=i then bit (a.flip j) else 0
@[simp] lemma price_one : price 1=1 := by ext i j; simp [price,bit, Matrix.one_apply,eq_comm]
@[simp] lemma price_mul (a b : Menu) : price (a*b)=price a*price b := by
  ext i j; rw [Matrix.mul_apply,sum_eq_single (b.perm j)];
  · by_cases e : a.perm (b.perm j)=i
    · have h' (x y) : bit (x ^^ y)=bit x*bit y := by decide +revert -- revert problem; change
      simp [price,e,h']
    simp [price,e]
  · intro k _ h; simp [price,Ne.symm h]
  simp
@[simp] lemma price_transpose (a : Menu) : (price a)ᵀ=price a⁻¹ := by
  ext i j; simp only [transpose_apply, price, Matrix.of_apply,back_flip,back_perm]
  by_cases h:a.perm.symm j=i
  · simp [h,show a.perm i=j by rw [← h]; simp]
  simp [h, show ¬a.perm i=j from fun e => h (by rw [← e,a.perm.symm_apply_apply])]

def Proper : Subgroup Menu where
  carrier := {u | det (price u)=1}
  one_mem' := by change det _=1; rw [price_one,det_one]
  mul_mem' {a b} hA hB := by change det _=1; rw [price_mul,det_mul,hA,hB,mul_one] -- hypotheses coerced?
  inv_mem' {a} he := by change det _=1; rw [← price_transpose,det_transpose]; exact he

instance : DecidablePred (· ∈ (Proper : Set Menu)) := fun u => inferInstanceAs (Decidable (det (price u)=1))
-- abbrev projection uses subgroup's carrier not Coee? ensure Fintype instance
abbrev Pos := ↥Proper

-- diagonal turns (flip all but i) & rotations (flip one and exchange i,j) inside Proper.
def mute (i : Age) := (⟨Equiv.refl _, fun j => decide (j ≠ i)⟩ : Menu)
def trade (i j : Age) := (⟨Equiv.swap i j, fun k => decide (k=i)⟩ : Menu)
lemma pM (i : Age) : mute i ∈ Proper := (by change det _=1; decide +kernel +revert)
lemma pT (i j : Age) (h : i ≠ j) : trade i j ∈ Proper := by change det _=1; decide +kernel +revert

noncomputable section
def pose (a : Menu) : Op Age := (price a).map (fun x => (x:ℂ))
@[simp] lemma posed_mul (a b) : pose (a*b)=pose a*pose b := by
  unfold pose
  simp only [price_mul]
  exact map_mul ((Int.castRingHom ℂ).mapMatrix) _ _
@[simp] lemma posed_one : pose 1=1 := by
  unfold pose; rw [price_one]; ext; simp [Matrix.one_apply,apply_ite]
@[simp] lemma star_pose (a : Menu) : star (pose a)=pose a⁻¹ := by ext i j; simp [pose,← price_transpose]
lemma poseU (a : Menu) : pose a∈unitary _ := by constructor <;> rw [star_pose,← posed_mul] <;> simp
lemma pos_det (a : Menu) (p : a∈Proper) : det (pose a)=1 := by
  unfold pose
  change det ((Int.castRingHom ℂ).mapMatrix (price a))=_
  rw [← RingHom.map_det,show (price a).det=1 from p,map_one]
@[simp] lemma cc_pose (a : Menu) : CF.cc (pose a)=pose a := by ext; simp [pose]

private lemma commute_at (a : Menu) (T : Op Age) (x y : Age) (h : T * pose a = pose a * T) :
    T (a.perm x) (a.perm y) * (bit (a.flip y) : ℂ) = (bit (a.flip x) : ℂ) * T x y := by
  have he := Matrix.ext_iff.mpr h (a.perm x) y
  rw [Matrix.mul_apply, Matrix.mul_apply, sum_eq_single (a.perm y) (by intro b _ hb; simp [pose,price,hb.symm]) (by simp), sum_eq_single x] at he
  · simpa [pose,price] using he
  · intro b _ h; simp [pose,price,h]
  simp
lemma proper_commuting (T : Op Age) (h : ∀ m : Pos, T * pose m.val = pose m.val * T) :
    T = T 0 0 • 1 := by
  have he (i j : Age) (p : i ≠ j) : T i j=0 := by
    have ht := commute_at (mute i) T i j (h ⟨_,pM i⟩)
    simp [mute,bit,Ne.symm p] at ht; exact neg_eq_self.mp ht -- name?
  have ht (i : Age) : T i i=T 0 0 := by
    by_cases hp:i=0
    · rw [hp]
    -- trade with 0
    have hh := commute_at (trade 0 i) T 0 0 (h ⟨_,pT 0 i (Ne.symm hp)⟩)
    simpa [trade,bit] using hh
  ext i j; by_cases hm : i=j
  · subst j; rw [ht]; simp -- tune self rewrite
  simp [he i j hm,hm]
end
end Menu
end YM.CF.SatinStressData
