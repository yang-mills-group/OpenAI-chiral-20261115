import SatinStress.Internal.Intertwine
/-!
# Commuting weights for one-generation Sheet

Impose `[α≠β]` weights using the single traceless diagonal **H** after
complexification, verifying actual supports of root entries, rather than
invoking abstract irreducibility and tensor decomposition hypotheses.
-/
set_option autoImplicit false
namespace YM.CF.SatinStressData
open Gauge SU Function Matrix Finset
open Complex (I)
open scoped Matrix Kronecker Topology BigOperators

-- matrices with `wp` etc in `ℤ`, kernel checks including negative diagonal

noncomputable def element (i j : F) : Fund := single i j 1
-- element noncomputable?
def wp : F → ℤ := ![1,10,100,1000,-1111]
noncomputable def H : Fund := diagonal fun i => (wp i:ℂ)
def wt : Sheet → ℤ
 | .inl u => wp u.val.1 + wp u.val.2
 | .inr i => -(wp i)
def integerVersion (G : Matrix F F ℤ) : Matrix Sheet Sheet ℤ := Matrix.of (fun i j =>
  match i,j with
  | .inl a,.inl b => G a.val.1 b.val.1 * (1 : Matrix F F ℤ) a.val.2 b.val.2 +
    (1 : Matrix F F ℤ) a.val.1 b.val.1 * G a.val.2 b.val.2 -
    (G a.val.1 b.val.2 * (1: Matrix F F ℤ) a.val.2 b.val.1 + (1 : Matrix F F ℤ) a.val.1 b.val.2 * G a.val.2 b.val.1)
  | .inr x,.inr y => -G y x
  | _,_ => 0)
lemma compatible (G : Matrix F F ℤ) (x y : Sheet) :
   spinRep (G.map fun t => (t:ℂ)) x y = (integerVersion G x y : ℂ) := by
  rcases x with x|x <;> rcases y with y|y <;>
    simp [integerVersion,spinRep,scheme,Join.both,upper,lower,gen_entry, one_apply, Int.cast_ite]

lemma H_clear : H.trace=0 := by
  rw [H,trace_diagonal,← Int.cast_sum,show (∑ x:F, wp x) = 0 by decide,Int.cast_zero]
lemma H_price : spinRep H = diagonal fun s => (wt s : ℂ) := by
  ext i j; rw [show H=(diagonal wp).map (fun x => (x:ℂ)) by ext i j; by_cases e:i=j <;> simp [H,e], compatible]
  have he : integerVersion (diagonal wp) i j = diagonal wt i j := by decide +revert +kernel
  rw [he]; simp only [diagonal_apply]; split <;> simp

lemma distinct0 (i j : Sheet) (he : wt i = wt j) : i=j := by decide +revert +kernel
-- beware revert proposition eq dependent

noncomputable def sheetId (a b : ℂ) : SheetEnd := Join.both (a • 1) (b • 1)
lemma sheetId_fixed (a b : ℂ) : FixedS (sheetId a b) := by
  intro g
  unfold holds sheetId mat each; rw [Join.both_mul,Join.both_mul]
  simp

lemma rooted_zero {a b : F} (h : a ≠ b) : trace (element a b) = 0 := by simp [element,h]
lemma sees (a b : F) (x y : Sheet) : spinRep (element a b) x y = (integerVersion (single a b 1) x y : ℂ) := by
  rw [show element a b = (single a b (1:ℤ)).map (fun k => (k:ℂ)) by ext; simp only [map_apply,element,single_apply]; split <;> simp, compatible]

def label (x:Sheet) : Bool := Sum.isLeft x
def arc (x y : Sheet) : Prop := x=y ∨ ∃ a b:F, a≠b ∧ integerVersion (single a b 1) x y≠0
instance (x y : Sheet) : Decidable (arc x y) := by unfold arc; infer_instance
set_option maxHeartbeats 1000000 in
theorem two_steps : ∀ x y : Sheet, label x = label y → ∃ z, arc x z ∧ arc z y := by
  decide +kernel

lemma fixed_diagonal {T : SheetEnd} (h : FixedS T) : T=diagonal T.diag := by
  ext i j; by_cases he:i=j; simp [he]; rw [diagonal_apply_ne T.diag he]
  by_contra hi
  have hh := Matrix.ext_iff.mpr (differentiate_fixed T h H_clear) i j
  rw [H_price, diagonal_mul,mul_diagonal,mul_comm (T i j)] at hh
  exact he (distinct0 i j (by exact_mod_cast mul_right_cancel₀ hi hh))

lemma middle : (0:F)<1 := by decide
def origin : Ten := ⟨(0,1),middle⟩

lemma fixed_id {T : SheetEnd} (h : FixedS T) :
    T = sheetId (T (.inl origin) (.inl origin)) (T (.inr 0) (.inr 0)) := by
  have he := fixed_diagonal h
  have ha (x y : Sheet) (a : arc x y) : T x x=T y y := by
    rcases a with rfl|⟨a,b,hp,hv⟩; rfl
    have hy := differentiate_fixed T h (rooted_zero hp)
    unfold holds at hy; rw [he] at hy; have hx := Matrix.ext_iff.mpr hy x y
    rw [mul_diagonal, diagonal_mul,diag_apply,diag_apply,mul_comm (T x x), sees] at hx
    exact mul_left_cancel₀ (by exact_mod_cast hv) hx.symm
  have hd (x y : Sheet) (h : label x = label y) : T x x=T y y := by
    obtain ⟨z,e,t⟩:=two_steps x y h; exact (ha x z e).trans (ha z y t)
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · by_cases hh : i=j
    · subst j; simpa [sheetId,Join.both] using hd (.inl i) (.inl origin) rfl
    simp [Join.both,sheetId,hh]; nth_rw 1 [he]; simp [hh]
  · simp [Join.both,sheetId]; rw [he]; simp
  · simp [Join.both,sheetId]; rw [he]; simp
  by_cases hp:i=j
  · subst j; simpa [Join.both,sheetId] using hd (.inr i) (.inr 0) rfl
  simp [Join.both,sheetId,hp]; nth_rw 1 [he]; simp [hp]

theorem fixed_iff (T : SheetEnd) : FixedS T ↔ ∃ a b, T = sheetId a b := by
  refine ⟨fun h => ⟨_,_,fixed_id h⟩,?_⟩
  rintro ⟨a,b,rfl⟩; exact sheetId_fixed a b
end YM.CF.SatinStressData
