import GaugeFieldConstruction.ComplexColors
import Mathlib.Tactic
/-!
# Constant SU invariant tensors on the two species
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Matter
open CF Function Set Matrix Finset
open scoped Topology Matrix Matrix.Norms.Frobenius Kronecker BigOperators

def note (i a : F) : ℤ := if i=a then 4 else -1
def tall (i : F) : sl := ⟨Matrix.diagonal fun a => (note i a:ℂ), by
  rw [payable,Matrix.trace_diagonal]; rw [← Int.cast_sum, show ∀ i:F, ∑ k,note i k=0 from by decide +kernel]; simp⟩

def weight (i : F) (a : Sheet) : ℤ := Sum.elim (fun b:Ten=>note i b.val.1+note i b.val.2) (fun b:F => -note i b) a
lemma tilted (i : F) : repX (tall i).val = diagonal (fun a=> (weight i a:ℂ)) := by
  -- coordinate lift
  let n (a:F) : ℂ:= note i a
  have hp(b c:Ten) : ExTwo.gen (Matrix.diagonal n) b c= if b=c then n b.val.1+n b.val.2 else 0 := by
    rw [gen_entry]
    by_cases h : b=c
    · subst c; simp [Matrix.diagonal_apply,Matrix.one_apply, Ne.symm,b.property.ne]
    rw [if_neg h]; simp only [Matrix.diagonal_apply,Matrix.one_apply]
    have hu := b.property; have ht:=c.property
    have hm : b.val.1 ≠ c.val.1 ∨ b.val.2 ≠ c.val.2 := by by_contra! x; exact h (Subtype.ext <| Prod.ext x.1 x.2)
    split_ifs with h₁ h₂ h₃ h₄ <;> first | simp_all | grind
    order
  ext x y
  cases x <;> cases y <;>
    simp [repX,tall, weight, Join.both,Matrix.diagonal_apply, hp, n] -- hp interfering

lemma noticed : ∀ (i j : Sheet), (∀ k, weight k i=weight k j) → i=j := by decide +kernel

-- Lie weights force diagonal sheet
lemma plate (W : U) (p : pure W) : W=Matrix.diagonal W.diag := by
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.diag_apply]
  split_ifs with ht
  · subst j; rfl
  by_contra hv
  apply ht; apply noticed
  intro k
  have he := earned_pure W p (tall k); rw [tilted] at he
  have hz := Matrix.ext_iff.mpr he i j; rw [Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm (W i j)] at hz
  exact_mod_cast (mul_right_cancel₀ hv hz.symm)

def entry (i j : F) (h : i≠j) : sl := ⟨Matrix.single i j (1:ℂ),by rw [payable]; simp [h]⟩
-- Executable account of root generators on Sheet.
def intEntry (a b : F) (i j : Sheet) : ℤ := match i,j with
  | Sum.inl u,Sum.inl v => let m (i j : F) : ℤ:= if a=i ∧ b=j then 1 else 0
                            let n (i j:F) :ℤ :=if i=j then 1 else 0
                            m u.val.1 v.val.1*n u.val.2 v.val.2 + n u.val.1 v.val.1*m u.val.2 v.val.2-
                            (m u.val.1 v.val.2*n u.val.2 v.val.1+n u.val.1 v.val.2*m u.val.2 v.val.1)
  | Sum.inr u,Sum.inr v => if a=v ∧ b=u then -1 else 0
  | _,_ => 0
lemma actualEntry (a b) (h) (i j) : repX (entry a b h).val i j=(intEntry a b i j:ℂ) := by
  cases i <;> cases j
  · simp only [intEntry, repX,entry,Join.both,Matrix.fromBlocks_apply₁₁, CF.gen_entry]
    push_cast; simp [Matrix.one_apply,Matrix.single_apply]
  · simp [intEntry,repX,Join.both]
  · simp [intEntry,repX,Join.both]
  simp only [repX,entry,Join.both,Matrix.fromBlocks_apply₂₂,intEntry, Matrix.transpose_apply, Matrix.neg_apply,Matrix.single_apply]
  split_ifs <;> norm_num

lemma carry (W : U) (p : pure W) (a b : F) (h : a≠b) (i j) (ht : intEntry a b i j≠0) :
    W i i=W j j := by
  have hv := earned_pure W p (entry a b h); rw [plate W p] at hv
  have hm := Matrix.ext_iff.mpr hv i j; rw [Matrix.mul_diagonal,Matrix.diagonal_mul] at hm
  apply mul_right_cancel₀ (show (intEntry a b i j : ℂ)≠0 from by exact_mod_cast ht)
  change W.diag i * _ = W.diag j * _
  rw [← actualEntry a b h]; rw [hm,mul_comm]

def decisive (i j : Sheet) : Bool := decide (i=j) || decide (∃ a b,a≠b ∧ intEntry a b i j≠0)
lemma transfer (W : U) (p : pure W) (i j) (h : decisive i j=true) : W i i=W j j := by
  unfold decisive at h; simp only [beq_iff_eq, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain h|⟨a,b,v,w⟩:=h; rw [h]
  exact carry W p a b v i j w
lemma fpath : ∀ i j : F,decisive (.inr i) (.inr j)=true := by decide +kernel
lemma tpath : ∀ i j : Ten,∃ k : Ten,decisive (.inl i) (.inl k)=true ∧ decisive (.inl k) (.inl j)=true := by decide +kernel

def start : Ten := ⟨(0,4),by decide⟩
theorem pure_singular (W : U) : pure W ↔ ∃ a b:ℂ,W=Join.both (a • (1:Op Ten)) (b • (1:Op F)) := by
  constructor
  · intro h
    refine ⟨W (.inl start) (.inl start), W (.inr 0) (.inr 0),?_⟩
    have hx {x y} : W x y=if x=y then W x x else 0 := by
      exact (Matrix.ext_iff.mpr (plate W h) x y).trans (Matrix.diagonal_apply ..)
    ext i j; rw [hx]
    cases i with
    | inl a => cases j with
            | inl b=>
               by_cases e:a=b
               · subst b; simp [Join.both,Matrix.one_apply]
                 obtain ⟨k,p,t⟩ := tpath a start; exact (transfer W h _ _ p).trans (transfer W h _ _ t)
               simp [Join.both,Matrix.one_apply,e]
            | inr b=> rw [if_neg (by simp)]; rfl
    | inr a=>
      cases j with
      | inl b=> rw [if_neg (by simp)]; rfl
      | inr b => by_cases e:a=b
                 · subst b; simp [Join.both,Matrix.one_apply]; exact transfer W h _ _ (fpath a 0)
                 simp [Join.both,Matrix.one_apply,e]
  rintro ⟨a,b,rfl⟩ i; rw [blockRep,SU.each, Join.both_mul,Join.both_mul]; simp
end YM.GaugeFieldConstruction.Matter
