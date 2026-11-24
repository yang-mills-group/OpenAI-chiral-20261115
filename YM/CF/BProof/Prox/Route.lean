import YM.CF.BProof.Prox.Space

/-! Fixed-radius (special type) row addresses for the matrix pricing. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.Prox
open Function Filter Finset Matrix MeasureTheory Lattice Relation
open scoped Topology BigOperators Classical Matrix
variable {A I 𝕜 X: Type*} [Fintype A][Fintype I]
-- Agreement on a prescribed set; no equality unless stated. later unwrap packed Scopes.
structure Scope (X A:Type*) where
 upon : Finset A→X→X→Prop
 mono {S T: Finset A}{x y:X} (h:S⊆ T) (p:upon T x y) : upon S x y

namespace Scope
def flags (A:Type*) : Scope (Finset A) A where
 upon S T U:= ∀ i∈S,i∈T ↔ i∈U
 mono h p:=fun i ht=>p i (h ht)
end Scope

abbrev Pup (X I 𝕜:Type*) := X→ Matrix I I 𝕜
variable {B:Base A}(F:B.Index I) (S:Scope X A)
section
variable [Zero 𝕜] (Y : Pup X I 𝕜)(k:ℕ)
structure Via : Prop where
 door i j x : ¬ B.N (F.port i) (F.port j) k → Y x i j=0
 lock i x y : S.upon (B.ball (F.port i) k) x y→ ∀ j,Y x i j=Y y i j
end
namespace Via
variable {F S} {k T a:ℕ}
section
variable [Zero 𝕜]{Y : Pup X I 𝕜}
lemma le (H : Via F S Y k)(e:k≤T): Via F S Y T := ⟨fun i j x h=> H.door _ _ _ (mt (B.mono e) h),fun i x y h j=> H.lock i x y (S.mono (B.ball_le _ _ _ e) h) j⟩
end
section
variable [DecidableEq I]
lemma one [MulZeroOneClass 𝕜]: Via F S (fun _=> (1:Matrix I I 𝕜)) k := by
 refine ⟨fun i j x h=>?_,fun i x y h j=>rfl⟩; exact Matrix.one_apply_ne' (fun e=> h (e ▸ B.start _ k)) -- tune
end
lemma zero [Zero 𝕜] : Via F S (fun _=> (0:Matrix I I 𝕜)) k := ⟨fun i j x _=>rfl,fun i x y _ j=>rfl⟩
lemma add [AddZeroClass 𝕜] {Y Z : Pup X I 𝕜} (H: Via F S (B:=B) Y k)(w: Via F S Z k) : Via F S (Y+Z) k := by
 refine ⟨fun i j x h=>?_,fun i x y h j=> ?_⟩; simp only [Pi.add_apply, Matrix.add_apply,H.door i j x h,w.door i j x h,zero_add]; simp only [Pi.add_apply, Matrix.add_apply,H.lock i x y h,w.lock i x y h]
lemma neg [NegZeroClass 𝕜] {Y : Pup X I 𝕜} (H: Via F S (B:=B) Y k) : Via F S (-Y) k:=by
 refine ⟨fun i j x h=>?_,fun i x y h j=>?_⟩; simp only [Pi.neg_apply,Matrix.neg_apply,H.door i j x h, neg_zero]; exact congrArg Neg.neg (H.lock i x y h j)
lemma sub [AddGroup 𝕜] {Y Z:Pup X I 𝕜}(H: Via F S (B:=B) Y k)(w:Via F S Z k): Via F S (Y-Z) k := by rw [sub_eq_add_neg]; exact H.add w.neg
lemma pi_smul {E:Type*}[Zero 𝕜][SMulZeroClass E 𝕜]{Y:Pup X I 𝕜}(H: Via F S (B:=B) Y k) (c:E): Via F S (c • Y) k :=⟨fun i j x h=> by simp only [Pi.smul_apply, Matrix.smul_apply,H.door i j x h,smul_zero],fun i x y h j=> congrArg (c • ·) (H.lock i x y h j)⟩ -- name lookup
lemma sum [AddCommMonoid 𝕜] {J:Type*} (t:Finset J)(Y:J→ Pup X I 𝕜)(H: ∀ i∈t, Via F S (B:=B) (Y i) k): Via F S (∑ i∈t,Y i) k:= by
 induction t using Finset.induction_on with
 | empty=> rw [sum_empty]; exact zero
 | @insert i t u ih=> rw [sum_insert u]; exact (H _ (mem_insert_self ..)).add (ih (fun i h=>H _ (mem_insert_of_mem h)))
lemma mul [NonUnitalNonAssocSemiring 𝕜]{Y Z:Pup X I 𝕜}(H:Via F S (B:=B) Y k)(w:Via F S Z T): Via F S (Y*Z) (k+T):= by
 constructor
 · intro i j x h; change ∑ l,(Y x i l)*(Z x l j) =0; refine sum_eq_zero fun l _=> ?_; by_cases g:B.N (F.port i) (F.port l) k; rw [w.door _ _ x (fun p=> h (B.triangle g p)),mul_zero]; rw [H.door _ _ x g,zero_mul]
 intro i x y h j; change (Y x*Z x) i j=(Y y*Z y) i j; simp only [Matrix.mul_apply]; refine sum_congr rfl fun l _=>?_ ; by_cases hx:B.N (F.port i) (F.port l) k; swap; · rw [H.door _ _ _ hx,H.door _ _ _ hx,zero_mul,zero_mul]
 exact congrArg₂ (·*·) (H.lock _ _ _ (S.mono (B.ball_le _ _ _ (by omega)) h) _) (w.lock _ _ _ (S.mono (B.shares (k:=k) _ ((B.ball_m ..).2 hx) T) h) _)
lemma pow [DecidableEq I][Semiring 𝕜]{Y:Pup X I 𝕜}(H:Via F S (B:=B) Y k)(r:ℕ) : Via F S (Y^r) (k*r):= by
 induction r with |zero=> simp only [Nat.mul_zero,pow_zero]; exact one| succ r ih=> rw [pow_succ,Nat.mul_succ]; exact ih.mul H
end Via
end YM.CF.BProof.Prox
