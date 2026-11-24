import SatinStress.Internal.Weights
/-!
# The E₀₄ root test for adjoint-valued Slot maps

Every such intertwiner between traceless complex Lie matrices and Sheet endomorphisms is
determined by its value on E₀₄, indeed by two entries there. (This is with the direct
sum representation `each` in the project.) Then we'll apply this fact to the
actual real-linear intertwiners from Color and to all of the generation indices.
-/
noncomputable section
namespace YM.CF.SatinStressData
open Gauge SU Function Matrix Finset
open Complex (I)
open scoped Matrix Kronecker Topology BigOperators

lemma through {i j k:F} : element i j * element j k = element i k := by simp [element]
lemma miss {i j k l:F} (h : j ≠ k) : element i j * element k l=0:= by unfold element; exact Matrix.single_mul_single_of_ne 1 i j k h 1
lemma neighbor {i j k : F} (h : i≠k) : commuteCost (element i j) (element j k)=element i k := by rw [commuteCost, through, miss h.symm,sub_zero]
lemma polarized {i j : F} : commuteCost (element i j) (element j i)=element i i-element j j := by rw [commuteCost, through,through]
lemma bilinear_reverse {X Y : Fund} : commuteCost X Y = -commuteCost Y X := by unfold commuteCost; abel
lemma adj_diff {f g} (h : AdjS f) (p : AdjS g) : AdjS (f-g) := by intro u A hx; simp only [LinearMap.sub_apply,mul_sub,sub_mul,h u A hx,p u A hx]

lemma directed {f : Fund →ₗ[ℂ] SheetEnd} (h : AdjS f) (z : f (element 0 4)=0) (Y : Fund) (e : trace Y=0) : f Y=0 := by
  have hs (A : Fund) (a : trace A=0) (B:Fund) (b : trace B=0) (u : f B=0) : f (commuteCost A B)=0 := by rw [differentiate_adj f h a b,u,commuteCost]; simp
  have ht (i:F) (g : i ≠ 4) : f (element i 4)=0 := by
    by_cases H:i=0
    · subst i; exact z
    rw [← neighbor (j:=0) g]; exact hs _ (rooted_zero H) _ (rooted_zero (by decide)) z
  have ha (i:F) : f (element 4 4) = f (element i i) := by
    by_cases g:i=4
    · rw [g]
    have he := hs _ (rooted_zero (Ne.symm g)) _ (rooted_zero g) (ht i g)
    rw [polarized,map_sub,sub_eq_zero] at he; exact he
  have hy (i j:F) (p:i≠j) : f (element i j)=0 := by
    by_cases hu:i=4
    · subst i
      have hd := hs _ (rooted_zero p) (element j j - element 4 4) (by simp [element]) (by rw [map_sub,ha j]; simp)
      -- expand
      rw [commuteCost,mul_sub,sub_mul,through,miss p.symm,miss p.symm,through] at hd
      simp only [sub_zero,zero_sub,sub_neg_eq_add,map_add] at hd
      ext a b; apply (add_self_eq_zero (R:=ℂ)).mp; exact Matrix.ext_iff.mpr hd a b
    by_cases hv:j=4
    · rw [hv]; exact ht i hu
    rw [← neighbor (j:=4) p, bilinear_reverse,map_neg, hs _ (rooted_zero (Ne.symm hv)) _ (rooted_zero hu) (ht i hu), neg_zero]
  have hh (i) : (∑ j:F, f (single i j (Y i j)))= Y i i • f (element 4 4) := by
    have hf (j:F)(z:ℂ) : f (single i j z) = z • f (element i j) := by unfold element; rw [← map_smul,Matrix.smul_single,smul_eq_mul,mul_one]
    rw [sum_eq_single i,hf,← ha i]
    · intro j _ hz; rw [hf,hy i j (Ne.symm hz),smul_zero]
    simp
  rw [matrix_eq_sum_single Y]; simp_rw [map_sum, hh]; rw [← sum_smul]; change trace Y • _ = _; rw [e,zero_smul]

local notation "U" => element 0 4

-- possible entries on a Lie intertwiner evaluated there.
def poleTop (j:F) (p : 0<j := by decide) : Sheet := .inl ⟨(0,j),p⟩
def poleBot (j:F) (p : j<4 := by decide) : Sheet := .inl ⟨(j,4),p⟩
def call (x y : Sheet) := (x=.inr 4 ∧ y=.inr 0) ∨ ∃ (j:F) (p:0<j) (q:j<4), x=poleTop j p ∧ y=poleBot j q
set_option synthInstance.maxSize 4096 in
lemma weights_root (x y : Sheet) (h : wt x = wt y + (wp 0 - wp 4)) : call x y := by
  have he : (x=Sum.inr 4 ∧ y=Sum.inr 0) ∨
      (x=poleTop 1 ∧ y=poleBot 1) ∨
      (x=poleTop 2 ∧ y=poleBot 2) ∨
      (x=poleTop 3 ∧ y=poleBot 3) := by decide +revert +kernel
  rcases he with e| p|p|p; exact Or.inl e
  · exact Or.inr ⟨1,by decide,by decide,p⟩
  · exact Or.inr ⟨2,by decide,by decide,p⟩
  exact Or.inr ⟨3,by decide,by decide,p⟩

lemma next_top (j:F) (p : 0<j) (q:j<4) : wt (poleTop j p) = wt (poleBot j q)+(wp 0-wp 4) := by
  unfold poleTop poleBot wt; dsimp; omega

lemma predicts {f : Fund →ₗ[ℂ] SheetEnd} (h : AdjS f) (x y : Sheet) (v : f U x y≠0) : wt x = wt y + (wp 0-wp 4) := by
  have t := differentiate_adj f h H_clear (rooted_zero (show (0:F) ≠ 4 by decide)); rw [H_price, show commuteCost H U = (((wp 0-wp 4:ℤ)):ℂ) • U by
    unfold element commuteCost H; ext i j; rw [Matrix.sub_apply,Matrix.smul_apply,diagonal_mul,mul_diagonal]; by_cases e:i=0 <;> by_cases h:j=4 <;> simp [e,h,eq_comm],map_smul] at t
  have e:= Matrix.ext_iff.mpr t x y; rw [Matrix.smul_apply,smul_eq_mul,commuteCost,Matrix.sub_apply,diagonal_mul,mul_diagonal,mul_comm (f U x y),← sub_mul] at e
  have he : wt x - wt y = wp 0 - wp 4 := by exact_mod_cast mul_right_cancel₀ v e.symm
  omega

lemma column_off {v : Sheet} {u : Sheet} {x : Sheet} (f : Fund →ₗ[ℂ] SheetEnd) (h : AdjS f)
    (p : wt u = wt v + (wp 0 - wp 4)) (hv : x ≠ u) : f U x v=0 := by
  by_contra e
  exact hv (distinct0 _ _ ((predicts h x v e).trans p.symm)) -- `..` not allowed?
lemma row_off {v : Sheet} {u : Sheet} {x : Sheet} (f : Fund →ₗ[ℂ] SheetEnd) (h : AdjS f)
    (p : wt u = wt v + (wp 0 - wp 4)) (hv : x ≠ v) : f U u x=0 := by
  by_contra e
  exact hv (distinct0 x v (add_right_cancel ((predicts h _ _ e).symm.trans p)))

set_option synthInstance.maxSize 2048 in
lemma rootMatch (k : F) (p : 0<k) (q : k<4) (e : k ≠ 1) :
   integerVersion (single k 1 1) (poleBot k q) (poleBot 1)=1 := by decide +revert +kernel

lemma carries_root {f : Fund →ₗ[ℂ] SheetEnd} (h : AdjS f) (z : f U (poleTop 1) (poleBot 1)=0)
    (k : F) (p : 0<k) (q:k<4) : f U (poleTop k p) (poleBot k q) = 0 := by
  by_cases hp:k=1
  · subst k; exact z
  have ht := differentiate_adj f h (rooted_zero hp) (rooted_zero (show (0:F) ≠ 4 by decide))
  let R:=spinRep (element k 1); have hK : R*f U=f U*R := sub_eq_zero.mp (ht.symm.trans (by
    rw [commuteCost, miss (by decide), miss q.ne', sub_self, map_zero]))
  have he(x) : f U x (poleBot 1)=0 := by by_cases u:x=poleTop 1; rw [u]; exact z; exact column_off f h (next_top _ (by decide) (by decide)) u
  have hy := Matrix.ext_iff.mpr hK (poleTop k p) (poleBot 1)
  simp only [Matrix.mul_apply, he, mul_zero,sum_const_zero] at hy
  rw [sum_eq_single (poleBot k q)] at hy
  · have hh : R (poleBot k q) (poleBot 1)=1 := by
      unfold R; rw [sees]; have he : integerVersion (single k 1 1) (poleBot k q) (poleBot 1)=1 := rootMatch k p q hp
      rw [he]; simp
    rw [hh, mul_one] at hy; exact hy.symm
  · intro a _ hx; rw [row_off f h (next_top k p q) hx,zero_mul]
  simp

lemma coefficients (a b : ℂ) : scheme a b U (poleTop 1) (poleBot 1) = -a ∧ scheme a b U (.inr 4) (.inr 0) = -b := by
  constructor
  · simp [scheme,poleTop,poleBot,Join.both,upper,gen_entry,one_apply,element]
  simp [scheme,Join.both,lower,element]
lemma follows (f : Fund →ₗ[ℂ] SheetEnd) (h : AdjS f) (a b : ℂ)
    (u : f U (poleTop 1) (poleBot 1) = -a) (v : f U (.inr 4) (.inr 0) = -b)
    {G : Fund} (p : G.trace=0) : f G = scheme a b G := by
  let Z := f - scheme a b
  have hx := adj_diff h (sector_scheme a b)
  have he : Z U (poleTop 1) (poleBot 1) = 0 := by simp [Z,u,(coefficients a b).1]
  apply sub_eq_zero.mp; apply directed hx _ G p
  ext x y
  change Z U x y=0
  by_contra q
  rcases weights_root x y (predicts (f:=Z) hx _ _ q) with ⟨rfl,rfl⟩|⟨k,H,T,rfl,rfl⟩
  · exact q (by simp [Z,v,(coefficients a b).2])
  exact q (carries_root hx he k H T)
end YM.CF.SatinStressData
