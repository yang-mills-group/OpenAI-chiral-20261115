import YM.CF.DPress.Wagon.Gamut
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
/-!
 Cash-normalized log-replication. This is the homogeneous-word technique of the proof of Lemma slotineq. For convenience we use maximum over the finite pattern library (each with supremum over marks of the indicated *class*). Thus we won't assert eq:ChessEQ separately for copies having exact common labels. Need U_P for ALL bounded-cost applications, and prove the cost version of eq:Chess-P with that use. Works because the homogeneous-process argument also proves: a positive maximum on words is still a maximum on each half-copy (both labels transported with same pricing). Doesn't claim copy consistency about a lap of the torus from a path of operations; only one boundary at a time. Doesn't need additional donor symmetries. -/
namespace Race.Credit
variable {T:Race n L}(A:Style T)(u:Reward T A){ℒ:Fixed.Test n→ℝ}(p:Bound T ℒ) {k m:ℕ}{s:List Bool}
def texts : (n:ℕ)→Finset (List Bool)
| 0=> {[]}
| i+1=> (univ ×ˢ texts i).image fun p=> p.1::p.2
lemma tal(k:ℕ)(s: List Bool):s∈ texts k↔ s.length=k:=by
 induction k generalizing s with
 | zero=> simp [texts]
 | succ k ih=> cases s <;> simp [texts,ih]
local notation "Q" => tariff A u ℒ
def Ahead (x:ℝ)(u:Reward T A)(ℒ:Fixed.Test n→ℝ)(s: List Bool)(m:ℕ) := s.length=m+m ∧ x=tariff A u ℒ s
lemma seat : ∃ (x:List Bool), x.length=m+m ∧∀ v:List Bool,v.length=m+m→ tariff A u ℒ v≤ tariff A u ℒ x:= by
 let n:=m+m; have hp: (texts n).Nonempty:= ⟨List.replicate n true,(tal ..).mpr (by simp)⟩; obtain ⟨x,p,v⟩:= exists_max_image _ (Q) hp; exact ⟨x,(tal ..).1 p,fun i h=>v i ((tal ..).2 h)⟩
variable (v:(m+m)*A.w=T.η){x:ℝ}(t:∀ s: List Bool,s.length=m+m→ tariff A u ℒ s ≤ x) (u0:0<x)
-- at a high word both copies preserve.SUP
local notation "P" => Ahead A x u ℒ
include t p v u0
lemma match_Q (B C: List Bool)(h:P (B++C) m)(w:B.length=m) : P (B++B.reverse) m∧ P (C.reverse++C) m:=by
 let S:= B++B.reverse; let F:=C.reverse++C; have hv:C.length=m:=by have he:=h.1; rw [List.length_append,w] at he; omega
 have he:S.length=m+m:=(by simp [S,w]); have ht:F.length=m+m:=(by simp [F,hv]); have hp:x*x≤ Q S* Q F:=by rw [h.2,←sq]; exact highTop A u p B C (w.trans hv.symm) (by rw [w,hv]; exact v)
 let n₁:=Q S; let n₂:= Q F
 have hj(S F: List Bool)(a:Q S* Q F ≥ x*x)(k: Q S≤x)(l: Q F ≤ x): x= Q S:=by
    apply le_antisymm _ k; by_contra! t'; have H: Q S* Q F < x*x:= (mul_le_mul_of_nonneg_left l (f_income A u p _)).trans_lt (mul_lt_mul_of_pos_right t' u0); exact H.not_ge a
 exact ⟨⟨he,hj S F hp (t _ he) (t _ ht)⟩,⟨ht,hj F S (mul_comm (Q S) (Q F) ▸ hp) (t _ ht) (t _ he)⟩⟩ -- tune
omit p t u0
lemma rotateH {B C:List Bool}(p:P (B++C) m) : P (C++B) m:=by
 have ht:(B++C).length=m+m:=p.1; have he:(C++B).length=m+m:=by simp only [List.length_append, add_comm C.length]; rw [←List.length_append]; exact ht
 refine ⟨he,?_⟩; rw [p.2,tariff,tariff, rotate_N A u _ _ _ _] -- use implicit signatures p omit? include h etc
 · rw [←List.length_append,ht,v]
 rw [←List.length_append,ht]; exact ⟨m,rfl⟩ -- name
omit v
lemma grow_E (b: Bool){s:List Bool}{k:ℕ}(h:k ≤ s.length):∃ x y: List Bool,s=x++y∧ x.length=k:=⟨s.take k,s.drop k,(List.take_append_drop ..).symm,by simp [h]⟩ -- remove m binder
include t p v u0
lemma final_Q {b:Bool}{K:ℕ}{w:List Bool}(e:P ((List.replicate K b) ++ w) m)(g:K ≤ m)(k:0<K):P (List.replicate (m+m) b) m :=by
 induction g using Nat.decreasingInduction generalizing w with
 | self=>
    obtain ⟨p,v⟩:= match_Q A u p v t u0 _ _ e List.length_replicate; rw [List.replicate_add]; simpa only [List.reverse_replicate] using p
 | of_succ l p' IH=>
    let R_:= List.replicate l b; have u' : R_.length=l:= List.length_replicate; have ht : l+w.length=m+m:=by simpa only [List.length_append,List.length_replicate] using (show (List.replicate l b ++ w).length=m+m from e.1)
    obtain ⟨x,y,h,mh⟩:= grow_E b (s:=w) (by omega : m-l ≤ w.length); have hp: P ((R_++x)++y) m:=by rw [List.append_assoc,←h]; exact e
    obtain ⟨hv,k'⟩:= match_Q A u p v t u0 (R_++x) y hp (by rw [List.length_append,u',mh]; omega);
    have he:P (R_++R_++x++x.reverse) m:=by
       rw [List.reverse_append,show R_.reverse=R_ from List.reverse_replicate] at hv;
       have h: P (R_++((R_++x)++x.reverse)) m:= rotateH A u v (by rw [List.append_assoc (R_++x)]; exact hv); simpa only [List.append_assoc] using h
    have c: l+l = (l+1)+(l-1):= by omega
    have hs:R_++ R_ = List.replicate (l+1) b ++ List.replicate (l-1) b:=by rw [← List.replicate_add, c,List.replicate_add]
    apply IH (w:=List.replicate (l-1) b ++x++x.reverse) ?_ (by omega); rw [hs] at he; simpa only [List.append_assoc] using he
end Race.Credit
end YM.CF.DPress.Wagon
