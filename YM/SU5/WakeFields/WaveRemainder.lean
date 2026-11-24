import YM.SU5.WakeFields.Flood
import YM.SU5.Exchange.Seed.Keys

/-!
# Filtered Shelf for layer count ≠ degree

This is where `leg_Ρ` used to need pure solvent. Now even the previously billed
children in `Q` can depend on this Key. The BOOK and the CUT used with it are BOTH allowed
to vary. Only a one-higher layer is paid in each use of K. No Cauchy consortium summing
over all layer orders, only the finite path recurrence. No topology on Copy.
-/
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.CF.Cadre
open Function NormedSpace Filter Finset Finsupp PowerSeries Lattice Cube
open Skye Scree Mew Palot
open scoped Topology ContDiff BigOperators Classical Push.AbsoluteSums
set_option maxHeartbeats 300000
variable {A N I E : Type*} [Fintype I] [LinearOrder I] [NormedCommRing N] [NormedAlgebra ℂ N] [CompleteSpace N]
section
variable (c : ℕ)
variable (X : PowerSeries N)
abbrev slice (c : ℕ) (X : PowerSeries N) : N := ∑ k∈range (c+1), coeff k X

-- keep helper for bump evaluated at height
private def grange (r : ℕ) (G : PowerSeries N) := PowerSeries.mk (fun j=> if j ≤ r then coeff j G else 0)
private lemma coeff_grange (r i : ℕ) (G : PowerSeries N) :
    coeff i (grange r G) = if i ≤ r then coeff i G else 0 := coeff_mk ..
private lemma small_eval (m : ℕ) (F : PowerSeries N) (h : ∀ i, i ≥ m → coeff i F=0) :
    Aqua F ∧ hitU F = ∑ i∈range m,coeff i F :=
 ⟨summable_of_ne_finset_zero (s:=Finset.range m) (fun i v=> by rw [h i (Nat.le_of_not_gt (mt mem_range.mpr v)),norm_zero]),
    tsum_eq_sum (fun i v=>h i (Nat.le_of_not_gt (mt mem_range.mpr v)))⟩
private lemma grange_eval (r : ℕ) (G : PowerSeries N) : Aqua (grange r G) ∧ hitU (grange r G) = slice r G := by
 obtain ⟨p,t⟩:= small_eval (r+1) (grange r G) (fun i v=> by rw [coeff_grange,if_neg]; omega)
 refine ⟨p,t.trans (sum_congr rfl fun i v=>?_ )⟩
 rw [coeff_grange,if_pos (Nat.lt_succ_iff.mp (mem_range.mp v))]
variable (S : Finset A) (Z : A → PowerSeries N)
private lemma reduce_slice :
    ∏ i ∈ S,slice c (Z i) = slice (c * (1+S.card)) (∏ i∈S, grange c (Z i)) := by
 let F (i) := grange c (Z i); let G := ∏ i∈S,F i
 calc
    ∏ i∈S, slice c (Z i) = ∏ i∈S,hitU (F i) := prod_congr rfl (fun i _=> (grange_eval ..).2.symm)
    _ = hitU G := (Aqua.ψ_m S F (fun i _=> (grange_eval ..).1)).2.symm
    _ = _ := (small_eval _ G (fun i h=>?_)).2
 unfold G; rw [coeff_prod]; apply sum_eq_zero; intro k w
 have he: ∃ i∈S,c<k i := by
    by_contra! v
    have ht:=sum_le_sum v; rw [(mem_finsuppAntidiag.mp w).1, sum_const, smul_eq_mul] at ht
    rw [mul_add, mul_one, Nat.mul_comm c S.card] at h; omega
 obtain ⟨j,x,e⟩:=he
 exact prod_eq_zero x ((coeff_grange ..).trans (if_neg (not_le.mpr e)))
private lemma same_levels (m : ℕ) (t : m ≤ c) :
    coeff m (∏ i ∈ S, grange c (Z i)) = coeff m (∏ i∈S,Z i) := by
 rw [coeff_prod,coeff_prod]
 refine sum_congr rfl fun j v=> prod_congr rfl (fun i u=>?_)
 rw [coeff_grange,if_pos]
 exact ((single_le_sum (fun i _=>Nat.zero_le (j i)) u).trans_eq (mem_finsuppAntidiag.mp v).1).trans t
end
variable (S : Finset A) (F : A → Key I → PowerSeries N)
variable (p : ∀ i∈S,∀ k : ℕ, Flood k (fun x => coeff k (F i x)))
include p
lemma waveCoeff (c : ℕ) : Flood c (fun x=> coeff c (∏ i ∈ S,F i x)) := by
 simp_rw [coeff_prod]
 apply Flood.total; intro j v; let g (i : A) := j i
 exact (mem_finsuppAntidiag.mp v).1 ▸ Flood.purchase S (fun i x=> coeff (j i) (F i x)) g (fun i w=> p i w _)

lemma wakeEnd (c : ℕ) : Flood (c+1)
    (fun x=> (∏ i∈ S, slice c (F i x)) - slice c (∏ i ∈ S,F i x)) := by
 let L:=range (c+1); let J:= range (c*(1+ S.card) + 1); have hs : L ⊆ J := range_mono (add_le_add_left (Nat.le_mul_of_pos_right _ (show 0<1+S.card by omega)) _)
 let K:= J \ L; let V(i x):= grange c (F i x); let W(i : ℕ)(x):= coeff i (∏ i∈ S,V i x)
 have he(x): (∏ i∈ S, slice c (F i x))-slice c (∏ i ∈ S,F i x)=∑ i∈K,W i x := by
    rw [reduce_slice c S (fun i=> F i x)]
    rw [show slice c (∏ i∈S,F i x)= ∑ i∈L,W i x from sum_congr rfl (fun i t=>(same_levels c S (fun i=>F i x) i (Nat.lt_succ_iff.mp (mem_range.mp t))).symm)]; change (∑ i∈J,_) - _=_; rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
 simp_rw [he]
 refine Flood.total K W (fun i v=> Flood.lower (p:=i) (waveCoeff S V ?_ i) ?_)
 · intro j w k
   unfold V; simp_rw [coeff_grange]; split
   · exact p j w k
   exact Flood.null _
 exact Nat.le_of_not_gt (mt mem_range.mpr (mem_sdiff.mp v).2)

omit p
variable [Fintype A] [DecidableEq A]
variable (F : Mew.Key I → leaf A→ PowerSeries N)
variable (h : ∀ i : leaf A,∀ k : ℕ,Flood k (fun x=> coeff k (F x i)))
variable (O : Finset A)
include h
lemma gasCoeff (r : ℕ) : Flood r (fun z=> coeff r (hGas O (F z))) := by
 unfold hGas; simp_rw [map_sum]; exact Flood.total _ _ (fun i _=> waveCoeff i _ (fun j _=> h j) r)
lemma wakeGas (r : ℕ) : Flood (r+1) (fun z => (hGas O (slice r ∘ F z)) - slice r (hGas O (F z))) := by
 let W:=Cadre.stream O
 let V(i : hook A) (x : Key I):= (∏ j∈i,slice r (F x j)) - slice r (∏ j∈i,F x j)
 apply (Flood.total W V (p:=r+1) (fun i _=> wakeEnd i _ (fun j _ => h j) r)).cong
 intro z _; change _=∑ i∈W,V i z; unfold hGas slice V slice; rw [sum_sub_distrib]; simp_rw [map_sum]; exact congrArg ((∑ i∈ W,∏ j∈i,(slice r ∘ F z) j) - ·) Finset.sum_comm
end YM.CF.Cadre
#print axioms YM.CF.Cadre.wakeGas
