import Weft.Fiber
import Mathlib.RingTheory.RootsOfUnity.Complex
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Drift
namespace Grain
open Function Finset Mew
open scoped BigOperators Topology
variable {I E:Type}[Fintype I][LinearOrder I][AddCommGroup E][Module ℂ E]
local notation "nT" => (Fintype.card (PairKey I)+1) -- roots purchase at nT. DFT extraction
local notation "K"=> Key (PairKey I)
abbrev lights (n:ℕ):ℂ:=Complex.exp (2*Real.pi*Complex.I/n)
lemma light_prim {n:ℕ}(p:0<n):IsPrimitiveRoot (lights n) n:=Complex.isPrimitiveRoot_exp _ p.ne'
lemma light_one {n:ℕ}(p:0<n):‖lights n‖=1:=(light_prim p).norm'_eq_one p.ne'
attribute [-instance] instDecidableEqLex
local notation "WX" x:max => (lights (Fintype.card (PairKey x)+1))
-- coefficient 
noncomputable def rainbow (f:K→E)(z:K)(i:ℕ):E:= ((nT:ℕ):ℂ)⁻¹ • ∑ j∈range nT, ((WX I^j)^i)⁻¹ • f ((WX I^j) • z)
lemma crater{n i k:ℕ}(h:0<n)(p:i<n)(v:k<n): (∑ j∈range n, ((lights n ^ j)^i)⁻¹*((lights n ^ j)^k))=(if i=k then (n:ℂ) else 0):=by
 let z:=lights n; have he:z≠0:=by intro hz; have hf:=light_one h; rw [(show lights n=0 from hz),norm_zero] at hf; exact zero_ne_one hf
 have hl:= light_prim h
 by_cases hh:i=k
 · subst k; simp [he,show lights n≠0 from he]
 rw [if_neg hh]; let Q:= (z^i)⁻¹*z^k
 have hm: Q^n=1:=by unfold Q; simp only [mul_pow,inv_pow,←pow_mul]; rw [mul_comm i n, mul_comm k n,pow_mul z n,pow_mul z n,(show z^n=1 from hl.pow_eq_one),one_pow,one_pow,inv_one,mul_one]
 have hx:Q≠1:=by
    intro t; have hg:z^k=z^i:= by unfold Q at t; rw [mul_comm,←div_eq_mul_inv] at t; exact (div_eq_one_iff_eq (pow_ne_zero _ he)).mp t
    rcases lt_or_gt_of_ne hh with hv|hv
    · let u:=k-i; rw [show k=i+u by unfold u; omega,pow_add] at hg; exact hl.pow_ne_one_of_pos_of_lt (show u≠0 by unfold u; omega) (show u<n from (Nat.sub_le ..).trans_lt v) (mul_left_cancel₀ (pow_ne_zero _ he) (hg.trans (mul_one _).symm))
    let u:=i-k; rw [show i=k+u by unfold u; omega,pow_add] at hg; exact hl.pow_ne_one_of_pos_of_lt (show u≠0 by unfold u; omega) (show u<n from (Nat.sub_le ..).trans_lt p) (mul_left_cancel₀ (pow_ne_zero _ he) (hg.symm.trans (mul_one _).symm))
 have hQ:= mul_neg_geom_sum (x:=Q) n -- check
 rw [hm, sub_self] at hQ; have hp:= (mul_eq_zero.mp hQ).resolve_left (sub_ne_zero.mpr (Ne.symm hx))
 refine Eq.trans (sum_congr rfl (g:=fun j=>Q^j) ?_) hp
 intro j _; unfold Q z; rw [mul_pow,inv_pow]; simp only [←pow_mul]; rw [Nat.mul_comm i j,Nat.mul_comm k j]
lemma rainbow_chip(t:Finset (PairKey I))(F:PairKey I→Bool→ℂ)(v:E)(z:K)(i:ℕ)(hi:i<nT):
 let g(w:K):=(∏ j∈t, Drift.entry (F j) (yard j) w) • v
 rainbow g z i=(if t.card=i then g z else 0):=by
 intro g
 have he(a:ℂ):g (a • z)=a^t.card • g z:=by unfold g; simp_rw [Drift.entry,Pi.smul_apply,smul_eq_mul,mul_left_comm _ a,←mul_add a,prod_mul_distrib, prod_const]; rw [mul_smul]
 unfold rainbow; simp_rw [he, ←mul_smul, ←Finset.sum_smul]; rw [crater (show 0<nT from Nat.zero_lt_succ _) hi (Nat.lt_succ_of_le (card_le_univ _))]
 split_ifs with h h₁ <;> first|omega|rw [zero_smul,smul_zero]|rw [←mul_smul,inv_mul_cancel₀ (by exact_mod_cast (show nT≠0 from Nat.succ_ne_zero _)),one_smul]
lemma rainbow_plus {f g:K→E} (z:K)(i:ℕ): rainbow (fun z=> f z+g z) z i= rainbow f z i+rainbow g z i:=by unfold rainbow; simp only [smul_add,sum_add_distrib]
lemma shawl {D:Finset I}{f:Mew.Key (PairKey I)→E}(e:Grain D f)(z:K)(a:ℂ) : f (a • z)=∑ i∈ Ico 1 nT, a^i • rainbow f z i:=by
 induction e with
 | zero=> simp [rainbow]
 | add _ _ h v=> change _+_= _; simp_rw [rainbow_plus,smul_add,sum_add_distrib]; rw [h,v]
 | chip t F v p h u=>
   let g(w:K):=(∏ j∈t,Drift.entry (F j) (yard j) w) • v
   change g (a • z)=∑ i∈_,a^i • rainbow g z i
   have he:g (a • z)=a^t.card • g z:=by unfold g; simp_rw [Drift.entry,Pi.smul_apply,smul_eq_mul,mul_left_comm _ a,←mul_add a,prod_mul_distrib, prod_const]; rw [mul_smul]
   rw [he,sum_eq_single_of_mem t.card (mem_Ico.mpr ⟨card_pos.mpr p,Nat.lt_succ_of_le (card_le_univ _)⟩), rainbow_chip _ _ _ _ _ (Nat.lt_succ_of_le (card_le_univ _)),if_pos rfl]
   intro i ui pi; rw [rainbow_chip _ _ _ _ _ (mem_Ico.mp ui).2,if_neg (Ne.symm pi),smul_zero]
lemma shawl_zero {D:Finset I}{f:Mew.Key (PairKey I)→E}(e:Grain D f)(z:K){i:ℕ}(hi:i<nT)(p:D.card < i): rainbow f z i=0:=by
 induction e with
 | zero=>simp [rainbow]
 | add _ _ h v=>rw [rainbow_plus,h,v,add_zero]
 | chip s F v l g q=>
    rw [rainbow_chip _ _ _ _ _ hi,if_neg]
    intro he
    have hQ:s.card ≤ D.card := by rw [←card_image_of_injOn g]; exact card_le_card (image_subset_iff.mpr q)
    omega
#print axioms shawl
#check @shawl
end Grain
end YM.CF.Drift
