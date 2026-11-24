import YM.CF.Urn.Shaft
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I α ι n m: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]
open Stilo Scree Hake
section
abbrev chim(K:ι→ι→ℂ)(L:ι→n→ℂ):ι→ FC (LinkI ι n):= largeH L+smallH K
-- scalar mixtures `mix` of transformed letters etc; bypass explicit tuple choices.
abbrev roseB (w:ι→ ι→ℂ)(F:ι→ FC n)(i:ι):FC n:=∑ j:ι,w i j • F j
def rateL (w:ι→ι→ℂ)(L:ι→n→ℂ)(i:ι)(j:n):ℂ:=∑ x:ι,w i x* L x j
def taxL (w K:ι→ι→ℂ)(i j:ι):ℂ:=∑ x:ι,∑ y:ι,w i x*w j y*K x y
lemma tallP (w:ι→ι→ℂ)(L:ι→n→ℂ):lank (rateL w L)=roseB w (lank L):=by
 funext i; unfold rateL lank roseB; simp only [sum_smul,mul_smul, smul_sum]; rw [sum_comm] -- tune
lemma rateW (w K: ι→ι→ℂ)(L:ι→n→ℂ)(D:List ι):acts (taskC (roseB w (lank L)) (Stilo.price (taxL w K) n) D) (pod n)=pailL seenH ∅ (chime (roseB w (chim K L)) (pod _) D):=by
 let G:=roseB w (largeH L); let H:=roseB w (smallH (n:=n) K); let U:=roseB w (chim K L); have he:U=G+H:=by funext i; unfold G H U roseB chim; simp only [Pi.add_apply,smul_add,sum_add_distrib]
 let Y:= pod (LinkI ι n); let B:= pailL (@seenH ι n) ∅; have h: Y=hoist seenH ∅ (pod n):=by unfold Y; rw [pod,hoops,knot_empty]
 have ht : Deck (@seenH ι n) ∅:= dH
 have hp(x:ι):acts (smallH K x) Y=0:=by
    unfold smallH; rw [act_sum]; apply sum_eq_zero; intro j _; rw [act_smul,show acts (takeF (flame j)) Y=0 from Eq.trans (take_act (n:=LinkI ι n) _ _) (if_neg (notMem_empty _)), smul_zero]
 have hu(i): acts (H i) Y=0:=by unfold H roseB; rw [act_sum]; simp_rw [act_smul,hp]; simp
 have hv(i j:ι): antiB (smallH (n:=n) K i) (chim K L j)=K i j • 1:=by
    rw [chim,Pi.add_apply,minus_sum, shoot L K]; unfold smallH; simp only [antiB_sum,antiB_sum',antiB_smul,antiB_smul',antiB,take_take,smul_zero,sum_const_zero,add_zero]; rfl
 have hk(i j:ι):antiB (H i) (U j)= Stilo.price (taxL w K) (LinkI ι n) i j:=by unfold H roseB U; simp_rw [roseB, Stilo.price,taxL,antiB_sum,antiB_sum',antiB_smul,antiB_smul',hv,sum_smul,smul_smul,mul_assoc]; rfl
 have hm(i:ι)(x:Wave (LinkI ι n)):B (acts (largeH L i) x)=acts (lank L i) (B x):=by
    have hp:flame (n:=n) i∉ lows seenH:=by simp only [lows,Finset.mem_map,mem_univ,true_and]; rintro ⟨j,h⟩; exact distinguish i j h.symm
    unfold B largeH lank; rw [act_add,map_add,show pailL seenH ∅ (acts (put (flame i)) x)=0 from branchX seenH ∅ ht hp (notMem_empty _) _,zero_add,act_sum,map_sum,act_sum]
    exact sum_congr rfl fun j _=> by rw [act_smul,map_smul,act_smul,show pailL seenH ∅ (acts (put (seenH j)) x)=_ from petals _ ∅ ht j x]
 have hf(i:ι)(x:Wave (LinkI ι n)):B (acts (G i) x)=acts (roseB w (lank L) i) (B x):=by unfold G roseB; rw [act_sum,act_sum,map_sum]; exact sum_congr rfl fun j _=> by rw [act_smul,map_smul,hm,act_smul]
 have hy:=devote U G H (roseB w (lank L)) Y B (taxL w K) he hu hk hf D; rw [show B Y=pod n from h ▸ pourL _ _ ht _] at hy; exact hy.symm
variable {o m':Type*}[Fintype o][LinearOrder o]
end
end YM.CF.Urn
