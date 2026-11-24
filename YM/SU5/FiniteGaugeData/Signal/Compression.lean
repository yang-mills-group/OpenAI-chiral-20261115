import YM.SU5.FiniteGaugeData.Signal.Antenna
/-!
# Linear density Gram interpolation
 Pay operator height while keeping exact charge exclusions at sampled nodes. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal.Sparkle
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea Supplies
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {I J:Type*}[Fintype I][LinearOrder I]
variable {N:Side}{a b u v:ℝ}{i j d k:ℕ}
namespace Condense
variable {W W': Finset I}{p: Ket I}
lemma closedCut_iff : acts (cutM W) p=p ↔ ∀ i, i∉W→p.ofLp i=0:= by
 constructor; · intro e i v; nth_rw 1 [←e]; rw [cut_apply, if_neg v]
 intro e; apply PiLp.ext; intro i; rw [cut_apply]; split; rfl; exact (e i (by assumption)).symm
lemma empties_iff : acts (cutM W) p=0 ↔∀ i∈ W,p.ofLp i=0:=by
 rw [←show acts (cutM Wᶜ) p=p ↔ acts (cutM W) p=0 by rw [dim_cut,act_sub,act_one]; exact sub_eq_self]; simp [closedCut_iff] -- name
lemma closedCut (t:W⊆W')(p':acts (cutM W) p=p):acts (cutM W') p=p:=by apply closedCut_iff.mpr; exact fun i x=> closedCut_iff.mp p' i (mt (fun e=> t e) x)
lemma sectorwiseCut {Q: Op I}(e:∀ i∈W,∀ j,j∉W→Q j i=0)(p':acts (cutM W) p=p): acts (cutM W) (acts Q p)=acts Q p:= by
 apply closedCut_iff.mpr; intro i h; rw [act_at]; change ∑ j:I, Q i j*p.ofLp j=0; apply sum_eq_zero; intro j _; by_cases v:j∈W; rw [e _ v _ h,zero_mul]; rw [closedCut_iff.mp p' j v,mul_zero]
lemma inwardCut (t:W ⊆ W')(p: Ket I): acts (cutM W) (acts (cutM W') p)=acts (cutM W) p:=by
 apply PiLp.ext; intro i; rw [cut_apply, cut_apply,cut_apply]; split; rename_i v; rw [if_pos (t v)]; rfl
-- oracle for cross terms
variable [Nonempty I]
include p
lemma column_credit {A B: Op I}(h:‖A-B‖ ≤ u): |(inner ℂ p (acts A p)).re-(inner ℂ p (acts B p)).re| ≤ u*‖p‖^2:=by
 rw [←Complex.sub_re,←inner_sub_right,←act_sub]; exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((Flare.opy ..).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring)))
-- Given on-site price and small finite-range remainder, retains enough after packing.
variable {A B:Op I}{W:J→ Finset I}{S:Finset J} (f:(S:Set J).Pairwise fun i j=> Disjoint (W i) (W j)) -- projection coe Set, tune
variable (fd:(S:Set J).Pairwise fun i j=> cutM (W i)*B*cutM (W j)=0) (e:∀ i∈ S,∀ x:Ket I, acts (cutM (W i)) x=x→v*‖x‖^2 ≤ (inner ℂ x (acts A x)).re)
local notation "U0"=> S.biUnion W
include f fd e
set_option maxHeartbeats 520000 in
lemma packed (z: acts (cutM (S.biUnion W)) p=p)(a:‖A-B‖≤u): (v-2*u)*‖p‖^2 ≤ (inner ℂ p (acts A p)).re:=by
 let y (i:J):=acts (cutM (W i)) p; have he(i:J):acts (cutM (W i)) (y i)=y i:=Retain.bore (cutM_idp _) _ -- open
 have hz: (∑ i∈S,y i)=p:=by
    apply PiLp.ext; intro x; rw [WithLp.ofLp_sum,Finset.sum_apply]; simp_rw [y,cut_apply]; by_cases v:x∈ S.biUnion W
    · obtain ⟨j,v,t⟩:=mem_biUnion.mp v; rw [sum_eq_single_of_mem _ v (fun i p e=> if_neg (fun k=>Finset.disjoint_left.mp (f (x:=i) (y:=j) p v e) k t)),if_pos t]
    rw [sum_eq_zero fun i h=> if_neg (fun w=>v (mem_biUnion.mpr ⟨_,h,w⟩)),closedCut_iff.mp z x v]
 have hl(T:Op I)(t:(S:Set J).Pairwise fun i j=> cutM (W i) *T*cutM (W j)=0): inner ℂ p (acts T p) =∑ i∈S,inner ℂ (y i) (acts T (y i)):=by
    nth_rw 1 2 [←hz]; rw [sum_inner]; apply sum_congr rfl; intro i b; rw [map_sum,inner_sum]; apply sum_eq_single_of_mem i b; intro j g w
    unfold y; rw [←act_mul, ←(cutM_idp (W i)).isSelfAdjoint.star_eq, act_inner,←act_mul,←mul_assoc, t b g (Ne.symm w), act_zero,inner_zero_right] -- using eq? tune rewritesp
 have h: ‖p‖^2=(∑ i∈ S,‖y i‖^2):=by
    apply Complex.ofReal_injective; push_cast; have hh:= hl 1 ?_; swap
    · intro i p j h hi; rw [mul_one]; unfold cutM; rw [Matrix.diagonal_mul_diagonal]; ext x y; by_cases v:x=y
      · subst y; by_cases g:x∈W i; · simp [g,fun (l:x∈W j)=>Finset.disjoint_left.mp (f p h hi) g l]
        simp [g]
      simp [v]
    simp_rw [act_one,inner_self_eq_norm_sq_to_K] at hh; exact hh
 have hp:(v-u)*‖p‖^2 ≤ (inner ℂ p (acts B p)).re:=by
    rw [h,hl B fd,Complex.re_sum,mul_sum]; apply sum_le_sum; intro i q; have hg:= abs_le.mp (column_credit (p:=y i) a); linarith only [(e i q _ (he i)),hg.2]
 have hy:= abs_le.mp (column_credit (p:=p) a); linarith only [hp,hy.1]
end Condense
end YM.CF.Signal.Sparkle
#print axioms YM.CF.Signal.Sparkle.Condense.packed
