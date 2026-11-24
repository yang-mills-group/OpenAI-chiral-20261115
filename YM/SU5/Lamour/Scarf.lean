import YM.SU5.Lamour.Ferry
/-! # finite farm pricing of Mark vs the flat ray, uniform regardless I. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 190000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace Flare Pannier.Chancel Velvet Pannier.Damask Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[LinearOrder n][Fintype n][Fintype I][LinearOrder I]
variable {p R S:Finset I} {A P:Op I}{z v w U:ℝ}
lemma warp_bound (d:ℕ)(h:p.card≤ d)(w:0≤v)(t:∀ i∈p,∀ j∈ S,‖A i j‖≤ v): Bun A p S ((d:ℝ)+1+v):=by
 intro j tj; apply le_trans (sum_le_sum (g:=fun _=>v^2) (fun i hi=>pow_le_pow_left₀ (norm_nonneg _) (t i hi j tj) 2)) _; rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (sq_nonneg v)).trans; let W:= (d:ℝ)+1+v; have hx:1 ≤ W:=by unfold W; linarith [Nat.cast_nonneg (α:=ℝ) d]
 have hg:(d:ℝ)≤ W:=by unfold W; linarith; -- tune
 change _≤(W^2)^2
 apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ w (show v ≤ W from (by unfold W; linarith [Nat.cast_nonneg (α:=ℝ) d])) 2) (Nat.cast_nonneg d)) _; rw [sq (W^2)]; exact mul_le_mul_of_nonneg_right (hg.trans (by nlinarith)) (sq_nonneg _)
def plumeE (d:ℕ)(r v:ℝ): ℕ→ℝ
 | 0=> 0
 | k+1=>(d:ℝ)*(r^d+v*plumeE d r v k)
lemma plume_non {d n:ℕ}{r v:ℝ}(h:0≤r)(g:0≤v): 0≤plumeE d r v n:=by induction n with| zero=> exact le_rfl| succ k ih => unfold plumeE; positivity
lemma wake_priceT(P Q E F:ℂ)(v t B w W:ℝ)(T:Finset I)(i:I)(g: ‖P‖ ≤v)(h: ‖E‖≤ B)(q:‖F-E‖≤ w*W)(e: ‖P-Q‖≤w)(y:0≤ v): ‖P*(parity i T*F)-Q*(parity i T*E)‖ ≤ w*(B+v*W):=by
 let p:= parity i T; have hu:‖p‖=1:=(by simp [p,parity,norm_pow]); change ‖P*(p*F)-Q*(p*E)‖≤_; rw [show P*(p*F)-Q*(p*E)=P*(p*(F-E))+(P-Q)*(p*E) from (by ring)]
 apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,norm_mul,norm_mul,hu,one_mul,one_mul]; apply (add_le_add (mul_le_mul g q (norm_nonneg _) y) (mul_le_mul e h (norm_nonneg _) ((norm_nonneg _).trans e))).trans_eq; ring
lemma shawl (u:1≤U)(w':0≤w)(y:0≤v)(a:Aᵀ= -A)(q:Pᵀ= -P)(h:Bun P S S U)(p':∀ i∈ S,∀ j∈S,‖A i j‖≤ v)(t:∀ i∈ S,∀ j∈ S,‖A i j-P i j‖≤ w)(d:ℕ)(hx:S.card≤d)(k:ℕ)(g:R⊆S)(p:R.card≤ k):‖pf A R-pf P R‖≤ w*plumeE d U v k:=by
 have hU:0≤ U:= le_trans zero_le_one u; induction k generalizing R with
 | zero=> have he:R=∅:= card_eq_zero.mp (le_zero_iff.mp p); rw [he,pf,pf,paired_vac,paired_vac,sub_self,norm_zero,plumeE,mul_zero]
 | succ k ih=>
    by_cases f:R.Nonempty
    · let i:=R.min' f; have hv:i∈ R:=min'_mem R f; let T:=R.erase i; have hg: R=insert i T:=(insert_erase hv).symm; have hF:Flies i T:=fun j tj=>lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase tj)) (mem_erase.mp tj|>.1.symm); let N:=plumeE d U v k
      have ht:T⊆ S:= Finset.Subset.trans (erase_subset ..) g; have hp:T.card ≤ k:= Nat.le_of_succ_le_succ (le_trans ((card_erase_add_one hv).le) p)
      rw [hg, flair a hF,flair q hF, ←sum_sub_distrib]; apply (norm_sum_le ..).trans;
      have he:0≤N:=plume_non hU y
      refine (sum_le_sum (g:=fun _=>w*(U^d+v*N)) (fun j tj=>?_)).trans ?_
      · let e:T.erase j⊆ S:= Finset.Subset.trans (erase_subset j T) ht
        have V:= (p' i (g hv) j (ht tj)); exact wake_priceT _ _ _ _ v 0 _ _ _ _ _ V ((nest_lane q h e hU).trans (pow_le_pow_right₀ u (le_trans (card_le_card e) hx))) (ih e (le_trans (card_le_card (erase_subset j T)) hp)) (t i (g hv) _ (ht tj)) y
      rw [sum_const,nsmul_eq_mul, plumeE]; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_trans (card_le_card ht) hx)) (by positivity : 0 ≤ w*(U^d+v*N))).trans_eq (by unfold N; ring)
    rw [not_nonempty_iff_eq_empty.mp f,pf,pf,paired_vac,paired_vac,sub_self,norm_zero]; exact mul_nonneg w' (plume_non hU y)
variable [Nonempty n]{T: Finset n} {F Y: FC n}{A P Q:Op n}{D:Finset n}{b:Bool}
/-- cost of vacuum read center via ANY normalized functional on tomes. -/
def shell(E:FC n→ₗ[ℂ] ℂ)(T D: Finset n)(u:ℝ): Prop:=∀ p⊆D,‖E (tome T p)‖ ≤ u
lemma ledger_u (u:0≤U)(e:Fine T D b F) (d:ℕ)(Y:D.card ≤ d){E:FC n→ₗ[ℂ] ℂ}(h:shell E T D U) : ‖E F‖ ≤ 2^d*‖F‖*U:=by
 obtain ⟨w,hv,f⟩:=farm_bill e
 nth_rw 1 [f]; rw [map_sum]; apply (norm_sum_le ..).trans; apply le_trans (b:=∑ _∈D.powerset,‖F‖*U) (sum_le_sum (fun i p=>by rw [map_smul,norm_smul]; exact mul_le_mul (hv i (mem_powerset.mp p)) (h i (mem_powerset.mp p)) (norm_nonneg _) (norm_nonneg _))) ?_; rw [sum_const,nsmul_eq_mul,card_powerset,mul_assoc]; push_cast; gcongr <;> norm_num -- tune
-- sail application
variable {x y x': Wave n}(g: Clad P (cutM T) 1 1 Q){L: Op n}(wK:L=laneP (cutM T) 1 Q)(s:Sea P x)(f:Sea (cutM T) y)
def ray (L:Op n)(T: Finset n):= Hail (shadeK T) basisKet L
include g wK s f
lemma loft_shell (d:ℕ)(h:D.card≤d)(u:1≤U)(a:Bun (ray L T) D D U): shell (alleyR y x) T D (U^d):=by
 intro p v; rw [tome_rife,armed_pay _ _ p g wK f s (seedTrim T)]; exact (nest_lane (hail_turn ..) a v (le_trans zero_le_one u)).trans (pow_le_pow_right₀ u (le_trans (card_le_card v) h)) -- p
lemma near_shell (d:ℕ)(h:D.card≤d)(u:1≤ U)(a:Bun (ray L T) D D U) (q:0<z)(r:IsStarProjection A)(Y':Sea A x')(p':0≤v)(a':∀ i∈D,∀ j∈D,‖(ray (slant (cutM T) A z) T) i j‖≤ v)(e:0≤w)(t:∀ i∈ D,∀ j∈ D, ‖(ray (slant (cutM T) A z) T) i j-(ray L T) i j‖ ≤ w): shell (boomR x' (cutM_idp T) q-alleyR y x) T D (w*plumeE d U v d):=by
 intro p v; rw [LinearMap.sub_apply,tome_rife,oatHC (shadeK T) _ p q (cutM_idp _) r Y' (seedTrim T),armed_pay _ _ p g wK f s (seedTrim T)]; exact shawl u e p' (hail_turn ..) (hail_turn ..) a a' t d h d v (le_trans (card_le_card v) h)
lemma near_trust (q:0<z)(r:IsStarProjection A)(Y':Sea A x')(e:0≤w)(u:1≤U)(a:Bun (ray L T) D D U)(d:ℕ)(l:D.card≤ d)(p':0≤v)(a':∀ i∈D,∀ j∈D,‖(ray (slant (cutM T) A z) T) i j‖≤ v)(t:∀ i∈ D,∀ j∈ D, ‖(ray (slant (cutM T) A z) T) i j-(ray L T) i j‖ ≤ w)(F Y:FC n)(H:Fine T D false F)(X:Fine T D false Y): ‖boomR x' (cutM_idp T) q F-alleyR y x Y‖≤2^d*(‖F‖*(w*plumeE d U v d)+‖F-Y‖*U^d):=by
 let V:=boomR x' (cutM_idp T) q; let B:=alleyR y x; rw [show V F-B Y=(V-B) F+B (F-Y) by rw [LinearMap.sub_apply,map_sub]; abel]; apply (norm_add_le ..).trans; have hv: Fine T D false (F-Y):=by rw [sub_eq_add_neg,←neg_one_smul ℂ Y]; exact H.add (X.scale _)
 have ht:=near_shell g wK s f d l u a q r Y' p' a' e t; have hg:= loft_shell g wK s f d l u a; exact (add_le_add (ledger_u (mul_nonneg e (plume_non (le_trans zero_le_one u) p')) H d l ht) (ledger_u (pow_nonneg (le_trans zero_le_one u) d) hv d l hg)).trans_eq (by ring) -- rw show V
end YM.CF.Lamour
#print axioms YM.CF.Lamour.near_trust
