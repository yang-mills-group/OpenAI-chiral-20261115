import YM.SU5.Lamour.Revel
import YM.SU5.Velvet.Viper
import YM.SU5.FiniteGaugeData.Pannier.Hollow
/-! # Contraction price. ANY global selected S from copies, length ANY k from Yen rolls. Pay UNSPLIT letters by pf & column ℓ² estimate under slanted Sea. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 14336
set_option maxHeartbeats 180000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace Flare Pannier.Chancel Pannier.Damask Velvet
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n:Type*}[LinearOrder n][Fintype n][LinearOrder I]{C A:I → FC n}{S T:Finset I}{X:Wave n}{u v U:ℝ}{k:ℕ}
lemma pause_zero (h:Pause A 0 X)(i:I):acts (A i) X=0:=by simpa [fo] using h [i] (by simp)
lemma pause_t (h:Pause A (k+1) X)(i:I):Pause A k (acts (A i) X):= fun l t=>by rw [←act_mul, show fo A l * A i =fo A (l++[i]) from (by simp [fo]),h _ (by simp; omega)]
lemma operate_f (Z: FC n)(Y:Wave n): ‖acts Z Y‖≤‖Z‖*‖Y‖:=by rw [← Matrix.l2_opNorm_toEuclideanCLM Z]; exact (acts Z).le_opNorm _
theorem native_cost (y:0≤v)(p:1≤u)(a:∀ i∈ S,‖A i‖≤v*u)(c:∀ i∈S,‖C i‖≤ v)(h:Pause A k X): ‖acts (nest C A S) X‖ ≤ (2*v)^S.card * u^k * ‖X‖ :=by
 have ht:0≤u:= le_trans zero_le_one p; induction S using Finset.induction_on_min generalizing X k with
 | empty=> simp; exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ p)
 | insert i S g ih=>
    have he {X k}(h:Pause A k X): ‖acts (nest C A S) X‖≤(2*v)^S.card*u^k*‖X‖:=ih (fun i t=> a _ (mem_insert_of_mem t)) (fun i t=>c _ (mem_insert_of_mem t)) h
    let Y:=acts (A i) X; let N:=nest C A S; let P:=acts N X; let T:= acts N Y
    rw [card_insert_of_notMem (Flies.out g),pow_succ,nest_f C A g]; change ‖acts (C i*N+ signum S • (N*A i)) X‖ ≤_
    rw [act_add,act_smul,act_mul,act_mul]; apply (norm_add_le ..).trans; rw [norm_smul,show ‖signum S‖=1 from puff_norm _,one_mul]; change ‖acts (C i) P‖ + ‖T‖ ≤ _
    have hx: ‖T‖ ≤ (2*v)^S.card*u^k*(v*‖X‖):= by
       cases k with
       | zero=> unfold T Y; rw [pause_zero h i,map_zero,norm_zero]; positivity
       | succ k=> apply (he (pause_t h i)).trans; rw [pow_succ]; apply (mul_le_mul_of_nonneg_left ((operate_f ..).trans (mul_le_mul_of_nonneg_right (a _ (mem_insert_self ..)) (norm_nonneg _))) (pow_nonneg ht k |> fun e=> mul_nonneg (by positivity) e)).trans_eq; ring
    apply (add_le_add ((operate_f ..).trans (mul_le_mul (c _ (mem_insert_self ..)) (he h) (norm_nonneg _) y)) hx).trans_eq; ring
lemma nest_fall (e:S.Nonempty)(c:∀ i∈ S,acts (star (C i)) X=0)(a:∀ i∈S,acts (A i) X=0): inner ℂ X (acts (nest C A S) X)=0:=by
 let i:=S.min' e; have hv:i∈ S:=min'_mem S e; let T:=S.erase i; have ht:S=insert i T:=(insert_erase hv).symm; have hx:Flies i T:=fun j tj=>lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase tj)) (mem_erase.mp tj|>.1.symm)
 rw [ht,nest_f C A hx]; change inner ℂ X (acts (pressFun _ _ _ _) X)=_; rw [pressFun,act_add,act_smul,act_mul,act_mul, a _ hv, map_zero,smul_zero,add_zero,←act_inner,c _ hv,inner_zero_left]
variable [Fintype I]{K:Op I}
theorem nest_rude (p:Kᵀ= -K)(h:∀ j∈ S,∑ i, ‖K i j‖^2 ≤ (v^2)^2)(y:0≤v) : ‖pf K S‖ ≤ v^S.card:=by
 have he: ‖wedge K S‖ ≤ (v^2)^S.card:=by
    induction S using Finset.induction_on_min with
    | empty=>simp [wedge_empty,vacuum]
    | insert i S e ih=>
       let u:= acts K (basisKet i); have hz:‖u‖≤v^2:=by apply (sq_le_sq₀ (norm_nonneg _) (sq_nonneg _)).1; rw [EuclideanSpace.norm_sq_eq]; apply (h i (mem_insert_self ..)).trans'; refine sum_le_sum fun j _=>?_ ; rw [show u j=K j i from basis_act K j i] -- tune
       rw [wedge_min _ _ _ e, card_insert_of_notMem (Flies.out e), pow_succ']; exact (operate_f ..).trans (mul_le_mul ((cost_pe false _).trans hz) (ih (fun j tj=> h _ (mem_insert_of_mem tj))) (norm_nonneg _) (sq_nonneg _))
 apply (sq_le_sq₀ (norm_nonneg _) (pow_nonneg y _)).1; rw [← norm_pow, pf_square _ _ p,quantum_at,←basis_inner,←pow_mul,pow_mul' v]; exact (norm_inner_le_norm ..).trans (by simpa using he)
-- localized version pf_lane
abbrev Bun (K:Op I)(S T:Finset I)(v:ℝ):Prop:= ∀ j∈T,∑ i∈S, ‖K i j‖^2 ≤ (v^2)^2
lemma nest_lane (p:Kᵀ= -K)(h:Bun K S S v)(e:T⊆S)(y:0≤v): ‖pf K T‖≤v^T.card:=by
 let D:= cutM S; let A:=D*K*D; have hx(i j):A i j= if i∈ S ∧ j∈ S then K i j else 0:=by unfold A D cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases h:i∈ S<;> by_cases q:j∈ S<;> simp [h,q]
 have he {T: Finset I}(h:T⊆S):quant A T T=quant K T T:=by unfold A; rw [quant_mul, quant_mul, show quant D=cutM S.powerset from quantCut _,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,if_pos (mem_powerset.mpr h),one_mul,mul_one]
 have hg:Aᵀ= -A:=by unfold A; rw [Matrix.transpose_mul, Matrix.transpose_mul,p,show Dᵀ=D from self_t S,neg_mul,mul_neg,mul_assoc]
 have hv:‖pf A T‖^2=‖pf K T‖^2:=by rw [← norm_pow,←norm_pow,pf_square _ _ p,pf_square _ _ hg,he e];
 apply (nest_rude hg _ y).trans'; exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hv.ge
 intro j fj; rw [← sum_subset (subset_univ S) ]; exact (h j (e fj)).trans' (Eq.le (sum_congr rfl fun i q=>by rw [hx i j,if_pos ⟨q,e fj⟩])); intro i ti w; simp [hx i j,w]
@[simp] lemma bow_limit(S T:Finset I): ‖bow T S‖=1:=by unfold bow parity; rw [norm_prod]; simp
/-- interpolate estimate -/
theorem power_price(p:Kᵀ= -K)(q:Bun K S S v)(h:Pause A k X)(z:1≤u)(w:0≤v)(a:∀ i∈ S,‖A i‖≤v*u)(c:∀ i∈ S,‖C i‖≤v):‖acts (wake C A K S) X‖ ≤ (4*v)^S.card * u^k * ‖X‖:=by
 let x:=(2*v)^S.card*u^k*‖X‖; rw [wake,act_sum]; apply (norm_sum_le ..).trans; apply le_trans (sum_le_sum (g:=fun _=>x) _) (Eq.le ?_)
 · intro T t; let D:=S \ T; have ht:T⊆ S:= mem_powerset.mp t; have hu:0≤u:=le_trans zero_le_one z; rw [stir,act_smul,norm_smul,norm_mul,bow_limit,one_mul]; have hp:D⊆ S:=sdiff_subset
   refine (mul_le_mul ((nest_lane p q ht w).trans (pow_le_pow_left₀ w (show v≤2*v by linarith) T.card)) (native_cost w z (fun i (ti:i∈D)=>a i (hp ti)) (fun i (ti:i∈D)=> c i (hp ti)) h) (norm_nonneg _) (by positivity)).trans_eq ?_; unfold x; rw [←mul_assoc,←mul_assoc,←pow_add,add_comm,card_sdiff_add_card_eq_card ht]
 unfold x; rw [sum_const,nsmul_eq_mul,card_powerset]; push_cast; rw [show 4*v=2*(2*v) from by ring,mul_pow (2:ℝ) (2*v)]; ring
@[simp] lemma bow_erase_empty(S:Finset I): bow S ∅=1:=by simp [bow,parity]
lemma main_w (hX:‖X‖=1)(a:∀ i∈ S,acts (A i) X=0)(c:∀ i∈ S,acts (star (C i)) X=0)(K:Op I) : inner ℂ X (acts (wake C A K S) X)=pf K S:=by
 rw [wake,act_sum,inner_sum,sum_eq_single_of_mem S (mem_powerset.mpr subset_rfl)]; · simp [stir,inner_smul_right,act_smul,inner_self_eq_norm_sq_to_K (𝕜:=ℂ),hX]
 intro T t p; have he:S⊆T→ T=S:=fun w=> le_antisymm (mem_powerset.mp t) w; rw [stir,act_smul,inner_smul_right,nest_fall (sdiff_nonempty.mpr (mt he p)) (fun i ti=>c _ (mem_sdiff.mp ti).1) (fun i ti=> a _ (mem_sdiff.mp ti).1),mul_zero]
end YM.CF.Lamour
#print axioms YM.CF.Lamour.power_price
#print axioms YM.CF.Lamour.main_w
