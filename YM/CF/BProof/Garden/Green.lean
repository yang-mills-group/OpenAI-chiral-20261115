import YM.CF.BProof.Garden.Settle
/-! Crop and exact coupling factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I]
def square (S:Finset I)(C:Op I):Op I := cutM S*C*(cutM S)
def plump (S:Finset I)(C:Op I):FC I:=exp (coupl (square S C))*berth S
lemma square_entry (S:Finset I)(C:Op I)(i j:I): square S C i j=if i∈S ∧ j∈S then C i j else 0:=by
 unfold square cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases h:i∈S <;> by_cases g:j∈S <;> simp [h,g]
@[fun_prop] lemma plump_cont (S:Finset I):Continuous (plump S):=by
 letI : NormedAlgebra ℚ (FC I):=NormedAlgebra.restrictScalars ℚ ℂ (FC I); unfold plump square; fun_prop
lemma square_tr (S:Finset I){C:Op I}(x:Cᵀ= -C) : (square S C)ᵀ= - square S C:=by simp only [square,Matrix.transpose_mul,self_t,x,neg_mul,mul_neg,mul_assoc]
lemma coupl_tick (S:Finset I)(C:Op I): coupl (square S C)=(2:ℂ)⁻¹ • ∑ i∈S, ∑ j∈S,C i j • (put i * put j) :=by
 unfold coupl squareP; congr 1; simp only [square_entry,ite_smul,zero_smul]; rw [← sum_subset (s₁:=S) (subset_univ _) (by intro i _ hi; simp only [hi,false_and,ite_false,sum_const_zero])]; apply sum_congr rfl; intro i hi; rw [← sum_subset (s₁:=S) (subset_univ _) (by intro j _ hj; rw [if_neg (by simp [hj])])]; exact sum_congr rfl fun j hj=> if_pos ⟨hi,hj⟩
lemma coupl_here(S:Finset I)(C:Op I): Sector S false (coupl (square S C)):=by rw [coupl_tick]; exact (Sector.sumS _ _ fun i hi=> Sector.sumS _ _ (fun j hj=> ((Sector.up i hi).mul (Sector.up j hj)).scale _)).scale _ -- tune
lemma tuft (S:Finset I)(C:Op I) : Sector S false (exp (coupl (square S C))):=by
 rw [exp_eq_tsum ℂ]; dsimp only; rw [tsum_eq_sum (s:=range (Fintype.card I+1))]; apply Sector.sumS; · intro i hh; clear hh; apply Sector.scale; induction i with
   | zero=>rw [pow_zero]; exact Sector.one
   | succ i ih=> rw [pow_succ]; exact ih.mul (coupl_here ..)
 intro i hi; rw [mem_range] at hi; rw [coupl_nil _ i (by omega),smul_zero]
lemma plump_here (S:Finset I)(C:Op I): Sector S false (plump S C):=(tuft ..).mul berth_stays
lemma plump_id (S:Finset I)(C:Op I): plump S C * berth S=plump S C:=by unfold plump; rw [mul_assoc,berth_idp]
@[simp] lemma plump_vac(S:Finset I)(C:Op I): acts (plump S C) (vacuum I)=pairWave (square S C):=by rw [plump,act_mul,berth_vac,stored]
lemma plump_law {U:UNI I}{S:Finset I}(g:Commute U.val (cutM S))(C:Op I): twist (quantU U) (plump S C)=plump S (congrC U C):=by
 have he:square S (congrC U C)=congrC U (square S C):=by unfold square congrC; have hp : U.valᵀ*cutM S=cutM S*U.valᵀ:= transpose_cut g.eq; simp only [←mul_assoc]; rw [←g.eq]; simp only [mul_assoc,hp] -- tune
 have hc:cutM (∅:Finset I)=0:=by ext i j; by_cases h:i=j<;>simp [cutM,h]
 rw [plump,map_mul,breeze_exp,cabin_spin (p:=∅) (q:=S) (Finset.disjoint_empty_left S) (by rw [hc]; exact Commute.zero_right _) g, plump,he]; congr 2
 rw [twist_formula]; change (quant U.val* _)*star _=_; rw [coupl_cov,mul_assoc, show quant U.val*star ((quantU U).val)=1 from (quantU U).property.2,mul_one]; rfl
lemma plump_slot {p q:Finset I}(d:Disjoint p q)(C:Op I): acts (cabin p q*plump (p∪q) C) (vacuum I) = pf C p • basisKet p:=by
 let S:=p∪q; rw [act_mul,sideSlot d (homeZone (plump_here ..)),plump_vac]; congr 1
 change (pairWave (cutM S*C*_)).ofLp p=(pairWave _).ofLp p
 nth_rw 2 [← self_t S]; rw [← pair_cov, quantCut, cut_apply,if_pos (mem_powerset.mpr subset_union_left)] -- maybe nth
lemma bootC {I:Type*}[Fintype I][LinearOrder I](A:FC I): ‖exp A‖ ≤ Real.exp ‖A‖:=by
 rw [congrFun (exp_eq_tsum ℝ), Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]; -- tune use ℂ
 refine (norm_tsum_le_tsum_norm ?_).trans ( (?_ : _))
 · exact norm_expSeries_summable' (𝕂:=ℝ) A -- tune
 exact Summable.tsum_mono (norm_expSeries_summable' (𝕂:=ℝ) A) (by apply Summable.of_norm; exact norm_expSeries_summable' (𝕂:=ℝ) ‖A‖) (fun n=> by rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity))
lemma plump_cost (S:Finset I){C:Op I}(h:‖C‖≤1) : ‖plump S C‖≤ Real.exp ((S.card:ℝ)^2):=by
 have he:‖coupl (square S C)‖≤(S.card:ℝ)^2:=by
   let f(i j:I):=C i j • (put i*put j); have hp i j:‖f i j‖≤1:=by unfold f; rw [norm_smul]; exact mul_le_one₀ ((norm_entry ..).trans h) (norm_nonneg _) ((norm_mul_le ..).trans (mul_le_one₀ (payPut i) (norm_nonneg _) (payPut j))) -- tune
   rw [coupl_tick,norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv]; norm_num)); apply le_trans (norm_sum_le ..); apply le_trans (sum_le_sum (g:=fun _=>∑ j∈S,(1:ℝ)) (fun i _=>(norm_sum_le ..).trans (sum_le_sum fun j _=>hp i j))); simp only [sum_const,nsmul_eq_mul,mul_one,pow_two]; rfl
 unfold plump; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (stampCost (cabin_proj ..))).trans; exact (bootC _).trans (Real.exp_le_exp.mpr he)
lemma berth_un (S T:Finset I): berth (S∪T)=berth S*berth T:=by simpa using cabin_merge (I:=I) ∅ S ∅ T
lemma splitplump {S T:Finset I}{C:Op I}(h:Disjoint S T)(g:square (S∪T) C=square S C+square T C): plump (S∪T) C=plump S C * plump T C:=by
 have he: Commute (coupl (square S C)) (coupl (square T C)):=council (coupl_here ..) (coupl_here ..) h
 letI : NormedAlgebra ℚ (FC I):=NormedAlgebra.restrictScalars ℚ ℂ (FC I)
 unfold plump; rw [g, show coupl (square S C+square T C)=coupl (square S C)+coupl (square T C) from ?_, exp_add_of_commute he, berth_un,mul_assoc,mul_assoc]; congr 1; rw [←mul_assoc,←mul_assoc, (council (tuft T C) berth_stays h.symm).eq]; simp only [coupl,squareP,Matrix.add_apply,add_smul,sum_add_distrib,smul_add]
lemma plump_empty(C:Op I): plump ∅ C=1:=by
 have ht:cabin (∅:Finset I) ∅=1:=cabin_nil; simp only [plump,berth,coupl_tick,sum_empty,smul_zero,exp_zero,one_mul,ht]
lemma plump_goal(C:Op I): acts (plump univ C) (vacuum I)=pairWave C:=by rw [plump_vac, show square univ C=C from (Matrix.ext fun i j=> by rw [square_entry, if_pos ⟨mem_univ _,mem_univ _⟩])]
end YM.CF.BProof.Garden
