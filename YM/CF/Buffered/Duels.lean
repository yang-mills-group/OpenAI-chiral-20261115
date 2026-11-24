import YM.CF.Buffered.Incorporated
/-!
# Quantized inter-block hops
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Cin
open Function Fock NormedSpace SU Lat Lattice Cube Finset Mir Branch Reflect
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {I J R:Type*} [LinearOrder I][LinearOrder J][LinearOrder R][Fintype I][Fintype J][Fintype R]
variable (f g:I↪J)
section sector
lemma widen {S T:Finset I}{A:FC I}{b:Bool}(h:S ⊆ T)(p:Sector S b A):Sector T b A:=by
 induction p with
 | zero=> apply Sector.zero
 | one=> apply Sector.one
 | add _ _ p q=> exact p.add q
 | mul _ _ p q=> exact p.mul q
 | scale _ c p=> exact p.scale _
 | up _ e=> apply Sector.up; exact h e
 | down _ e=> apply Sector.down; exact h e
lemma uncut : cutM (univ:Finset I) = 1:=by ext x y; by_cases p:x=y <;> simp [cutM,p,Matrix.one_apply]
lemma untheta {S:Finset I}{A:FC I}(U:UNI I){b:Bool}(p:Sector S b A):Sector univ b (theta U A):= theta_carries U (widen (subset_univ _) p) (by rw [uncut,map_one]) -- tune
lemma uninstall {S:Finset I}{A:FC I}{b:Bool}(p:Sector S b A):Sector univ b (into f A):= widen (subset_univ _) (sector_in f p)
lemma undg (A:Op I) : Sector univ false (dg A):= pair_charge (by rw [uncut,one_mul,mul_one])
lemma unseed (s:Finset I)(A:Op I): Sector univ false (seedR s A):=by nth_rw 1 [←show cutM univ*A*cutM univ=A from by rw [uncut,one_mul,mul_one]]; exact RP.letter ..
lemma uncreate (v:Ket I): Sector univ true (create v):= Sector.makeP _ (by rw [uncut,act_one])
lemma unremove (v:Ket I): Sector univ true (remove v):=(uncreate v).contr
lemma evenc {S T:Finset J}{A B:FC J}(h:Sector S false A)(p:Sector T false B)(v:Disjoint S T) : Commute A B := by simpa only [Commute,SemiconjBy, Sector.grainB,one_smul,Bool.and_false,Bool.false_eq_true,ite_false] using Sector.apart h p v
lemma interchange (x y:Ket I) (h: Disjoint (lows f) (lows g)): into f (remove x) * into g (create y) = -(into g (create y) * into f (remove x)):=by
 simpa only [Sector.grainB,neg_smul,one_smul,Bool.and_true,ite_true] using Sector.apart (sector_in f (unremove x)) (sector_in g (uncreate y)) h
end sector

def slip (A:Op I): FC J := ∑ i,∑ j, A i j • (put (f i)*takeF (g j))
lemma slip_one (A:Op I) : slip f f A=into f (dg A):=by unfold slip dg dyad; simp_rw [map_sum,map_smul,map_mul,put_in,take_in]
lemma slip_into {A:Op I}(e:J↪R){f' g':I↪R}(h:∀ i,e (f i)=f' i)(p:∀ i,e (g i)=g' i): into e (slip f g A)= slip f' g' A:=by simp_rw [slip,map_sum,map_smul,map_mul,put_in,take_in,h,p]
lemma slip_scale (A:Op I)(z:ℂ): slip f g (z • A)= z • slip f g A:= by simp_rw [slip,Matrix.smul_apply,smul_sum,smul_assoc]
lemma slip_real (A:Op I)(z:ℝ): slip f g (z • A)= z • slip f g A:= by simp_rw [slip,Matrix.smul_apply,smul_sum,smul_assoc]
lemma slip_sector (A:Op I): Sector univ false (slip f g A):=by unfold slip; exact Sector.sumS _ _ (fun i _=> Sector.sumS _ _ (fun j _=> ((Sector.up (f i) (mem_univ _)).mul (Sector.down (g j) (mem_univ _))).scale _))
lemma slip_cont : Continuous (slip f g):= continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> (continuous_id.matrix_elem i j).smul continuous_const
lemma slip_star (A:Op I): star (slip f g A)=slip g f (star A):= by unfold slip; rw [sum_comm]; simp only [star_sum,star_smul,star_mul,takeF,star_star]; rfl
lemma slip_factor (A B:Op I): slip f g (A*star B)=∑ i, into f (create (acts A (basisKet i))) * into g (remove (acts B (basisKet i))):=by
 unfold slip; simp_rw [Matrix.mul_apply, sum_smul]; -- tune
 rw [show (∑ x:I, into f (create (acts A (basisKet x))) * into g (remove (acts B (basisKet x))))=∑ x:I, ∑ i:I, ∑ j:I,(A i x * star (B j x)) • (put (f i) * takeF (g j)) from ?_]
 · let D(i j x:I):=(A i x*star (B j x)) • (put (f i)*takeF (g j))
   change ∑ i,∑ j,∑ x,D i j x=∑ x,∑ i,∑ j,D i j x; simp_rw [sum_comm (f:=fun i j=>D _ i j),sum_comm (f:=fun i j=>∑ x,D i x j)] -- tune
 apply sum_congr rfl; intro x _; rw [create_def,remove_def]; simp_rw [map_sum,map_smul,basis_act, sum_mul,mul_sum,put_in,take_in,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,smul_smul]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; rw [mul_comm]
lemma slip_theta {f' g':I↪J}{U:UNI J}{V:UNI I}(h:Framed f f' U V)(p:Framed g g' U V)(t:Disjoint (lows f') (lows g'))(A:Op I): theta U (slip f g A)= -slip g' f' (twist V (star A)):=by
 let B:Op I:=1
 have he : A=A*star B:=by simp [B]
 have hu : twist V (star A)=V.val*B * star (V.val*A) := by rw [twist_formula,star_mul,mul_one,mul_assoc]
 rw [hu,slip_factor]; nth_rw 1 [he]; rw [slip_factor,theta_sum,←sum_neg_distrib]
 refine sum_congr rfl fun i _=>?_ ; rw [theta_mul,h.theta f (uncreate _), p.theta g (unremove _),theta_upV,theta_downV,act_mul,act_mul,map_smul,map_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]; exact interchange f' g' _ _ t
section whole
open Installed (point)
variable {P:Type*}[Fintype P][DecidableEq P] (F:Installed P I J)
-- onsite/point->hop kernels. use representation including antiperiodic signs at wrap
lemma installed_pair (W W':J→FC J)(v:P→ Op I)(a:Op J)(T:P→P)(h:∀ i j x y, a (point F i x) (point F j y)=if T i=j then v i x y else 0): dyad a W W'=∑ i:P,∑ x:I, ∑ y:I, v i x y • (W (point F i x) * W' (point F (T i) y)):=by
 let D(z w:J):= a z w • (W z*W' w); change (∑ i,∑ j,D i j)=_
 have he (f:J→FC J): ∑ i:J, f i=∑ j:P,∑ k:I, f (point F j k):= by rw [←Equiv.sum_comp F f,Fintype.sum_prod_type]; rfl
 rw [he]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro x _; rw [he]; rw [sum_eq_single (T i)]
 · dsimp [D]; simp only [h, if_true]
 · intro k _ hk; unfold D; simp_rw [h,if_neg (Ne.symm hk),zero_smul,sum_const_zero]
 simp
lemma installed_dg (T:P→P)(v:P→ Op I)(a:Op J)(h:∀ i j x y,a (point F i x) (point F j y)= if T i=j then v i x y else 0): dg a=∑ i:P,slip (point F i) (point F (T i)) (v i):= installed_pair F put takeF v a T h
lemma installed_self (v:P→ Op I)(a:Op J)(h:∀ i j x y,a (point F i x) (point F j y)= if i=j then v i x y else 0): dg a=∑ i:P,into (point F i) (dg (v i)):=by simp_rw [←slip_one]; exact installed_dg F id v a h -- tune
lemma installed_seed (v:P→ Op I)(a:Op J)(h:∀ i j x y,a (point F i x) (point F j y)= if i=j then v i x y else 0)(s:Finset I)(t:Finset J)(k:∀ i (x:I),point F i x∈t↔ x∈s) : seedR t a=∑ i:P,into (point F i) (seedR s (v i)):=by
 have ht (s:Finset I)(t:Finset J)(A:Op J)(v:P→Op I)(w:∀ i (x:I),point F i x∈t↔ x∈s)(h:∀ i j x y,A (point F i x) (point F j y)=if i=j then v i x y else 0)(W:J→FC J)(Q:I→FC I)(q:∀ (i:P) x, W (point F i x)=into (point F i) (Q x)): dyad (cutM t*A*cutM t) W W= ∑ i:P,into (point F i) (dyad (cutM s*v i*cutM s) Q Q):=by
    rw [installed_pair F W W (fun i=>cutM s*v i*cutM s) _ (fun i=>i)]; swap
    · intro i j x y; unfold cutM; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,w,h]; split_ifs <;> simp
    refine sum_congr rfl fun i _=> ?_; simp_rw [dyad,q,map_sum,map_smul,map_mul]
 unfold seedR; rw [ht s t (star a) (fun i=>star (v i)) k ?_ _ takeF (fun _ _=>(take_in ..).symm), ht sᶜ tᶜ a v (fun i x=>by rw [mem_compl,mem_compl,k]) h _ put (fun _ _=>(put_in ..).symm)] -- tune
 · simp only [←map_add,←sum_add_distrib,map_smul,smul_sum]
 intro i j x y; change star (a (point F j y) (point F i x))=_; rw [h]; by_cases e:i=j
 · subst j; rw [if_pos rfl,if_pos rfl]; rfl
 rw [if_neg e,if_neg (Ne.symm e),star_zero]
end whole
end YM.CF.Buffered.Cin
#print axioms YM.CF.Buffered.Cin.slip_theta
#print axioms YM.CF.Buffered.Cin.installed_seed
