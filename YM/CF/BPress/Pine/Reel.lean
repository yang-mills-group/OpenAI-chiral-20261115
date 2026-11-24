import YM.CF.BPress.Pine.Tune
/-! VolumeB-poly Pf rule. Auxiliary exterior (OVER LETTERS, not CAR of physics) only to price the two-type ordered Wick values. Laplace formula proved here; sign factoring of decorated Wick terms will be through THIS pure exterior and sectors. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable (l:List I){x:I}
local notation "Ω_" => vacuum I
lemma takes_ex (i:I)(p:i ∉ l): acts (takeF i) (acts (raw l) Ω_)=0:=by induction l with|nil=> rw [show raw ([]:List I)=1 from rfl, act_one, ←remove_take, vacuum_take]|cons a l ih=>
     obtain ⟨e,p⟩:= not_or.mp (show ¬(i=a ∨ i∈l) from mt List.mem_cons.mpr p); rw [←act_mul,show raw (a::l)=put a*raw l from rfl,←mul_assoc,eq_neg_of_add_eq_zero_left ((mixed ..).trans (if_neg e)), neg_mul,mul_assoc,act_neg,act_mul,act_mul,ih p,map_zero,neg_zero] -- tune
lemma cost_put (i:I): ‖Fock.put i‖≤1:=by
 rw [show put i=poke {i} from (Poly.tag_once (cane I) i).symm]; exact tag_size _
lemma cost_raw : ‖raw l‖ ≤1:=by induction l with|nil=>simp [raw]|cons i l ih=> exact (norm_mul_le (put i) _).trans ((mul_le_mul (cost_put i) ih (norm_nonneg _) zero_le_one).trans_eq (mul_one _))
-- even number of letters buys entire tape, any permutation (the Dough subalgebra)
lemma lifted (v: Even l.length): Flour univ (raw l) ∧ Sector (l.toFinset) false (raw l):=by
 generalize z:l.length=n at *; induction n using Nat.strong_induction_on generalizing l with|h n ih=>
    rcases l with (_|⟨a,l⟩); exact ⟨Flour.grainE,Sector.one⟩ ; rcases l with (_|⟨b,l⟩); simp at z; subst n; simp at v
    rw [List.length_cons,List.length_cons] at z; have hp:Even l.length:=by rw [Nat.even_iff] at v ⊢; omega
    obtain ⟨u,t⟩:= ih _ (by omega : l.length < n) l rfl hp -- tune ih order
    rw [show raw (a::b::l)= put a* put b* raw l from (mul_assoc ..).symm]; exact ⟨Flour.mul (Flour.putPut univ (mem_univ _) (mem_univ _)) u, ((Sector.up a (by simp)).mul (Sector.up b (by simp))).mul (Chalk.zoom t (fun i g=> by simpa [List.mem_toFinset.mp g]))⟩ -- tune
lemma existent (p:x∈l) : put x * raw l=0:=by induction l with |nil=> simp at p| cons a l ih=> rcases List.mem_cons.mp p with v|v; subst a; rw [show raw (_::_)=put x*raw l from rfl, ←mul_assoc, put_sq,zero_mul]; rw [show raw (_::_)=put a*raw l from rfl, ←mul_assoc,eq_neg_of_add_eq_zero_left (put_put x a),neg_mul,mul_assoc,ih v]; simp
lemma tape_zero (h:¬ l.Nodup):raw l=0:=by
 induction l with|nil=> simp at h| cons a l ih=>by_cases p:a∈l; exact existent l p; rw [show raw (a::l)= put a*raw l from rfl, ih (fun v=> h (List.nodup_cons.mpr ⟨p,v⟩)),mul_zero]
-- calcul density: Dough ➞ FC.P. expose additive & multiplicative as needed; map_prod uses Subalgebra.AlgHom but target not Comm!
lemma listS {n:Type}[Fintype n][LinearOrder n] (l:List (↥(Dough n))): Subtype.val l.prod=(l.map (fun (i:Dough n)=> (i:FC n))).prod:=by induction l with|nil=> rfl|cons i l ih=> rw [List.map_cons,List.prod_cons,List.prod_cons, Subalgebra.coe_mul]; congr 1
lemma sumS {n J:Type}[Fintype n][LinearOrder n](X:Finset J)(f:J→Dough n):Subalgebra.val (Dough n) (∑ i∈X,f i)=∑ i∈X,(f i).val:=map_sum ..
lemma tideExp {E:Type*}[NormedRing E][NormedAlgebra ℂ E] (A:E)(h:A*A=0): exp A=1+A:=by
 rw [exp_eq_tsum ℂ]; dsimp only; rw [tsum_eq_sum (s:=({0,1}:Finset ℕ)) ?_]; · rw [sum_insert (by simp)]; simp
 intro n v; have ht:n≥2:=by simp only [mem_insert,mem_singleton] at v; omega
 obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le ht; rw [pow_add,pow_two,h,zero_mul,smul_zero]
end YM.CF.BPress.Pine
