import YM.CF.BPress.Pine.Reel
/-! VolumeB-poly Pf rule. Auxiliary exterior (OVER LETTERS, not CAR of physics) only to price the two-type ordered Wick values. Laplace formula proved here; sign factoring of decorated Wick terms will be through THIS pure exterior and sectors. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
-- support-labeled contractions. Include several copies of each pair as needed. NO arity-0 markers from pair expansion. CP: material vector.Cash priced later.
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y](F:Branch.Field Y)
structure EdgeD(I B Y:Type)[LinearOrder I][DecidableEq Y](F:Branch.Field Y) where
 anchor:I → Y
 src:B→ I
 dst:B→ I
 past(x:B): src x < dst x
 look:B→ Seal Y
 paints:∀ i,Grove F (look i) -- Fintype Y & B meta issues
 back(i:B):anchor (src i)∈look i
 front(i:B):anchor (dst i)∈look i
variable {F}
namespace EdgeD
variable (D:EdgeD I B Y F) (K:B→ℂ)
def manifest (x:B):= Matrix.single (D.src x) (D.dst x) (K x) - Matrix.single (D.dst x) (D.src x) (K x)
-- single direction
lemma manifest_lt (x:B)(i j:I)(h:i<j): manifest D K x i j= if i=D.src x ∧ j=D.dst x then K x else 0:=by
 unfold manifest; rw [Matrix.sub_apply]; have he:¬ (i=D.dst x∧j=D.src x):= fun ⟨p,q⟩=>(D.past x).not_gt (by rwa [p,q] at h)
 simp only [Matrix.single,Matrix.of_apply]; -- tune
                                                                                                                                                                                                                    --
 split_ifs <;> grind
lemma direction(x:B): (D.manifest K x)ᵀ= -(D.manifest K x):=by unfold manifest; rw [Matrix.transpose_sub,Matrix.transpose_single, Matrix.transpose_single,neg_sub] -- tune
abbrev bkg : Op I:= ∑ i,D.manifest K i
lemma sk: (D.bkg K)ᵀ= -(D.bkg K):=by unfold bkg; simp only [Matrix.transpose_sum,D.direction,Finset.sum_neg_distrib]
abbrev twigD(x:B): Dough I:=⟨ K x • (put (D.src x)*put (D.dst x)), (Flour.putPut univ (mem_univ _) (mem_univ _)).smul _⟩
abbrev holds (i:I):=univ.filter (fun x:B=> i=D.src x)
abbrev fromT (i:I): Dough I:=∑ x∈D.holds i,D.twigD K x
lemma grainP(i:I)(j:I)(s:ℂ): squareP (Matrix.single i j s)= s • (put i*put j):=by unfold squareP; rw [sum_eq_single i]; simp [Matrix.single,ite_smul,eq_comm]; intro k _ p; simp [Matrix.single,p, ite_smul,Ne.symm p]; simp
lemma grain(p:B): coupl (manifest D K p) = (D.twigD K p).val:=by
 let a:= D.src p; let b:= D.dst p; have hm(X Y: Op I): squareP (X-Y)=squareP X-squareP Y:=by unfold squareP; simp only [Matrix.sub_apply,sub_smul,sum_sub_distrib];
 unfold manifest coupl; change (2:ℂ)⁻¹ • squareP (Matrix.single a b (K p)-Matrix.single b a (K p))=_; rw [hm]
 rw [grainP,grainP, eq_neg_of_add_eq_zero_left (put_put b a),smul_neg,sub_neg_eq_add, ←two_smul ℂ (K p • (put a*put b)),smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul] -- tune rewrite at both sides hazard
lemma twig_k (p:B): ‖D.twigD K p‖≤ ‖K p‖:=by rw [natNorm,twigD]; dsimp only; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ((norm_mul_le ..).trans (mul_le_one₀ (cost_put _) (norm_nonneg _) (cost_put _)))
lemma assigned : (Subalgebra.val (Dough I)) (∑ i,D.fromT K i)=coupl (bkg D K):=by
 unfold fromT; simp_rw [sum_filter]; rw [sum_comm]; simp_rw [sum_ite_eq',mem_univ,ite_true]; rw [sumS]; change ∑ i,(D.twigD K i).val=coupl (bkg D K); unfold bkg; rw [sum_congr rfl (fun i (h:i∈(univ:Finset B))=> (D.grain K i).symm)]; unfold coupl; rw [←smul_sum]; congr 1; unfold squareP; simp_rw [Matrix.sum_apply, sum_smul]; rw [sum_comm]; apply sum_congr rfl; intro i h; rw [sum_comm] -- tune
lemma weaveD {i:I}{x y:B}(t:x∈ D.holds i)(q:y∈ D.holds i): D.twigD K x*D.twigD K y=0 := by
 let j:= D.dst x; apply Subtype.ext; unfold twigD; change (K x • _)*(K y • _)=(0: FC I); rw [←(mem_filter.mp t).2, ←(mem_filter.mp q).2, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]; apply smul_eq_zero_of_right; apply smul_eq_zero_of_right; rw [←mul_assoc (put i * _), mul_assoc (put i),eq_neg_of_add_eq_zero_left (put_put j i)]; -- hazards
 simp [←mul_assoc,put_sq] -- tune
lemma weather(i:I): (fromT D K i)*(fromT D K i)=0:=by unfold fromT; rw [sum_mul]; refine sum_eq_zero (fun j u=>?_); rw [mul_sum]; exact sum_eq_zero (fun i q=> D.weaveD K u q)
lemma wander {u v:Dough I} (h:Commute u v): Commute u.val v.val := h.map (Subalgebra.val (Dough I))
def stair (T:Finset I) : Dough I:= ∏ i∈T,(1+fromT D K i)
lemma woodS (T:Finset I) : exp (((∑ i∈T,fromT D K i): Dough I):FC I)= (stair D K T).val:=by
 letI : NormedAlgebra ℚ (FC I):=NormedAlgebra.restrictScalars ℚ ℂ _; induction T using Finset.induction_on with|empty=>simp [stair]|@insert i T h ih=> rw [sum_insert h,Subalgebra.coe_add, exp_add_of_commute (wander (Commute.all _ (_: Dough I))), ih, tideExp (fromT D K i).val (by exact congrArg Subtype.val (weather D K i)), stair,stair,prod_insert h]; rfl -- tune tideExp
lemma wood : pairWave (D.bkg K)=acts (stair D K univ).val (vacuum I):=by rw [←woodS, ←stored, ←D.assigned K]; rfl -- possibly rw solved
end EdgeD
end YM.CF.BPress.Pine
