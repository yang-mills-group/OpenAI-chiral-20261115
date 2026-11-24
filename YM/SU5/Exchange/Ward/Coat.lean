import YM.SU5.Exchange.Ward.Local
import YM.CF.Leaf.Jive
import YM.CF.Mica.Near
set_option autoImplicit false
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree Leaf Skye Dial Paige Vault
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
variable {ι:Type*}
variable (P W:Op n)
open Thera Ione
-- Actual tilt uses exponentL true.Reg +EMPTY slip. Can work if slip is scalar.
lemma rank2Rail : rank2 (derail P W):=by
 let f(o b:Bool)(S:Op n):=show rank2 (urn (wire o) (trailM b) S) from δX _ _ fun _ _=>δX _ _ fun _ _=>ψX _ _ (τX _ _ (αb _) (βb _))
 exact θX _ _ (f _ _ _) (f _ _ _)
abbrev attire (A:FC n)(F:Dough n):FC n:= A+bump A F.val+(2:ℝ)⁻¹ • bump (bump A F.val) F.val
lemma attireExp (A:FC n)(F:Dough n)(p:rank2 A): (exp F).val* attire A F=A*(exp F).val:=(Yz_h A F p).symm
lemma bumpCut (A:FC n)(F:Dough n): bump A (blind_E F).val=bump A F.val:=by
 change bump A (F.val-(wage_Q 0 F).val)=_
 have hp:(wage_Q 0 F).val= crumb F.val ∅ • 1:=by
    rw [(fineShape (wage_Q 0 F)).allP, sum_eq_single_of_mem (∅:Finset n) (mem_univ _)]; · rw [price_X,if_pos card_empty,poke, Poly.tag_void]
    intro k _ z; rw [price_X,if_neg (fun v=>z (card_eq_zero.mp v)), zero_smul]
 rw [hp]; unfold bump; rw [mul_sub,sub_mul, (Commute.one_right A|>.smul_right _).eq]; abel
lemma attireCut (A:FC n)(F:Dough n): attire A (blind_E F)=attire A F:=by unfold attire; rw [bumpCut,bumpCut]
lemma attire_add (A B:FC n)(F:Dough n): attire (A+B) F=attire A F+attire B F:=by unfold attire; rw [δb,δb,smul_add]; abel
lemma attire_sub (A B:FC n)(F:Dough n): attire (A-B) F=attire A F-attire B F:=by unfold attire; rw [hp_b,hp_b,smul_sub]; abel
lemma attire_sum {I:Type*}(S:Finset I)(A:I→ FC n)(F:Dough n): attire (∑ i∈ S,A i) F=∑ i∈ S,attire (A i) F:=by simp only [attire, σq, smul_sum, sum_add_distrib]
lemma attire_scale (A:FC n)(x:ℂ)(F:Dough n): attire (x • A) F=x • attire A F:=by unfold attire; simp only [τq,smul_add]; rw [smul_comm (2:ℝ)⁻¹]
lemma blindMask (A:Finset ι)(F:ι→ Dough n): ∑ i∈A, blind_E (F i)= blind_E (∑ i∈A,F i):=by
 apply pimp_Q; intro j; change crumb ((Dough n).val (_)) j= _; rw [map_sum]; change crumb (∑ i∈A,(blind_E _).val) _= _; rw [crumb_sum,shelter_Q]; split_ifs with v; simp_rw [shelter_Q, if_pos v]; exact sum_const_zero
 change _= crumb ((Dough n).val (_)) j; rw [map_sum,crumb_sum]; simp_rw [shelter_Q, if_neg v]; rfl
lemma maskExpHead (p:RG.BudgetPoint){N:Side}(F:RegBudget N)(V:Pane N) : blind_E (exponentL p F V)=exponentL p (head_L F) V:=by
 unfold exponentL; rw [←blindMask]; refine sum_congr rfl ?_; intro i _; unfold numbE; by_cases h:pingS p.threshold i.val.2 V
 · rw [Set.indicator_of_mem h,Set.indicator_of_mem h]; rfl
 rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h]; apply pimp_Q; intro j; rw [shelter_Q]; split <;> rfl <;> simp [crumb]
-- combine with corpus Pilot.P later
end YM.CF.Sault
