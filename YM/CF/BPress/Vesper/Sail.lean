import YM.CF.BPress.Vesper.Wheel
/-! Flag-Fourier density and optional circles. Independently integrated fields at the same torus length. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Vesper
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Push.AbsoluteSums Gas Palmer Fock Pastry Pine Pf Leaves EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Cube Lat SU Spin Spin.Paint Chalk Lily Skye Scree Branch Tenant DoughBag Tulip Dial Wheel --
variable {N:Side} (R:GramM N)(V:Orbit N)
abbrev Rod(N:Side):=Wheel (Site (More N))
abbrev ActY(N:Side):=Wheel (Site N)
def ringF (x:Rod N)(V:Force N):ℂ:= Wheel.ζ (forcePart V) x
abbrev flagsF (x:Finset (Force N)):= x.biUnion forcePart
abbrev trueFlags:= RG.flags R.p.threshold V.1
lemma separated_iff(A:Finset (Force N)): separated OreS A ↔ Set.PairwiseDisjoint (A:Set (Force N)) harbor:= by unfold separated; simp only [Set.PairwiseDisjoint,Set.Pairwise, Function.onFun,OreS, not_not,mem_coe]
lemma flags_disj(A:Finset (Force N))(p:separated OreS A): Set.PairwiseDisjoint (A:Set (Force N)) forcePart:=fun x b y c e=> Disjoint.mono x.property.2 y.property.2 ((separated_iff A).mp p b c e)
lemma paste (Z:Rod N)(t:Finset (Force N))(v:separated OreS t): (∏ i∈ t,ringF Z i)=(Wheel.ζ (flagsF t) Z):= (prod_biUnion (flags_disj t v)).symm -- tune argument
lemma tin_circ (Z:Rod N)(p:Finset (Force N)): tin OreS (fB R V (ringF Z)) p= weft (Wheel.ζ (flagsF p) Z) (tin OreS (f_budget R V) p):=by
 unfold tin; split; next h=> rw [←paste Z p h]; unfold fB weft; rw [hollow_prod, prod_mul_distrib]
 next h=>rw [weft,mul_zero]
abbrev stairF(p:Finset (Force N)):= exp (office R V.1) * tin OreS (f_budget R V) p
theorem boards : R.board V= ∑ i:Finset (Force N),if flagsF i=trueFlags R V then stairF R V i else 0:=by
 rw [GramM.board, show fueled R.p R.K V=∑ i:Finset (Force N),if flagsF i=trueFlags R V then tin OreS (f_budget R V) i else 0 from ?_,mul_sum]; apply sum_congr rfl; intro i _; by_cases v:flagsF i=trueFlags R V <;> simp only [v, ite_false,mul_zero,ite_true]; rfl -- tune
 unfold fueled; apply sum_congr rfl; intro i _; unfold tin; rw [separated_iff]; by_cases h:flagsF i=trueFlags R V; · rw [if_pos h]; have ht:coverF R.p i V.1:=h; change (if coverF R.p i V.1 ∧ Set.PairwiseDisjoint (i:Set (Force N)) harbor then _ else _) = (if Set.PairwiseDisjoint (i:Set (Force N)) harbor then _ else _); split <;> rename_i e <;> first| (rw [if_pos e.2]) | rw [if_neg (fun t=>e ⟨ht,t⟩)]
 rw [if_neg h, if_neg (fun v=> h v.1)]
theorem phase_full (x:Rod N): pantry R V 1 (ringF x)=∑ p:Finset (Force N),weft (Wheel.ζ (flagsF p) x) (stairF R V p):=by
 unfold pantry box; simp_rw [wee_void, mul_sum,tin_circ,stairF,weft,mul_left_comm (exp (office R V.1))]
variable (A:Op (Single N))(a b: Wave (Single N))(t:IsStarProjection A)
abbrev spinInner (a b:Wave (Single N)) (Q: FC (Single N)):= inner ℂ a (acts Q b)
include t
lemma ring_full (x:Rod N): spinInner a b (strength R V 1 (ringF x) A)=∑ p:Finset (Force N), Wheel.ζ (flagsF p) x*spinInner a b (tank A (stairF R V p)):=by
 simp_rw [strength,phase_full, tank_eq (h:=t),map_sum, cTask,spinInner,act_sum,act_smul,inner_sum,inner_smul_right] -- tune
lemma discharge : ∫ x:Rod N,(Wheel.ζ (trueFlags R V) x)⁻¹ * spinInner a b (strength R V 1 (ringF x) A) ∂coin (Site (More N))=spinInner a b (tank A (R.board V)):= by
 simp_rw [ring_full R V A a b t]; rw [order_f, boards]; rw [tank_eq (h:=t), map_sum, spinInner, act_sum, inner_sum]; apply sum_congr rfl; intro i _; split; next h=> rfl
 next h=> rw [map_zero, act_zero,inner_zero_right]
end YM.CF.BPress.Vesper
