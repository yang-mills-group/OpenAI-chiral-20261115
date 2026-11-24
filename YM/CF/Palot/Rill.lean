import YM.CF.Palot.Pent
import YM.Push.ABSOLUTE_SUMS.FiniteLog
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Ursell Push.AbsoluteSums.Graph Push.AbsoluteSums.Coef Push.AbsoluteSums.Gas
variable {ι E: Type*}[Fintype ι] [CommRing E][Algebra ℝ E]
abbrev SongQ(m:ℕ):= (Option (Fin m))
def pace(R:ι→ι→Prop)(F:ι→E)(s:Finset ι):= if Gas.separated R s then ∏ i∈s,F i else 0
def stoneC(R:ι→ι→Prop)(f:ι→ E)(n:ℕ): E:= ∑ s∈ univ.powersetCard n, pace R f s
def guava(R:ι→ι→Prop)(f:ι→ E)(z:Clusters ι) : E:= (coefficient R z.2/(z.1+1).factorial:ℝ) • ∏ i,f (z.2 i)
def tuneC (R:ι→ι→ Prop)(f:ι→E)(k:ℕ): E := ∑ z:SongQ k→ι, guava R f ⟨k,z⟩
lemma turn_R(R:ι→ι→Prop)(F:ι→ℝ)(p:Hard R)(k:ℕ): stoneC R F k=gasRow R F k:= (row R F k p).symm
lemma songL (R:ι→ι→Prop)(F:ι→ℝ)(k:ℕ): tuneC R F k=logRow R F k:=by unfold tuneC guava logRow Coef.linked; rw [sum_div]; exact sum_congr rfl fun i _=> by dsimp only; rw [smul_eq_mul]; ring
lemma vane (m:ℕ)(R:ι→ι→Prop)(p:Hard R)(u:ι→ E):(m+1:ℝ) • stoneC R u (m+1) = ∑ k∈range (m+1),(k+1:ℝ) • tuneC R u k* stoneC R u (m-k):=by
 let F(i:ι):MvPolynomial ι ℝ:= MvPolynomial.X i
 let P:=(m+1:ℝ) • stoneC R F (m+1); let Q:= ∑ k∈range (m+1), (k+1:ℝ) • tuneC R F k * stoneC R F (m-k)
 have hp : P=Q:=by
   apply MvPolynomial.funext; intro x
   have he(a:MvPolynomial ι ℝ):MvPolynomial.eval x a=MvPolynomial.aeval x a:= (congrFun (MvPolynomial.aeval_eq_eval x) a).symm
   rw [he,he]; unfold P Q; have ht(n): MvPolynomial.aeval x (stoneC R F n)= stoneC R x n:=by simp [stoneC,pace,F,apply_ite (MvPolynomial.aeval x)]
   have hh(n): MvPolynomial.aeval x (tuneC R F n)= logRow R x n:=by rw [←songL R x n]; simp [tuneC,guava,F]
   simp only [map_smul,map_sum,map_mul, ht, hh, turn_R R x p, smul_eq_mul]; exact recurrence R x m
 have he(a): MvPolynomial.aeval u (stoneC R F a)=stoneC R u a:=by simp [stoneC,pace,F, apply_ite (MvPolynomial.aeval u)]
 have hh(n): MvPolynomial.aeval u (tuneC R F n)=tuneC R u n:=by simp [tuneC,guava,F]; -- tune
 have hg:= congrArg (MvPolynomial.aeval u) hp; simpa only [P,Q,map_smul,map_sum,map_mul,he,hh] using hg
lemma streamU(n:ℕ)(R:ι→ι→ Prop)(F:ι→ E)(v:Fintype.card ι<n):stoneC R F n=0:=by unfold stoneC; rw [show Finset.powersetCard n (univ:Finset ι)=∅ from eq_empty_iff_forall_notMem.mpr (fun i p=>by rw [←(mem_powersetCard.mp p).2] at v; have he:= i.card_le_univ; omega),sum_empty]
lemma start(R:ι→ι→ Prop)(F:ι→ E): stoneC R F 0=1:=by simp [stoneC,pace,separated]
lemma vanish(R:ι→ι→Prop)(F:ι→E): ∑ i∈ range (Fintype.card ι+1),stoneC R F i= ∑ s:Finset ι,pace R F s:=by
 have hh(s:Finset ι)(g:s∈ (univ:Finset (Finset ι))):s.card∈range (Fintype.card ι+1):=mem_range.mpr (by have he:=s.card_le_univ; omega)
 rw [← sum_fiberwise_of_maps_to hh]; apply sum_congr rfl; intro i _; unfold stoneC; rw [powersetCard_eq_filter]; simp
end YM.CF.Palot
