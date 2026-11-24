import YM.CF.Siete.Lights
import YM.CF.Matter.Mass
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Scree
variable {κ:Type*}[LinearOrder κ][Fintype κ]
def portB (F:FC κ)(i j:κ):ℂ:=inner ℂ (acts (put i*put j) (vacuum κ)) (acts F (vacuum κ))
lemma port_eq(F:FC κ)(i j:κ):portB F i j= if i=j then 0 else parity i {j}*crumb F {i,j}:=by
 by_cases h:i=j
 · rw [h,portB,put_sq]; simp
 rw [if_neg h,portB, act_mul, vacuum,put_act]; simp only [notMem_empty, ↓reduceIte, parity, filter_empty,card_empty, pow_zero,one_smul, put_act]; change inner ℂ (if _ then 0 else parity i {j} • (basisKet {i,j})) _= parity i {j}*_
 rw [if_neg (by simpa using h),inner_smul_left,basis_inner, basis_act]; simp [parity,crumb]
private lemma wing (A B: FC κ)(b:Bool)(U:UNI κ): inner ℂ (acts A (vacuum κ)) (acts (sings b (quantU U) B) (vacuum κ)) = inner ℂ (acts (twist (quantU (star U)) A) (vacuum κ)) (dove b (acts B (vacuum κ))):=by
 rw [singT,twist_formula,twist_formula,quantU_star]; change inner ℂ _ (acts (_ * _ * star (quant U.val)) _) =inner ℂ (acts (star _ * A * star (star (quant U.val))) _) _; rw [act_mul,act_mul,act_mul,act_mul, remove_vac_pair,star_star,quant_vac,act_inner,dove_acts,dove_base]; -- tune
lemma iRev(b:Bool)(F:FC κ)(i j:κ): inner ℂ (acts (put i*put j) (vacuum κ)) (dove b (acts F (vacuum κ)))= cSignX b (portB F i j):=by
 unfold portB; rw [←dove_dot,dove_acts b (put i *put j),win_m,win_up,win_up,dove_base] -- tune implicit
lemma score(b:Bool)(F:FC κ)(U:UNI κ)(i j:κ): portB (sings b (quantU U) F) i j= ∑ k:κ, ∑ l:κ,U.val i k *(U.val j l * cSignX b (portB F k l)):=by
 unfold portB; rw [wing, map_mul,twist_p,twist_p]; unfold prong; simp_rw [sum_mul,mul_sum,act_sum,sum_inner,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,act_smul,inner_smul_left]
 refine sum_congr rfl fun x _=> sum_congr rfl fun y _=> ?_
 rw [iRev]; simp [portB]; ring
lemma drawn(b r:Bool)(x:ribbon κ)(U:UNI κ)(i j:LeanV κ): portB (paintR b r U x).val i j=∑ k:LeanV κ, ∑ l:LeanV κ,(spice U r).val i k * ((spice U r).val j l * cSignX (b.xor r) (portB x.val k l)):=score .. -- tune
end YM.CF.Prism
