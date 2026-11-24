import YM.CF.BProof.Double.Peso
import YM.CF.BProof.Wick.Quest
/-! Price any dg/dyad insertion under this Wick quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter Fock Finset Branch Stint Align Double
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I] {A P Q C:Op I}
lemma issue_inner (x y:Book I): issue A P Q C x y=inner ℂ (pend x) (acts (cern A P Q C) y):=by
 unfold issue tau cern; rw [pend_move]; rw [act_mul,show (oblique A P Q C)ᵀ=star (cc (oblique A P Q C)) from by rw [←cc_star,cc,star_star],←act_inner (star (cc (oblique A P Q C))),star_star]
lemma pend_base {J:Type*}[DecidableEq J](i:J): pend (basisKet i)=basisKet i:=by apply PiLp.ext; intro j; by_cases h:j=i <;>simp [pend,h] -- tune
lemma issue_std (i j:Double.Tree I): issue A P Q C (basisKet i) (basisKet j)=cern A P Q C i j:=by rw [issue_inner, pend_base,basis_inner,basis_act]
def costQ (A P Q C B:Op I)(u v:Bool):= B*(letter u v (cern A P Q C))ᵀ
lemma columnTrace {T S: Wave I}(h:Scores (fun i j:Double.Tree I=> cern A P Q C i j) (claim basisKet T S)) (B: Op I)(u v:Bool):
    let F:=fun x:I=>cell (Double.bind u x); let G:=fun x:I=>cell (Double.bind v x); normal T S (dyad B F G)=(costQ A P Q C B u v).trace:=by
 intro F G; have ht(i j:I):normal T S (F i * G j)=letter u v (cern A P Q C) i j:=by
    have he:= h.two (Double.bind u i) (Double.bind v j); simp only [claim,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,printedT] at he; exact he
 unfold dyad costQ; simp_rw [map_sum,map_smul,ht]; rfl
variable {c:ℝ}{T:Wave I}
lemma fullGauge (p:Shelf A C c)(h:Task A T): Scores (fun i j:Double.Tree I=> cern A 0 0 C i j) (claim basisKet T (pairWave C)):=by simpa only [issue_std] using ordinaryGauge h p (basisKet (n:=Double.Tree I))
lemma dgTest (p:Shelf A C c)(h:Task A T)(B:Op I): normal T (pairWave C) (dg B)= (costQ A 0 0 C B true false).trace := columnTrace (fullGauge p h) B true false
lemma pairTest (p:Shelf A C c)(h:Task A T)(B:Op I): normal T (pairWave C) (star (coupl B))=((1/2:ℂ) • costQ A 0 0 C (star B) false false).trace :=by
 have he: star (coupl B) = (1/2:ℂ) • dyad (star B) takeF takeF:= by unfold coupl; rw [star_smul,show star (2:ℂ)⁻¹=1/2 from (by norm_num), show star (squareP B)= _ from ?_]; unfold squareP dyad; rw [sum_comm]; simp only [star_sum,star_smul,star_mul]; rfl -- tune
 rw [he,map_smul, Matrix.trace_smul]; congr 1; exact columnTrace (fullGauge p h) (star B) false false
end YM.CF.BProof.Wick
