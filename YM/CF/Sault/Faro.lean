import YM.CF.Scree.Cook
import YM.CF.Sedge.Craft
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- π_map vacuum.Span.Key.L
lemma col (A:FC n)(j:Finset n): crumb A j=(acts A (vacuum n)).ofLp j:=(basis_act ..).symm
def ballL(v:Poly n m)(c:Wave m) : Wave n →ₗ[ℂ] Wave m where
 toFun x := ∑ i:Finset n,x.ofLp i • acts (v.tag i) c
 map_add' x y:=by simp [add_smul,sum_add_distrib]
 map_smul' x y:=by simp [smul_sum,smul_smul]
lemma loaf (v:Poly n m)(c:Wave m)(F:FC n): ballL v c (acts F (vacuum n))=acts (v.eval F) c:=by unfold Poly.eval; change ∑ i:Finset n,_=acts (∑ i:Finset n,crumb F i • v.tag i) _; rw [act_sum]; exact sum_congr rfl fun _ _=>by rw [act_smul,col]
lemma passL (i:n)(v:Poly n m)(c:Wave m)(x:Wave n): ballL v c (acts (put i) x)= acts (v.term i) (ballL v c x):=by
 rw [←basis_expand x,map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul,map_smul,map_smul]; congr 1
 rw [←poked j,←act_mul,loaf,loaf,show put i=poke {i} from (Poly.tag_once (Pastry.cane n) i).symm,v.eval_prod,v.eval_oneT,v.tag_once,act_mul]
lemma harp (v:Poly n m)(c:Wave m)(A:FC n)(B:FC m)(h:∀ i:n,∃ x:ℂ,antiB A (put i)=x • 1∧antiB B (v.term i)=x • 1)(p:ballL v c (acts A (vacuum n))=acts B c)(y:Wave n): ballL v c (acts A y)=acts B (ballL v c y):=by
 let L:=ballL v c; have he:L (vacuum n)=c:=by rw [←act_one (vacuum n)]; unfold L; rw [loaf,Poly.eval_one,act_one]
 have hv (j:Finset n): L (acts A (basisKet j))=acts B (L (basisKet j)):=by
    induction j using Finset.induction_on with
    |empty=>change L _=acts B (L (vacuum n)); rw [he]; exact p
    |insert i j g ih=>
       obtain ⟨x,q,u⟩:=h i; rw [create_basis_is _ _ g,map_smul,map_smul,map_smul,map_smul, ←act_mul, show A*put i=x • 1-put i*A from eq_sub_of_add_eq q,show L (acts (put i) _)=_ from passL .., act_sub,act_smul,act_mul,map_sub,map_smul,act_one,show L (acts (put i) _)=_ from passL ..,ih, ←act_mul B, show B*v.term i=x • 1-v.term i*B from eq_sub_of_add_eq u,act_sub,act_smul,act_one,act_mul]
 rw [←basis_expand y,map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; intro j hj; rw [map_smul,map_smul,map_smul,map_smul, ←hv]
-- Express CAR
abbrev trailM(t:Bool)(i:n):FC (LeanV n):=takeF (n:=LeanV n) (t,i)
def palm (P:Op n)(i:n):FC (LeanV n):= wire true i+∑ j:n,(cc P i j) • trailM false j
def hilt (P:Op n)(i:n):FC (LeanV n):= wire false i+∑ j:n,((1-P) i j) • trailM true j
lemma plus_α(A B C:FC n):antiB (A+B) C=antiB A C+antiB B C:=by unfold antiB; rw [add_mul,mul_add]; abel
lemma chord (i:n)(P:Op n)(p:IsStarProjection P)(j:LeanV n):∃ x:ℂ,antiB (palm P i) (put j)=x • 1∧antiB (put i) ((nursery P p).term j)=x • 1:=by
 rcases j with ⟨b,j⟩; rw [palm,plus_α,wire,show antiB (put _) (put _) = _ from put_put ..,zero_add,antiB_sum]; simp_rw [antiB_smul]; cases b
 · refine ⟨cc P i j,?_,?_⟩; · simp_rw [trailM,antiB,mixed]; simp [apply_ite _ _]
   change antiB (put i) (prong takeF (cc P) _)= _; rw [antiB_comm (prong takeF (cc P) (Prod.snd (false,j))) (put i),prong,antiB_sum]; simp_rw [antiB_smul,antiB,mixed]; simp [apply_ite _ _]
 refine ⟨0,?_,?_⟩; · simp [trailM,antiB,mixed]
 change antiB (put i) (prong put (1-P) _)=_; rw [prong,antiB_sum']; simp_rw [antiB_smul',antiB,put_put]; simp
lemma chord' (i:n)(P: Op n)(p:IsStarProjection P)(j:LeanV n):∃ x:ℂ,antiB (hilt P i) (put j)=x • 1∧antiB (takeF i) ((nursery P p).term j)=x • 1:=by
 rcases j with ⟨b,j⟩; rw [hilt,plus_α,wire,show antiB (put _) (put _) = _ from put_put ..,zero_add,antiB_sum]; simp_rw [antiB_smul]; cases b
 · refine ⟨0,?_,?_⟩; · simp [trailM,antiB,mixed]
   change antiB (takeF i) (prong takeF (cc P) _)=_; rw [prong,antiB_sum']; simp_rw [antiB_smul',antiB,take_take]; simp
 refine ⟨(1-P) i j,?_,?_⟩; · simp_rw [trailM,antiB,mixed]; simp [apply_ite _ _]
 change antiB (takeF i) (prong put (1-P) _)= _; rw [prong,antiB_sum']; simp_rw [antiB_smul',antiB,mixed]; simp [apply_ite _ _]
lemma rock (i:n)(x:ℂ):acts (x • takeF i) (vacuum n)=0:=by rw [act_smul,← remove_take,vacuum_take,smul_zero]
lemma runL (v:Poly n m)(c:Wave m):ballL v c (vacuum n)=c:=by rw [←act_one (vacuum n), loaf,Poly.eval_one,act_one]
variable {P:Op n}(p:IsStarProjection P)(x:Wave n)(h:Sea P x)
local notation "ℓ"=> (ballL (nursery P p) x)
include h
lemma polar(i:n)(y:Wave (LeanV n)) : ℓ (acts (palm P i) y)= acts (put i) (ℓ y):=by
 apply harp _ _ _ _ (chord i _ p); rw [palm,act_add,act_sum, sum_eq_zero (fun j hj=> rock (n:=LeanV n) (false,j) _),add_zero,wire,passL,runL]; change acts (prong put (1-P) i) x=_
 rw [prong_p,act_sub,act_one,map_sub,act_sub,tarp (v:=(acts P) (basisKet i)) p h.1 (by rw [←act_mul,p.isIdempotentElem.eq]),sub_zero,create_put] -- includes h syntax. 
lemma bore (i:n)(y:Wave (LeanV n)):ℓ (acts (hilt P i) y)=acts (takeF i) (ℓ y):=by
 apply harp _ _ _ _ (chord' i _ p); rw [hilt,act_add,act_sum, sum_eq_zero (fun j hj=> rock (n:=LeanV n) (true,j) _),add_zero,wire,passL,runL]; change acts (prong takeF (cc P) i) x=_
 let W:=1-P; let z:=basisKet i; have he:(acts W) z=z-acts P z:=by rw [show W=1-P from rfl,act_sub,act_one]
 have hf:=tars p h.1 (show (acts P) ((acts W) z)=0 from (by rw [he,map_sub,←act_mul,p.isIdempotentElem.eq,sub_self]))
 rw [prong_t]; unfold remove at hf; rw [he,map_sub,star_sub,act_sub] at hf; exact (sub_eq_zero.mp hf).symm.trans (by unfold z; rw [create_put])
end YM.CF.Sault
