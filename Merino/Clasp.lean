import Merino.Shuttle
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered StressExchange Dial

/-- Equivalence on left-bra uses on the *same* field after whatever other
choices on the right. -/
def Yoke (D:Evaluation n)(C:phy n):Prop:=
  ∀ z:Orbit n, acts (star (D z.1)) (mateK n)=acts (star (C z)) (mateK n)
namespace Yoke
variable {D D':Evaluation n}{C C':phy n}
lemma inner_y (p:Yoke D C)(z:Orbit n)(v:Phys n):
  inner ℂ (mateK n) (acts (D z.1) v)=inner ℂ (mateK n) (acts (C z) v):=by
 rw [←act_inner,←act_inner,p z]
lemma add (p:Yoke D C)(q:Yoke D' C'):Yoke (D+D') (C+C'):=by
 intro z; rw [Pi.add_apply,Pi.add_apply,star_add,star_add,act_add,act_add,p z,q z]
lemma sub (p:Yoke D C)(q:Yoke D' C'):Yoke (D-D') (C-C'):=by
 intro z; rw [Pi.sub_apply,Pi.sub_apply,star_sub,star_sub,act_sub,act_sub,p z,q z]
lemma scale (p:Yoke D C)(fac:ℂ):Yoke (fac • D) (fac • C):=by
 intro z; rw [Pi.smul_apply,Pi.smul_apply,star_smul,star_smul,act_smul,act_smul,p z]
lemma sumWith {D:Axis→Evaluation n}{C:Axis→phy n}(p:∀ i,Yoke (D i) (C i)):
  Yoke (∑ i:Axis, D i) (∑ i:Axis,C i):=by
 intro z; rw [Finset.sum_apply,Finset.sum_apply,star_sum,star_sum,act_sum,act_sum]
 exact sum_congr rfl (fun i _=> p i _)
end Yoke


private lemma fixed_proj: IsStarProjection (tickA n):=by rw [touchP]; exact cutM_idp _
private lemma mill_sits (m:ℕ)(L:List Axis)(x:Site n):
    Commute (tickA n) (squareSum millQ m L x):=by
 induction L generalizing x with
 | nil =>
   rw [touchP, squareSum, millSt]
   -- stock diagonal
   unfold Tye.stock
   unfold Commute SemiconjBy cutM
   rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1
   ext; apply mul_comm
 | cons i L ih =>
   rw [squareSum]; unfold stripSum
   unfold Commute SemiconjBy; rw [mul_sum,sum_mul]
   exact sum_congr rfl (fun _ _=>(ih _).eq)
lemma first_null (x:Site n)(m:ℕ)(v:Orbit n):
    acts (star (barS0 n m x v)) (mateK n) = 0:=by
 unfold barS0; rw [star_sub,star_smul,star_one,act_sub,act_smul,act_one,
   sandwichV _ fixed_proj (mill_sits m _ _) _ (tickB n),sub_self]

lemma preJ_nil : preJ (tickA n) 0=0:=by unfold preJ dg dyad; simp

variable {K:Scree.Loom n}{a b d:ℝ}{p:BudgetPoint}{X:SOp n}
lemma flow_yoke (r:Skylit p d K)(ha:0≤a)(o x:Site n)
    (h:Trunk (node o) X (p.B/10) a b d):
    Yoke (flowHead K p (node x) (co_Ψ x o X)) (coverLine K p o x X):=by
 intro z
 unfold flowHead coverLine houseK
 rw [Function.comp_apply]
 by_cases v:z∈ pingMask p (offsetMask p.B x)
 · rw [Set.indicator_of_mem v,mask_eq r ha (trunk_go o x h) v z.2]
   exact (bra_eq _ fixed_proj _ (tickB _)).symm
 have g:z.1∉pass p (node x):=v
 rw [masked,Set.indicator_of_notMem g,Set.indicator_of_notMem v,preJ_nil]

lemma sheen_yoke (r:Skylit p d K)(ha:0≤a)(o:Site n)(m:ℕ)
    (h:Trunk (node o) X (p.B/10) a b d):
    Yoke (sheen K p (node o) X) (houseK p (offsetMask p.B o)
      (blazePlate K X-barS0 n m o)):=by
 intro z
 unfold houseK sheen traceCost
 by_cases v:z∈pingMask p (offsetMask p.B o)
 · rw [Set.indicator_of_mem v,mask_eq r ha h v z.2,
     Pi.sub_apply,star_sub,act_sub,first_null,sub_zero]
 have g:z.1∉pass p (node o):=v

 rw [masked,Set.indicator_of_notMem v,Set.indicator_of_notMem g,Matrix.trace_zero,
   zero_smul]

namespace Spool.Hem
theorem yoke {y:Spool n}(h:Hem y K p a b d)(fac:ℂ):
    Yoke (y.opening K p fac) (y.release K p fac):=by
 apply Yoke.scale
 apply Yoke.add (sheen_yoke h.skylight h.sign y.origin y.stepY h.sip)
 exact Yoke.sumWith (fun i=>
   (flow_yoke h.skylight h.sign _ _ (h.spurt i)).sub
   (flow_yoke h.skylight h.sign _ _ (h.spurt i)))
end Spool.Hem
end YM.CF.Merino

