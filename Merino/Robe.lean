import Merino.Rind
import YM.CF.Buffered.Mark
import YM.SU5.Interaction.Source.Reduction
import YM.SU5.Exchange.Stack.Manor
import YM.CF.Cascade.Velvet
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

structure LicenseY (S:Sa n)(F:Evaluation n):Prop where
  loc:AtSupport false S (toMark F)
  bill:Envelope F
  gauge_x(g:Seat n→E)(x:Pane n):F (gauge g x)=twist (quantU (tradew n g)) (F x)


namespace LicenseY
variable {S T:Sa n}{F G:Evaluation n}
lemma up (p:LicenseY S F)(l:S⊆T):LicenseY T F:={p with loc:=p.loc.mono l}
lemma add (p:LicenseY S F)(q:LicenseY S G):LicenseY S (F+G):=by
 refine ⟨p.loc.addM q.loc,Girt.kitE F G (·+·) (by fun_prop) p.bill q.bill,?_⟩
 intro g x; rw [Pi.add_apply,Pi.add_apply,map_add,p.gauge_x,q.gauge_x]
lemma scale (p:LicenseY S F)(z:ℂ):LicenseY S (z • F):=by
 refine ⟨p.loc.smulM z,Girt.pole_w F (z • ·) (by fun_prop) p.bill,?_⟩
 intro g x; rw [Pi.smul_apply,Pi.smul_apply,p.gauge_x,twist_scalar]
lemma sub (p:LicenseY S F)(q:LicenseY S G):LicenseY S (F-G):=by simpa [sub_eq_add_neg] using p.add (q.scale (-1))
lemma sumAll {α:Type*}(Y:Finset α)(A:α→Evaluation n)
    (p:∀ i,LicenseY S (A i)):LicenseY S (∑ i∈Y,A i):=by
 induction Y using Finset.induction_on with
 | empty => rw [sum_empty]; exact ⟨AtSupport.zeroM,Girt.rite_c _,fun _ _=> (map_zero (twist _)).symm⟩
 | insert i Y v h => rw [sum_insert v]; exact (p i).add h
end LicenseY

variable {o:Seat n} {p:BudgetPoint} {d a b:ℝ} {K:Scree.Loom n} {X:SOp n}
local notation "A"=>tickA n

private lemma preJ_gauge (W:Op I)(g:Seat n→E):
    preJ A (twist (tradew n g) W)=twist (quantU (tradew n g)) (preJ A W):=by
 unfold preJ; rw [map_add,twist_scalar,map_one,dg_cov,map_mul,map_mul,map_sub,
  map_one,Cascade.tick_g,show A*twist (tradew n g) W =
  twist (tradew n g) (A*W) from by rw [map_mul,Cascade.tick_g],trace_twist]

/-- Bra replacement after mask. Zero on a failed mask. The divergence
will use this recipe on each pose, *including* its scalar term. -/
def flowHead(K:Scree.Loom n)(p:BudgetPoint)(o:Seat n)(X:SOp n):
    Evaluation n := preJ A ∘ masked K p o X

theorem flow_licensed (r:Skylit p d K)(u:0≤a)(h:Trunk o X (p.B/10) a b d):
    LicenseY (casing p o) (flowHead K p o X):=by
 let S:=casing p o; let M:=masked K p o X; let F:=preJ A
 have co:Continuous F:=by unfold F preJ; fun_prop
 have bill:=Girt.pole_w M F co (mask_env r u h)
 refine ⟨AtSupport.fromEval _ bill (fun _ _ l=> congrArg F (mask_local r u h _ _ l)) ?_,bill,?_⟩
 · intro v; change Reed.Fine _ _ _ (preJ A (M v)); rw [touchP]; apply inSector
   have g (i:I) (t: node i.1.1 ∈ purse (p.B/10) o):i ∈ modesIn n S:=
     (mem_matterSet _ _).mpr (mem_filter.mpr ⟨mem_univ _,inside t⟩)
   ext i j
   rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]
   by_cases hp:M v i j=0
   · simp [hp]
   obtain ⟨t,y⟩:=mask_short r u h _ _ _ hp
   unfold S at g
   rw [if_pos (g i t),if_pos (g j y),one_mul,mul_one]
 intro g x
 change F _=_
 rw [mask_gauge r u h]; exact preJ_gauge ..

abbrev traceCost(K:Scree.Loom n)(p:BudgetPoint)(o:Seat n)(X:SOp n)(V:Pane n):ℂ:=
 (masked K p o X V).trace
def sheen(K:Scree.Loom n)(p:BudgetPoint)(o:Seat n)(X:SOp n): Evaluation n:=
  fun V=>traceCost K p o X V • 1

lemma sheen_gauge (r:Skylit p d K)(u:0≤a)(h:Trunk o X (p.B/10) a b d)
    (V:Pane n)(g:Seat n→E):
    traceCost K p o X (gauge g V)=traceCost K p o X V:=by
 unfold traceCost; rw [mask_gauge r u h,trace_twist]

lemma sheen_licensed (r:Skylit p d K)(u:0≤a)(h:Trunk o X (p.B/10) a b d):
    LicenseY (casing p o) (sheen K p o X):=by
 let M:=masked K p o X; let F(W:Op I):FC I:=W.trace • 1
 have bill:=Girt.pole_w M F (by unfold F; fun_prop) (mask_env r u h)
 refine ⟨AtSupport.fromEval _ bill (fun _ _ l=>congrArg F (mask_local r u h _ _ l)) (fun _=>Reed.Fine.one.scale _),bill,?_⟩
 intro g x; rw [sheen,sheen,sheen_gauge r u h,twist_scalar,map_one]

end YM.CF.Merino

