import Weft.Fiber
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Drift
open Finset Function
open scoped Topology BigOperators
open Mew
namespace Grain
variable {I:Type}[Fintype I][LinearOrder I]
attribute [-instance] instDecidableEqLex
local notation "Kb"=> Key (PairKey I)
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{D:Finset I}{f:Key (PairKey I)→E}
lemma dye(i:I)(k:Bool):River fun x:Kb=>x (pick i k):=by
    refine ⟨(continuous_apply (pick i k)).continuousOn,fun x hx j l p=>?_⟩; by_cases v:pick i k=j; subst j; simp only [update_self]; exact differentiableAt_id; simp_rw [update_of_ne v]; exact differentiableAt_const _
lemma reed(p:Grain D f):River f:=by
 induction p with
 | zero=>exact zeroR _
 | add _ _ l k=> exact dub_V l k
 | chip q F v _ _ _=>
   have h(i:PairKey I):River fun z:Kb=>entry (F i) (yard i) z:=by
     exact dub_V ((dye (yard i) false).scale (F i false)) ((dye (yard i) true).scale (F i true))
   have e(q:Finset (PairKey I)):River fun z:Kb=>∏ i∈q,entry (F i) (yard i) z:=by
     induction q using Finset.induction_on with
     | empty=> simp only [prod_empty]; exact zeroR _
     | insert a q H ih=> simp_rw [prod_insert H]; exact River.mul_T (h a) ih
   exact ⟨(e q).shore.smul continuousOn_const,fun i p j x h=> ((e q).slope i p j x h).smul (show DifferentiableAt ℂ (fun _:ℂ=> v) x from differentiableAt_const _)⟩
lemma horn(p:Grain D f)(i:PairKey I): tipI f [i]= f (pulse i.1 i.2 1):=by
 change cutI f _ 0=_
 rw [←(mitt p.reed roots i).deriv, show (fun w:ℂ=> f (update (0:Kb) i w))=(fun x:ℂ=> x • f (pulse i.1 i.2 1)) from funext (p.rad1 i.1 i.2)]
 simpa using ((hasDerivAt_id' (0:ℂ)).smul_const (f (pulse i.1 i.2 1))).deriv
end Grain
end YM.CF.Drift
end
