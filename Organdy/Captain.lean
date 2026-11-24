import Organdy.Hyssop
import YM.CF.Sault.Faro
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)


section
variable {m:Type} [LinearOrder m][Fintype m]
variable {A B:Op m}(u:IsStarProjection A)(v:IsStarProjection B)(c r:Bool)(U:UNI m)
variable (e:sings c U A=swapX r B)
open Sault
/-- Every wave can be obtained with a purely positive-leg exterior expression. -/
lemma paintExists(x:Wave m):∃ F:FC m, spanP m F ∧ acts F (vacuum m)=x:=by
  refine ⟨∑i:Finset m,x.ofLp i • poke i,snack (fun i _=>spanS (spanPt i) _),?_⟩
  rw [act_sum]; simp_rw [act_smul,poked]; exact basis_expand ..

include e
lemma sustains (x:FC (LeanV m)) (a:spanP _ x) :
   Spire.tourP U c r ((nursery A u).eval x) =
   (nursery B v).eval (sauce c r U x):=by
 let H:= nursery A u; let G:=nursery B v; let W:=sauce c r U
 change Spire.tourP _ _ _ (H.eval x)=G.eval (sauce c r U x)
 -- adapts appleT
 rw [a,map_sum,nutmeg,sauce,singT,win_sum,map_sum,map_sum]
 refine sum_congr rfl fun i _=> ?_
 rw [map_smul,cumin,win_c,twist_scalar,map_smul,H.eval_oneT]; congr 1
 change Spire.tourP U c r (H.tag i)=G.eval (W (poke i))
 clear ‹i ∈ _›
 induction i using Finset.induction_on_min with
 | empty=> rw [poke, Poly.tag_void,Poly.tag_void,show W 1=1 from ?_,G.eval_one]; cases r <;> simp [Spire.tourP,singT,theta_one,win_i]
           unfold W sauce; rw [singT,win_i,map_one]
 | insert j z k ih=>
    rw [poke, Poly.tag_min _ _ _ k,Poly.tag_min _ _ _ k,nomZ,show W (_*_)=_ from singm ..]
    change _=G.eval (W (put (n:=LeanV m) j)*W (poke z))
    rw [fireT G (show spanP (LeanV m) (W (put j)) from (show poke {j}=put j from Poly.tag_once (cane _) _) ▸ sauceS c r U {j}) (sauceS c r U z),ih]
    congr 1; exact (apple u v c r U e j).symm

omit e
-- symbol waves motion is quantU spice ∘ dove.
abbrev sailQ (c r:Bool)(U:UNI m)(x:Wave (LeanV m)):= 
 acts (quantU (spice U r)).val (dove (c.xor r) x)

lemma sail_move (z:FC (LeanV m))(x:Wave (LeanV m)):
   sailQ c r U (acts z x)=acts (sauce c r U z) (sailQ c r U x):=by
  unfold sailQ sauce;rw [singT,dove_acts,Fock.swivel]
lemma sail₀: sailQ c r U (vacuum (LeanV m))=vacuum (LeanV m):=by
 unfold sailQ vacuum;rw [dove_base]; exact quant_vac ..

include e
lemma ballMoves(q₀ z:Wave m)(x:Wave (LeanV m)):
  arum U c r q₀ (ballL (nursery A u) z x)=
    ballL (nursery B v) (arum U c r q₀ z) (sailQ c r U x):=by
  obtain ⟨F,a,he⟩:=paintExists x
  rw [←he,loaf,sail_move,sail₀,loaf,arum_act,sustains u v c r U e _ a]
omit e

lemma dove_twice {y:Type}[Fintype y](b:Bool)(w:Ket y): dove b (dove b w)=w:=by
  ext1; cases b <;> simp [dove,cSignX]

lemma sailOnto: Surjective (sailQ c r U):=by
  intro y; let t:=quantU (spice U r)
  use dove (c.xor r) (acts (star t.val) y)
  unfold sailQ
  change acts t.val _=_
  rw [dove_twice,←act_mul,t.property.2,act_one]
end
