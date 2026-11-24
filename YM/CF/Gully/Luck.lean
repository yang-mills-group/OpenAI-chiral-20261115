import YM.CF.Gully.Cube
import YM.CF.Scion.Verge
import YM.CF.Spark.Org
import YM.CF.Spire.Thick
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
section
open Spark
variable {I J:Type*}[LinearOrder I][Fintype I][LinearOrder J][Fintype J](e:I≃J)
variable {S:Op I}{P:Op J}(h:IsStarProjection S)(g:IsStarProjection P)(q:S=portW e.symm P)
local notation "W"=>Scion.ore_b e
include q h g
lemma cubic_C(X:ribbon J)(w:Wave J): cartsL e.symm (acts ((nursery P g).cook X) w)=acts ((nursery S h).cook (Artifact W X)) (cartsL e.symm w):=by
 let A:=cisT W; let F:= (nursery P g); let Q:=(nursery S h)
 change cartsL e.symm (acts (F.eval X.val) w)= acts (Q.eval (A X.val)) _; let V(s:Finset (LeanV J)):=A (poke s); have he(s)(p:Wave J): cartsL e.symm (acts (F.eval (poke s)) p)=acts (Q.eval (V s)) (cartsL e.symm p):=by
    rw [F.eval_oneT]; induction s using Finset.induction_on_min generalizing p with
    | empty=>simp only [V,poke,Poly.tag_void,map_one,Q.eval_one]; rfl
    | insert j S k ih=>
       unfold V; rw [Poly.tag_min _ _ _ k,poke,Poly.tag_min _ _ _ k,map_mul]; change cartsL _ (acts ((drawT P j)*_) p)= acts (Q.eval (A (put j)*V S)) _; obtain ⟨v,hv⟩:= coal W S
       have ht: Scree.spanP _ (V S):=by unfold V A; rw [hv]; exact Scree.spanS (Scree.spanPt _) _
       rw [show A (put j)= _ from trails W _, show put ((Scion.ore_b e).symm j)=poke {(Scion.ore_b e).symm j} from (Poly.tag_once (cane _) _).symm,Scree.fireT Q (Scree.spanPt ..) ht,Q.eval_oneT,Q.tag_once,act_mul,act_mul,←ih]
       have hh:= Scion.crease e.symm (acts (F.tag S) p) P j; rw [←q] at hh; exact hh
 rw [(fineShape X).allP,map_sum,map_sum,map_sum,act_sum,act_sum, cartsL,map_sum]; apply sum_congr rfl; intro i hi; rw [map_smul,act_smul,show A (_ • _)= _ from coastP ..,map_smul Q.eval,act_smul,map_smul]; exact congrArg _ (he i w)
omit q h g
open Urn Hake Scree
variable {U:UNI I}{V:UNI J}(b r:Bool)
private lemma tink (t:portW e.symm V.val=U.val) (x y:LeanV I): (spice U r).val x y=(spice V r).val (W x) (W y):=by
 rcases x with ⟨i,x⟩; rcases y with ⟨j,y⟩; cases r<;>cases i<;>cases j<;> simp [spice,jump_apply,invFilm,opBool,ccU, closeV,Pastry.thread, Scion.ore_b,← t,portW,phaseU] -- tune
lemma stone (t:portW e.symm V.val=U.val) (i:LeanV J):cisT W (Scree.sauce b r V (put i))=sauce b r U (cisT W (put i)):=by
 obtain ⟨a,rfl⟩:=(Scion.ore_b e).surjective i; cases a with | mk y x=>
  change cisT W (sauce b r V (wire y (e x)))=_; rw [trails,Equiv.symm_apply_apply]; rw [leafU,leafU,map_sum]; symm; refine Fintype.sum_equiv e _ _ fun j=>?_; rw [coastP,show cisT W (wire (y.xor r) (e j))=wire (y.xor r) j from (cx_p W (y.xor r,j)).1, tink e r t]; rfl
lemma bringB(t:portW e.symm V.val=U.val)(X:ribbon J): Artifact W (paintR b r V X)=paintR b r U (Artifact W X):=by
 apply Subtype.ext; let L:= cisT W; let B:=lotY b r U; let G:=lotY b r V; change L (G X.val)=B (L X.val); rw [(fineShape X).allP,map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; intro i _; rw [show G (_ • _)=_ from Ione.G_lot .., show L (cSignX _ _ • _)= _ from coastP ..,show L (_ • _)=_ from coastP .., show B (_ • _)=_ from Ione.G_lot ..]; congr 1
 induction i using Finset.induction_on_min with
 | empty=>simp only [poke,Poly.tag_void,map_one]
 | insert j T p ih=> rw [poke,Poly.tag_min _ _ _ p, map_mul,map_mul,map_mul,map_mul,show L (G (poke T))= _ from ih (mem_univ _), show L (G ((cane _).term j))= _ from stone e b r t j]; rfl
end
end YM.CF.Gully
