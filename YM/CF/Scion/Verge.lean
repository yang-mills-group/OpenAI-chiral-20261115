import YM.CF.Scion.Vice
import YM.CF.Girt.Tree
import YM.CF.Hive.Good
import YM.CF.Levier.CrestD
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]
variable {m:Type*}[LinearOrder m][Fintype m](e:n≃m)(w:Wave n)
abbrev ore_b := Equiv.prodCongr (Equiv.refl Bool) e
abbrev ore:= Equiv.sumCongr (ore_b e) (ore_b e) -- elaborate as Twig Lex defeq
open Matrix
lemma longB {F:n→ FC n}{G:m→ FC m}{P:Op n}{R:Op m} (h:∀ z:Wave n, ∀ i:n, cartsL e (acts (F i) z)=acts (G (e i)) (cartsL e z))(k: R=portW e P)(i:n): cartsL e (acts (prong F P i) w)=acts (prong G R (e i)) (cartsL e w):=by
 rw [prong,prong,act_sum,act_sum,cartsL,map_sum]; refine Fintype.sum_equiv e _ _ fun z=>?_ ; rw [act_smul,act_smul,map_smul,show R (e z) (e i)=_ from ?_]; exact congrArg ((P z i) • ·) (h _ _)
 rw [k]; simp [portW]
lemma crease (P:Op n)(i:LeanV n): cartsL e (acts (drawT P i) w)=acts (drawT (portW e P) ((ore_b e) i)) (cartsL e w):=by
 rcases i with ⟨u,i⟩; cases u <;> simp only [Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map,drawT,ite_true,Bool.false_eq_true,↓reduceIte,hideF, seekF]
 · exact longB e w (P:=cc P) (fun z i=>hoist_t e.toEmbedding ∅ (shelfG e) i z) rfl i
 apply longB e w (fun z i=> hoist_put e.toEmbedding ∅ i z); ext i j; simp [portW, Matrix.one_apply]; -- tune k
lemma grooveK (i:Oboe n): cartsL e (acts (bell i) w)=acts (bell (ore_b e i)) (cartsL e w):=by rcases i with ⟨b,i⟩; cases b; exact hoist_t _ _ (shelfG e) _ _; exact hoist_put ..
abbrev tinOre : Twig n≃ Twig m:= ore e
lemma warpGram (P:Op n)(p:IsStarProjection P)(F:List (LeanV n))(T:List (Oboe n)): let K:=portW e P
 cartsL e (acts ((nursery P p).eval (rollC put F)* rollC Hake.bell T) w)= acts (rollC (Proa.dialL (stick (portW e P))) ((Scion.cue F T).map (tinOre e))) (cartsL e w):=by
 intro K
 rw [Hake.chant,Scion.cue,List.map_append,List.map_map,List.map_map,Hake.lump]
 have he (F:LeanV n→FC n)(H:LeanV n→FC m)(k:∀ z i,cartsL e (acts (F i) z)=acts (H i) (cartsL e z))(Y:List (LeanV n))(x:Wave n): cartsL e (acts (rollC F Y) x)= acts (rollC H Y) (cartsL e x):=by
    induction Y generalizing x with
    | nil=> rw [show rollC F []=1 from rfl,show rollC H []=1 from rfl,act_one,act_one]
    | cons i t ih=> change cartsL _ (acts (_*rollC F t) _) =acts (_ * rollC H t) _; rw [act_mul,act_mul,←ih,k] -- k pattern lhs
 have hg(i):Proa.dialL (stick K) ((tinOre e) (twigExt i))=drawT K (ore_b e i):=stickUp K _; have hx(i):Proa.dialL (stick K) ((tinOre e) (twigCab i))=bell (ore_b e i):=stickLo .. -- me
 let J:=(nursery P p); let D:=Proa.dialL (stick K); let C:= D ∘ tinOre e
 change cartsL _ (acts (rollC J.term _*_) _)=acts (rollC D _* rollC D _) _
 rw [act_mul,act_mul]
 unfold rollC; rw [List.map_map,List.map_map];
 change cartsL _ (acts (rollC J.term F) (acts (rollC bell T) w)) = acts (rollC (C∘twigExt) F) (acts (rollC (C ∘ twigCab) T) _);
 rw [he J.term (C ∘ twigExt),he bell (C ∘ twigCab)];
 · intro z i; change cartsL _ _ =acts (D _) _; rw [show D _= _ from hx _]; exact grooveK ..
 intro z i; change cartsL _ _=acts (D _) _; rw [show D _= _ from hg _]; exact crease ..
end YM.CF.Scion
