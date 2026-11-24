import YM.CF.Scion.Verge
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
lemma picks_w (f:ι→A)(X:List ι): picks (X.map f)=(picks X).map fun i=>⟨i.neg,f i.front,i.back.map f⟩:=by
 induction X with| nil=>rfl| cons i X ih=> rw [List.map_cons,picks,ih,picks,List.map_cons,List.map_map,List.map_map]; rfl
lemma tribe (f:ι→A)(X:List ι)(P:A→ FC n)(C:A→ A→ FC n): taskC P C (X.map f)=taskC (P∘f) (fun i j=>C (f i) (f j)) X:=by
 induction p:X.length using Nat.strong_induction_on generalizing X with
 | h a ih=> cases X with
            | nil=>rfl
            | cons i X=>
                rw [List.length_cons] at p; rw [List.map_cons,task_one,task_one,picks_w, ih X.length (by omega) _ rfl,List.map_map]; unfold Function.comp; congr 2; apply List.map_congr_left; intro j v; dsimp only; rw [ih j.back.length (by have hp:= picks_mem v; omega) _ rfl]; rfl
variable (W:Weave m M)
def portX: Weave n M where
 seats:=W.seats ∘ (tinOre e)
 pals i j:=W.pals (tinOre e i) (tinOre e j)
 ward:=by constructor; intro i j; exact W.ward.1 (ore_b e i) (ore_b e j); intro i j; change W.pals (twigCab (ore_b e i)) (twigCab (ore_b e j))+W.pals (twigCab (ore_b e j)) (twigCab (ore_b e i))= _; rw [show _+_= _ from W.ward.2 (ore_b e i) (ore_b e j), ←show ore_b e (revertP j)=revertP (ore_b e j) from rfl]; simp only [(ore_b e).injective.eq_iff]
lemma podT (P:List (LeanV n))(L:List (Oboe n)): issue (portX e W) (rollC put P) (rollC bell L)=taskC (lank W.seats) (Stilo.price W.pals (LeanV M)) ((Scion.cue P L).map (tinOre e)):=by rw [tribe,ring_u]; rfl
end YM.CF.Scion
