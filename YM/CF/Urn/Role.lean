import YM.CF.Urn.Haven
import YM.CF.Urn.Shaft
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Urn
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa
variable {I α ι n m: Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]
open Stilo Scree Hake
open Pastry
variable (b r:Bool)(U:UNI n)(V:UNI m)
abbrev spear(B:Oak n)(x:Oboe n)(y:Oboe n):ℂ:= soar B (twigCab x) (twigCab y)+soar B (twigCab y) (twigCab x)
def KindX(P: Twig n→ Twig n→ℂ): Prop:= (∀ i j,P (twigExt i) (twigExt j)+P (twigExt j) (twigExt i)=0) ∧ ∀ i j,P (twigCab i) (twigCab j)+P (twigCab j) (twigCab i)= if i=Hake.revertP j then 1 else 0
def dimeF(P: Twig n→ Twig n→ℂ)(F:Twig n→ LeanV m→ℂ)(h:KindX P):FC (LeanV n)→ₗ[ℂ] FC n→ₗ[ℂ] FC (LeanV m):= petL P F twigExt twigCab h.1 h.2
lemma opus(A F:Ax n m)(P Q:Oak n)(h:KindX (soar P))(k:KindX (soar Q))(p:tendA b r U V A F)(q:playX b r U P Q)(T:List (LeanV n))(L:List (Oboe n)):lotY b r V (dimeF (soar P) (mount A) h (rollC put T) (rollC bell L))=dimeF (soar Q) (mount F) k (lotY b r U (rollC put T)) (lotB b r U (rollC bell L)):=by
 let X:= hoodY U r; have hy : ∀ i j,lotY b r V (Stilo.price (soar P) (LeanV m) i j)=Stilo.price (taxL X (soar Q)) (LeanV m) i j:= by intro i j; unfold Stilo.price X; rw [lonY,map_one,taxi b r U P Q q]
 let A':=lotY b r U; let C':=lotY b r V; let B:=lotB b r U
 have hx:= octave (mount A) (mount F) (soar P) (soar Q)  A' B C' (u:=twigExt) (v:=twigCab) X (sewV U r) (sewV U r) h.1 h.2 k.1 k.2 hy (trimH b r U V A F p) (fun i=>mold b r U i) (fun i=>mole b r U i) (fun i=> trit r U (chim (soar Q) (mount F)) true i) (fun i=> trit r U (chim (soar Q) (mount F)) false i) T L
 exact hx
lemma visage (b r:Bool)(U:UNI n)(F:FC n)(c:ℂ): lotB b r U (c • F)= cSignX (b.xor r) c • lotB b r U F:=cumin ..
section
-- generic left multilinearity, linear extension to projected coeff x, all charges.
lemma duet (i: Finset n × Finset n): ∃ L:List (Oboe n),piano i=rollC bell L:=by
 let P(j:n): Oboe n:=(true,j); let B(j:n):Oboe n:=(false,j)
 let l:=i.1.sort (· ≤ ·); let L:=i.2.sort (· ≤ ·)
 refine ⟨l.map P ++ L.reverse.map B,?_⟩; have he(t:List n): star ((t.map put).prod)=rollC bell (t.reverse.map B):=by
    induction t with| nil=> simp [rollC]| cons i t ih=> rw [List.map_cons,List.prod_cons,star_mul, ih,List.reverse_cons,List.map_append, Hake.lump]; simp only [rollC,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]; rfl
 rw [Hake.lump]; unfold piano; change rollC put l * star ((L.map put).prod)= _; rw [he,rollC, rollC,rollC, show List.map bell (l.map P) = l.map put from (List.map_map ..)] -- tune
lemma along_p (T:Finset n) :∃ L:List n,poke T=rollC put L:=⟨T.sort (· ≤ ·),rfl⟩
lemma caprice(A F:Ax n m)(P Q:Oak n)(h:KindX (soar P))(k:KindX (soar Q))(p:tendA b r U V A F)(q:playX b r U P Q)(x:FC (LeanV n))(v:spanP (LeanV n) x)(y:FC n) : lotY b r V (dimeF (soar P) (mount A) h x y)=dimeF (soar Q) (mount F) k (lotY b r U x) (lotB b r U y):=by
 have hp: y=pour ((hope n).symm y):=by
    conv_lhs=> rw [← (hope n).apply_symm_apply y]
    let H:=(hope n).symm y; change wont orchestra H= _; simp [wont,playB,pour,H]
 rw [v,hp]; unfold pour; -- tune occurrences, don't rw recur
 simp_rw [map_sum,LinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _; simp_rw [visage,lonY,map_smul,LinearMap.smul_apply,lonY]; obtain ⟨S,g⟩:=duet (n:=n) j; obtain ⟨T,l⟩:= along_p (n:=LeanV n) i; rw [g,l,opus _ _ _ _ _ _ _ _ _ _ p q]
end
end YM.CF.Urn
