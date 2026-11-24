import GaugeFieldConstruction.BoxM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
variable {I M:Type}[Fintype I][LinearOrder I][NormedCommRing M][NormedAlgebra ℂ M][CompleteSpace M]
structure Sect (I:Type) where
 reg : List (List I)
 pack : List I
def poet (p:List I) : List (Sect I) := match p with
 | []=> [⟨[],[]⟩]
 | [i]=> [⟨[[i]],[]⟩,⟨[],[i]⟩]
 | [i,j]=> [⟨[[i,j]],[]⟩,⟨[[i],[j]],[]⟩,⟨[[i]],[j]⟩,⟨[[j]],[i]⟩,⟨[],[i,j]⟩]
 | _=> []
lemma poet_max(p:List I):(poet p).length≤5:=by unfold poet; split<;>simp
structure Night(p:List I)(s:Sect I):Prop where
 subs : List.Perm (s.reg.flatten ++ s.pack) p
 duets : ∀ x∈s.reg,x≠[]
 holds : s.reg.length ≤ 2
lemma poet_b (p:List I)(s:Sect I)(i:s∈poet p): Night p s:=by
 unfold poet at i; split at i
 · simp only[List.mem_singleton] at i; rw[i]; exact ⟨List.Perm.refl _,by simp,by simp⟩
 · simp   at i; rcases i with rfl|rfl<;>exact ⟨List.Perm.refl _,by simp,by simp⟩
 · simp   at i; rcases i with rfl|rfl|rfl|rfl|rfl<;>first|exact ⟨List.Perm.refl _,by simp,by simp⟩|exact ⟨List.Perm.swap ..,by simp,by simp⟩
 simp only [List.not_mem_nil] at i
def Sect.wit (f g:Key I→M)(s:Sect I)(z:Key I):M:=(s.reg.map fun i=> lance f i z).prod*lance g s.pack z
variable {f g:Key I→ M}(hf:River f)(hg:River g)
include hf hg
private lemma cZmul (i:I)(v:Key I)(p:v∈hill I): cutI (f*g) i v=cutI f i v*g (dune i v)+f (dune i v)*cutI g i v:=(mitt (hf.mul_T hg) p i).deriv.symm.trans ((mitt hf p i).mul (mitt hg p i)).deriv
omit hg in
private lemma cZexp (i:I)(z:Key I)(p:z∈hill I): cutI (exp∘f) i z=exp (f (dune i z))*cutI f i z:=by
 rw [←(mitt hf.exp_V p i).deriv]; exact (hasFDerivAt_exp (𝕂:=ℂ)|>.comp_hasDerivAt _ (mitt hf p i)).deriv
private lemma hcXX (i j:I)(v:i≠ j) (z:Key I)(e:z∈hill I)(a:z i=0)(b:z j=0): lance ((exp∘f)*g) [i,j] z = exp (f z)* ((poet [i,j]).map (fun s=> Sect.wit f g s z)).sum:=by
 let E:=exp ∘ f; let eK:River E:=hf.exp_V; let D:=E ∘ dune i; let dK:River D:=eK.stay i
 let X:=cutI f i; let B:=g∘dune i; let T:=fun z=> (D*X) z* B z + D z * cutI g i z
 have hT:Set.EqOn (cutI (E*g) i) T (hill I):=by
    intro x t; rw [cZmul eK hg i _ t,cZexp hf i _ t]; rfl
 have hi:dune i z=z:=by change update _ _ 0=_; rw [←a,update_eq_self]
 have hj:dune j z=z:=by change update _ _ 0=_; rw [←b,update_eq_self]
 change cutI (cutI (E*g) i) j z= _; rw [twist_C j hT e]
 have h1:= fork_T ((dK.mul_T (hf.flow i)).mul_T (hg.stay i)) (dK.mul_T (hg.flow i)) j e
 change cutI T j z=cutI ((D*X)*B) j z+ cutI (D * cutI g i) j z at h1
 rw [h1,cZmul (dK.mul_T (hf.flow i)) (hg.stay i) _ _ e,cZmul dK (hf.flow i) _ _ e,cZmul dK (hg.flow i) _ _ e,hj]
 rw [show cutI B j z=_ from (dunk_C (f:=g) v) e,show cutI D j z=_ from (dunk_C (f:=E) v) e]; change ((cutI E j (dune i z)*X z + E (dune i z)* cutI X j z)*g (dune i z) + E (dune i z)*X z* cutI g j (dune i z)) + (cutI E j (dune i z)*cutI g i z + E (dune i z)*cutI (cutI g i) j z)=_
 simp only[hi,E,X, cZexp hf j z e,hj,poet, Sect.wit,lance, comp_apply,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.prod_cons,List.prod_nil]; ring
lemma silver (t:List I)(v:t.Nodup)(u:t.length≤2)(z:Key I)(p:z∈hill I)(a:∀ i∈t,z i=0): lance ((exp∘f)*g) t z= exp (f z)* ((poet t).map (fun i=> Sect.wit f g i z)).sum:=by
 match t with
 | []=> simp [poet,Sect.wit,lance]
 | [i]=>
    have hi:dune i z=z:=by change update _ _ 0=_; rw [←a i (by simp),update_eq_self]
    change cutI _ _ z=_; rw[cZmul hf.exp_V hg i z p,hi,cZexp hf i z p,hi]; simp only [poet,lance, Sect.wit,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.prod_cons,List.prod_nil, comp_apply]; ring
 | [i,j]=> exact hcXX hf hg _ _ (by simpa using v) z p (a _ (by simp)) (a _ (by simp))
 | i::j::k::l=>simp at u
end Iona
end YM.CF.Scree.Ing
end
