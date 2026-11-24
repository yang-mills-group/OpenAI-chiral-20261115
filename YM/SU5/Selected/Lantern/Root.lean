import YM.SU5.Selected.Lantern.Stock
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
-- Determinant factor for covariant frames. In this orientation remove uses conjugate scalar on Ket; keep it.
open Stencil
variable {n q:Type*}[Fintype n][LinearOrder n][Fintype q][DecidableEq q]
def tone (b:Bool):ℂ→*ℂ:= if b then (starRingEnd ℂ).toMonoidHom else MonoidHom.id _
lemma tax_r (b:Bool)(k:Ket n)(c:ℂ): creed b (c • k)= tone b c • creed b k:=by cases b; exact create.map_smul c k; change star (create (c • k))=star c • _; rw [map_smul,star_smul]; rfl
lemma toil (b:Bool)(i:Ket n): creed b i*creed b i=0:=by
 cases b; exact create_sq i; change star (create i)*star (create i)=_; rw [← star_mul,create_sq,star_zero]
def party (X:q→Ket n)(b:Bool)(L:List q): FC n:= foil (fun i=> creed b (X i)) L
-- blade duplication lemma via first-last rotation. no `Even` claim each odd by Contract.
private lemma doubleL {V:Type*}[Ring V](a:V)(f:q→V)(j:q)(p:∀ i:q, a*f i=-(f i*a))(g:a*f j=0) (L:List q): j∈L→ a*foil f L=0:=by induction L with
 | nil=> simp
 | cons i L ih=> intro u; rcases List.mem_cons.mp u with t|t; subst j; rw [foil,List.map_cons,List.prod_cons,←mul_assoc,g,zero_mul]
                 change a*(f i*foil f L)=_; rw [←mul_assoc,p,neg_mul,mul_assoc,ih t,mul_zero,neg_zero]
private lemma doubleR {V:Type*}[Ring V](a:V)(f:q→V)(j:q)(p:∀ i:q,f i*a=-(a*f i))(g:f j*a=0) (L:List q): j∈L→ foil f L*a=0:=by induction L using List.reverseRecOn with
 | nil=> simp
 | append_singleton L i ih=>
    intro u; change ((L ++ [i]).map f).prod * a=_; rw [List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,mul_assoc]; rcases List.mem_append.mp u with t|t
    · unfold foil at ih; rw [p,mul_neg,←mul_assoc,ih t,zero_mul,neg_zero]
    obtain rfl:=List.mem_singleton.mp t; rw [g,mul_zero]
private lemma trans (X Y:q→Ket n)(b:Bool)(c:ℂ)(i j:q)(t:i≠j) (g:Y j=X j+c • X i)(v:∀ k:q,k ≠ j → Y k=X k)(L:List q)(p:L.Nodup)(hi:i∈L)(hj:j∈L): party Y b L=party X b L:=by
 let x(k:q):= creed b (X k); let y(k:q):= creed b (Y k); have he(K:List q)(p:j∉K):foil y K=foil x K:= congrArg List.prod (List.map_congr_left (fun i h=> congrArg (creed b) (v i (fun q=> p (q ▸ h)))))
 obtain ⟨K,A,rfl⟩:=List.append_of_mem hj; rw [List.nodup_append] at p; obtain ⟨l,P,h⟩:=p; obtain ⟨u,r⟩:= List.nodup_cons.mp P; have hx(j q):x j*x q=-(x q*x j):= same_letter (b:=b) ⟨X j,rfl⟩ ⟨X q,rfl⟩
 change foil y _=foil x _; rw [show foil y _=foil y K*(y j*foil y A) from ?_,show foil x _=foil x K*(x j*foil x A) from ?_,he A u, he K (fun x=> (h j x j List.mem_cons_self rfl)),show y j=x j+tone b c • x i from ?_,add_mul,mul_add];
 all_goals try first | solve | (unfold y x; rw [g,creed_a,tax_r]) | simp only [foil, List.map_append,List.prod_append,List.map_cons,List.prod_cons] -- any_goals may unfold too much! 
 rw [add_eq_left]; rcases List.mem_append.mp hi with t'|t'
 · rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,←mul_assoc,doubleR _ x i (fun j=>hx j i) (toil ..) K t',zero_mul,smul_zero] -- fold
 · rw [Algebra.smul_mul_assoc,doubleL _ x i (fun j=> hx i j) (toil ..) A ((List.mem_cons.mp t').resolve_left t), smul_zero,mul_zero]
private lemma party_toll (b:Bool)(L:List q)(f:q→ℂ)(v:q→Ket n): party (fun i=>f i • v i) b L=tone b (L.map f).prod • party v b L:=by
 induction L with|nil=> simp [party,foil]|cons i L h=> rw [show party _ b _=creed b (f i • v i)*party (fun i=>f i • v i) b L from rfl,h]; rw [tax_r,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,List.map_cons,List.prod_cons,map_mul,smul_smul]; rfl -- tune
-- use lease list always toList univ, no reordering. λ matrices T selection rank$colors=10$ both.
def tape (b:Bool)(X:WRect n q):= party (col X) b (Finset.univ.toList)
lemma wave_det (b:Bool)(A:Op q):∀ X: WRect n q, tape b (X*A)=tone b A.det • tape b X:=by
 apply Matrix.diagonal_transvection_induction _ A
 · intro d _ X; unfold tape; rw [show col (X*Matrix.diagonal d)=(fun i:q=> d i • col X i) from ?_, party_toll, Finset.prod_map_toList, Matrix.det_diagonal]; ext1 i; apply PiLp.ext; intro j; rw [col_val,Matrix.mul_diagonal]; change X j i * d i = d i * X j i; ring
 · intro a X; rw [Matrix.TransvectionStruct.det, map_one, one_smul,tape,tape]; refine trans _ _ _ a.c a.i a.j a.hij ?_ ?_ _ (Finset.nodup_toList _) (by simp) (by simp)
   · apply PiLp.ext; intro i; rw [col_val]; unfold Matrix.TransvectionStruct.toMatrix; rw [Matrix.mul_transvection_apply_same]; rfl
   intro k p; apply PiLp.ext; intro i; rw [col_val]; unfold Matrix.TransvectionStruct.toMatrix; rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ p]; rfl
 intro A B h g X; rw [← Matrix.mul_assoc,g,h, Matrix.det_mul,smul_smul,map_mul,mul_comm]
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms tape
#print axioms wave_det
