import YM.CF.Buffered.Weight

/-! # Fixed-native-period extraction at two sets of disjoint CAR sites
   Track positivity via occupation diag (don't ignore parity signs on columns).
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Fock Reflect Function Filter MeasureTheory NormedSpace Finset Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I]
local notation "W" => FC I
variable {a b:Bool} {S T : Finset I} {A B : FC I}
private lemma seatHeir (k:Finset I)(i:I)(h:i ∉ k)(p:i ∉ S)(e:Sector S false A): A (insert i k) (insert i k)=A k k:=by
 let j:= insert i k; let x:=basisKet j; let y:=basisKet k; let u:= put i
 have he : Commute A u:=by simpa [Commute,SemiconjBy,Sector.grainB] using e.apart (Sector.up i (show i∈({i}:Finset I) from mem_singleton_self _)) (disjoint_singleton_right.mpr p)
 have hx:x= parity i k • acts u y:= create_basis_is i k h
 change A j j=_; rw [← basis_act A j j, ←basis_inner]; change inner ℂ x (acts A x)=_
 rw [hx, map_smul, inner_smul_left,inner_smul_right,←act_mul,he.eq,act_mul]
 let z:= acts A y
 rw [show inner ℂ (acts u y) (acts u z)=inner ℂ y z from ?_]
 · change star (parity i k)*(parity i k * _)=_; rw [parity_star,←mul_assoc,parity_sq,one_mul]; simp [y,z]
 rw [←act_inner, ←act_mul (star u)]
 rw [show acts (star u*u) y=y from (vacant_act i k).trans (if_neg h)]

lemma countRoom (k:Finset I)(e:Sector S false A): A k k=A (k∩S) (k∩S):=by
 -- erase outside. insert only OUTSIDE; inside induction conditional
 let R:=k∩S
 suffices h:∀ t⊆ (k \ S), A (t∪R) (t∪R)=A R R from by
    have he: k \ S∪R=k:=by ext; simp only [Finset.mem_union, R, Finset.mem_inter, Finset.mem_sdiff]; tauto
    rw [←he]; nth_rw 3 4 [he]; exact h (k \ S) le_rfl
 intro t p; induction t using Finset.induction_on with
 | empty=>simp
 | insert i t g ih=>
    have w:= Finset.mem_sdiff.mp (p (mem_insert_self ..)); have hv:i∉R:=by simp [R,w]
    rw [insert_union,seatHeir _ i (by simp [g,hv]) w.2 e]
    exact ih ((subset_insert ..).trans p)

private lemma there (A:W)(h:A≠0) : ∃ s:Finset I,(star A*A) s s≠0:=by
 by_contra! p
 have he(s:Finset I) : acts A (basisKet s)=0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp 
    nth_rw 1 [show A=star (star A) from (star_star _).symm]; rw [act_inner, ← act_mul, basis_inner,basis_act,p]
 exact h (op_columns (fun i=> by rw [act_zero,he]))
lemma splitNK (h:Disjoint S T)(p:Sector S a A)(q:Sector T b B)(t:A≠0)(u:B≠0) : A*B≠0:=by
 obtain ⟨x,X⟩:= there A t; obtain ⟨y,Y⟩:= there B u; let k:= (x∩S)∪(y∩T)
 have ht: Sector S false (star A*A):= by simpa only [Bool.xor_self] using p.contr.mul p
 have hu: Sector T false (star B*B):= by simpa only [Bool.xor_self] using q.contr.mul q
 have he:k∩S=x∩S:=by
    ext i; by_cases p:i∈ S; · simp [k,p,(Finset.disjoint_left.mp h p)]
    simp [p]
 have hy:k∩T=y∩T:=by
    ext i; by_cases p:i∈T; · simp [k,p,(Finset.disjoint_left.mp h.symm p)]
    simp [p]
 have g:Commute (star A * A) (star B):=by simpa [Commute, SemiconjBy,Sector.grainB] using ht.apart q.contr h
 intro f; have H : star (A*B)*(A*B)=star A*A*(star B*B):=by rw [star_mul,←mul_assoc, mul_assoc (star B),g.symm.eq,mul_assoc]
 have hp:(star A*A*(star B*B)) k k ≠ 0:= by
    rw [ht.sliced hu h, countRoom _ ht,countRoom k hu,he,hy,←countRoom _ ht,←countRoom _ hu]; exact mul_ne_zero X Y
 rw [← H,f,mul_zero] at hp; exact hp rfl

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
