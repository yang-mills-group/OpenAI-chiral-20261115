import YM.CF.Tap.Limas
import YM.CF.Scroll.Bene
/-!# flavor: bridges
 One-fermion conventions, and commuting base AP charges.
 Distinguish this from a ColorT argument. Uses even charged-sectors independently.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF
namespace Mezzo
open Function NormedSpace Lattice Laurent Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "V𝕊" => UNI Slot
open Tap
variable (N:Side)
universe u
-- even polymorphic spatial charges. lambda priority
abbrev across(X:Type u)[Fintype X][DecidableEq X] : V𝕊 →* UNI (X×Slot):=
 { toFun:=fun a=>⟨(1:Op X) ⊗ₖ a.val, Matrix.kronecker_mem_unitary (U₁:=(1:Op X)) (by exact (unitary _).one_mem) a.property⟩
   map_one':=Subtype.ext Matrix.one_kronecker_one  -- maybe needs implicit m n
   map_mul':=fun i j=>Subtype.ext (show (1:Op X) ⊗ₖ (i.val*j.val)=(1:Op X)⊗ₖ i.val * (1:Op X)⊗ₖ j.val from by rw [op_kron_mul,one_mul]) }
-- specific instances
abbrev singlet : V𝕊 →* UNI (Single N):= across (Site N×SpinIdx)
abbrev pal : V𝕊 →* UNI (SpinIdx×Slot):=across SpinIdx
abbrev duet : V𝕊 → UNI (Site N×SpinIdx×Slot) := fun g=>⟨(1:Op (Site N)) ⊗ₖ (pal g).val, Matrix.kronecker_mem_unitary (one_mem (unitary _)) (pal g).property⟩
lemma love_coat (g:V𝕊): love N (duet N g).val=(singlet N g).val:=by
 ext ⟨⟨x,a⟩,i⟩ ⟨⟨y,b⟩,j⟩
 change ((1:Op (Site N)) ⊗ₖ ((1:Op SpinIdx)⊗ₖ g.val)) (x,a,i) (y,b,j) = ((1:Op (Site N×SpinIdx))⊗ₖ g.val) _ _
 by_cases h:x=y <;> by_cases p:a=b<;> simp [h,p]
lemma twistLook {X:Type u}[Fintype X][DecidableEq X](g:V𝕊)(A:Op X)(Z:Op Slot):
 twist (across X g) (A⊗ₖ Z)= A⊗ₖ twist g Z:=by
 rw [twist_formula,twist_formula]; change (1:Op X) ⊗ₖ g.val *_* star ((1:Op X)⊗ₖ g.val)=_; rw [op_star_kron,op_kron_mul,op_kron_mul,one_mul,star_one,mul_one]
section Bin
local notation "🔑"=> Op (SpinIdx× Slot)
local notation "B"=> bins Slot
abbrev vanish (X:Op (SpinIdx× Slot)) : Op (SpinIdx× Slot) :=B * X * (1-B)
lemma vBinned (X:🔑): Binned (vanish X):=by
 have h': (1-B)*(1-B)=1-B:=by rw [sub_mul,one_mul,mul_sub,mul_one,binsSq]; abel -- order of rw
 unfold vanish Binned; rw [←mul_assoc B,←mul_assoc,binsSq,mul_assoc _ (1-B),h'] -- tune
lemma turn_B (g:V𝕊) : twist (pal g) B=B:=by
 change twist (across SpinIdx g) (_⊗ₖ (1:Op Slot))= _
 rw [twistLook,map_one]; rfl
lemma turn_vanish (g:V𝕊) (A:🔑) : vanish (twist (pal g) A)= twist (pal g) (vanish A):=by
 unfold vanish; rw [map_mul,map_mul,map_sub,map_one,turn_B]
lemma spa_vanish (X:🔑) (i:Axis): spaX (vanish X) i=spaX X i:=by rw [vanish,←spa_p,spa_s]
lemma turn_spa (g:V𝕊)(X:🔑)(i:Axis) : spaX (twist (pal g) X) i= twist g (spaX X i):=by
 rw [←spa_vanish,turn_vanish,vanish,←spa_p,map_sum]; simp_rw [show ∀ i' j:Axis,twist (pal g) ((petal i')⊗ₖ spaX X j)=(petal i')⊗ₖ (twist g (spaX X j)) from fun i' j=> twistLook ..]; exact spa_s ..
end Bin
end Mezzo
end YM.CF
