import Merino.Corolla.Change
import YM.CF.Stax.Horizon

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Cube Stax Mew Fock
open scoped YM.CF.Mew

variable {I:Type}[LinearOrder I][Fintype I]
variable {n:Side}{P:BudgetPoint}{q:ℕ}{h:ℝ}

open Rill Rue

variable {H G : Bag n}{d c:Aura n→ℝ}
variable (X : Aura n) (D:Support (More n))(Y:Aura n)
variable (t:Bias (cipherK q) H P h c)

lemma beer (p:Flight P q X h (H X) (c X) (d X))(hh:0≤h)(w:3≤P.B):
 Fray P h (cipherK q) X ∅ (t.payX X ∅ X 1) (d X):=by
 have hx: Bias.αt X X ∅ (cipherK q):=⟨le_rfl,empty_subset _,by simp [Lattice.halo]⟩
 have z:Fray P h (cipherK q) X ∅ 1 1:=⟨Medal.oneT,fun _ _=>⟨hx.2.2, empty_subset _⟩⟩
 obtain ⟨B,T,S⟩:=p.forms
 let g:=T.offer X le_rfl ∅ hx.2.1 hx.2.2
 have r:= g.book z w le_rfl hh T.price; rw [mul_one] at r
 have v: t.payX X ∅ X 1=g.toCrate.motion 1:=by
    funext i; apply Subtype.ext; rw [t.truth _ _ _ _ hx i]
    change Sault.rind (_*1) = Sault.rind (coll_T P X ∅ B i*1)
    rw [mul_one,mul_one]
    unfold coll_T; split_ifs with k; swap; rfl
    open Salt in
     exact S X le_rfl _ (((pillar X.val (open_l P.threshold X.val (∅:Support (More n)))).choose_spec.2 i.1).2 k)
 rw [v]
 exact r

def machine : Copy n→ₗ[ℂ]Copy n where
 toFun:=t.payX X D Y
 map_add' A B:=by
   funext i; apply Subtype.ext
   by_cases u:Bias.αt Y X D (cipherK q)
   · change _ = (t.payX X D Y A i).val+(t.payX X D Y B i).val
     simp_rw [t.truth _ _ _ _ u i]; change Sault.rind (_*((A i).val+(B i).val))=_
     rw [mul_add]; exact map_add _ _ _
   unfold Bias.payX; rw [dif_neg u,dif_neg u,dif_neg u,zero_add]
 map_smul' a A:=by
   funext i; apply Subtype.ext
   change _ = a • (t.payX X D Y A i).val
   by_cases u:Bias.αt Y X D (cipherK q)
   · simp_rw [t.truth _ _ _ _ u i]; change Sault.rind (_*(a • (A i).val))=_
     rw [Algebra.mul_smul_comm]; exact map_smul _ _ _
   unfold Bias.payX; rw [dif_neg u,dif_neg u]; change 0 = a • (0:FC (Dwell n)); simp

lemma csum(g:I→Cipher n): ((∑j,g j):Cipher n).val=∑j,(g j).val:=by
 let L:Cipher n→+ FC (Dwell n) := ⟨⟨fun x=>x.val,rfl⟩,fun _ _=>rfl⟩; exact map_sum L _ _

/- Key full pays as a linear combination of fixed motion kernels. -/
variable {Z:I→Bag n}{r:I→Aura n→ℝ}(v:∀j:I, Bias (cipherK q) (Z j) P h (r j))
lemma matrix_ramp (a:Key I)(ha:H=∑j:I,a j • Z j)(F:Copy n):
 t.payX X D Y F = ∑j:I,a j • (v j).payX X D Y F:=by
 by_cases u:Bias.αt Y X D (cipherK q); swap
 · simp only [Bias.payX,dif_neg u,smul_zero,sum_const_zero]
 funext i; rw [Finset.sum_apply]; apply Subtype.ext; rw [t.truth _ _ _ _ u,csum]
 have S:coll_T P X D (H Y) i=∑j:I,a j • coll_T P X D (Z j Y) i:=by
    unfold coll_T; split
    · simp_rw [ha,Finset.sum_apply,Pi.smul_apply]
    rw [sum_eq_zero]; intro j _; rw [smul_zero]
 rw [S,sum_mul,Sault.rind,map_sum]
 exact sum_congr rfl fun j _=>by
   rw [Algebra.smul_mul_assoc,map_smul]
   change _=a j • (((v j).payX X D Y F) i).val
   rw [(v j).truth _ _ _ _ u]

end YM.CF.Merino.Corolla
