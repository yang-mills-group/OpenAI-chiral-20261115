import Organdy.Buoy
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open PowerSeries
namespace Palmlet

lemma scaled (F:Copy n) (s:ℝ)(v:Palmlet F): Palmlet (s • F):= 
 fun i t=>congrArg (fun x:Cipher n=> s • x) (v i t)

lemma stow {ι:Type*}(A:Finset ι)(f:ι → Copy n)(t:∀ i∈A,Palmlet (f i)):
    Palmlet (∑ i∈A,f i):=by
  intro x t'
  rw [Finset.sum_apply,Finset.sum_apply]
  exact sum_congr rfl fun i v=> t _ v x t'

lemma files {ι:Type*}(A:Finset ι)(f:ι → Copy n)(t:∀ i∈A,Palmlet (f i)):
    Palmlet (∏ i∈A,f i):=by
  intro x t'
  rw [Finset.prod_apply,Finset.prod_apply]
  exact prod_congr rfl fun i v=> t _ v x t'
end Palmlet

variable (F:ForceBudget n)
local notation "rF"=> settleK F
variable {a0 b0:I→Aura n→ℝ}{V:I→Bag n} {σ:I→Seat n}
variable (u:Pollen p q h σ V a0 b0)
local notation "C:" z:max=> Cadre.chip (u.soar z) rF
lemma Pollen.downed (z:Key I)(X:Aura n)(D:Support (More n))(k:ℕ):
    coeff (k+1) ((C:z) X D) =
    ((k:ℝ)+1)⁻¹ • ∑ Y:Aura n, ∑ G∈ drum X Y D, u.soar z X D Y (
      ∑ l∈finsuppAntidiag G k,∏ i∈G, coeff (l i) ((C:z) i (D∩i.val))) :=by
  nth_rw 1 [Cadre.peel]
  rw [Cadre.sprig,Cadre.ore]
  simp_rw [coeff_prod]

lemma Pollen.neat (k:ℕ)(X:Aura n)(z:Key I):
    Palmlet (coeff k ((C:z) X ∅)):=by
  induction k using Nat.strong_induction_on generalizing X with
  |h k ih=>
    cases k with
    |zero=> rw [Cadre.peg,settle0]; exact fun _ _=>rfl
    |succ k=>
      rw [u.downed]
      apply Palmlet.scaled
      apply Palmlet.stow; intro Y _
      apply Palmlet.stow; intro G _
      apply u.peaceful
      apply Palmlet.stow; intro l t
      apply Palmlet.files; intro i hp
      rw [empty_inter]
      exact ih (l i) (Nat.lt_succ_of_le ((single_le_sum (fun j _=>Nat.zero_le (l j)) hp).trans_eq
        (mem_finsuppAntidiag.mp t).1)) _

lemma Pollen.settle (k:ℕ)(X:Aura n)(D:Support (More n)):
    Hush σ X.val (fun z=> coeff k ((C:z) X D)):=by
  induction k using Nat.strong_induction_on generalizing X D with
  |h k ih=>
    intro z hz w hw v
    change coeff k ((C:z) X D)=coeff k ((C:w) X D)
    cases k with
    |zero=> simp_rw [Cadre.peg]
    |succ k=>
      rw [u.downed,u.downed]
      refine congrArg (fun x=>_ • x) (sum_congr rfl fun Y _=>?_)
      refine sum_congr rfl fun G t=>?_
      have hh:= ((Cadre.drum_p ..).mp t).2.2
      have hg:Y.val⊆ X.val:=hh ▸ subset_union_left
      rw [u.quietly z w (fun i hi=>v i (hg hi))]
      refine congrArg (u.soar w X D Y) (sum_congr rfl fun l t=>prod_congr rfl fun i hp=>?_)
      have hu:i.val⊆X.val:=hh ▸ (Cadre.coneL hp).trans subset_union_right
      exact ih (l i) (Nat.lt_succ_of_le ((single_le_sum (fun j _=>Nat.zero_le (l j)) hp).trans_eq
        (mem_finsuppAntidiag.mp t).1)) _ _ z hz w hw (fun j hj=>v j (hu hj))

lemma Pollen.unkeyed (k:ℕ) : layerN rF (u.soar 0) k=rF:=by
  funext X D
  change (∑ i∈range (k+1),coeff i ((C:0) X D))=_
  rw [sum_eq_single 0,Cadre.peg]
  · intro i _ hk
    cases i
    · exact False.elim (hk rfl)
    rw [u.downed]
    simp [u.vacated]
  simp

variable {r:Aura n→Support (More n)→ℝ} {c:Occlus p}

lemma Pollen.rafter (w:3≤p.B)(t:0≤h)
  (fr:∀ (X:Aura n),∀ D⊆X.val,Fray p h (cipherK q) X D (settleK F X D) (r X D))
  (m:Timer (uChip (∑ i:I,a0 i) (∑ i:I,b0 i) r) (∑ i:I,a0 i) c.κ c.uΓ c.w (widthK n p.B) (spanV p.B) c.γ c.c c.d c.e 1 (∑ i:I,b0 i)):
  OrbitRack c σ q F h u.soar (∑ i:I,a0 i) (∑ i:I,b0 i) r (trawling V):=by
  refine ⟨fr,fun z hz=>(u.stock w t z hz).toPitch,fun z hz X=>(u.stock w t z hz).birth X,
    u.cardamom,?_,?_,u.unkeyed F,m⟩
  · intro k X D _ z hz x hx p
    unfold layerN
    exact sum_congr rfl fun i _=> u.settle F i X D z hz x hx p
  intro z k X v t
  exact Palmlet.stow _ _ (fun i (_:i∈range (k+1))=>u.neat F i X z) v t
end YM.CF.Organdy
