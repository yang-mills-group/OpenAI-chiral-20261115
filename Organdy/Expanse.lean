import Organdy.Poly
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


open Leaf
abbrev massif (L:ℕ):= 12*(L+1)
abbrev worthRock (L:ℕ):= (massif L+massif L+1)^4
def rockG (L:ℕ) (p:BudgetPoint) (o:Seat n):Aura n:=
 ⟨halo (massif L*p.B) {o},o,halo_subset _ _ (mem_singleton_self o)⟩
lemma centreRock (L:ℕ)(p:BudgetPoint)(o:Seat n):o∈ (rockG L p o).val:=
 halo_subset _ _ (mem_singleton_self o)
lemma coverRock {L:ℕ}(hp:2*(massif L*p.B)≤(More n).val)(o:Seat n):
    L ≤ (coverNumber p.B (rockG L p o).val)^3:=by
  let R:=massif L*p.B; let x: Lattice.Cover:=fun _=>R
  let w:=wrap (More n) x
  have hl:Lattice.lift w=x:= lift_eq_iff.mpr ⟨rfl,fun i=>by
    have hw:(More n).val>0:=(More n).property
    unfold x R; omega⟩
  let j:=w+o
  have he:separation o j=R:=by
    rw [separation_comm,separation,show j-o=w from add_sub_cancel_right w o,pdist,hl]; simp [x] ; exact le_antisymm
      (Finset.sup_le fun _ _=> le_rfl) (Finset.le_sup (b:=(0:Axis)) (f:=fun i=>R) (mem_univ _))
  have hw : j∈ (rockG L p o).val:=halo_spec.mpr ⟨o,mem_singleton_self _,he.le⟩
  let k:=coverNumber p.B (rockG L p o).val
  have hx:=Corona.extent _ p.B (centreRock L p o) hw
  have h: L<k:=by
    by_contra! g
    rw [he] at hx
    have ht:4*p.B+2≤6*p.B:=by linarith [p.B_pos]
    have hR:12*(L+1)*p.B≤L*(6*p.B)+2*p.B:=hx.trans
      (Nat.add_le_add_right (Nat.mul_le_mul g ht) ..) -- add right
    nlinarith [p.B_pos]
  have ht:1≤k:=by omega
  exact h.le.trans (by simpa only [pow_one] using
    (Nat.pow_le_pow_right ht (show 1 ≤ 3 from by decide))) -- ht:k≥1? h only L<k

abbrev lashCrag (s:ℝ)(L:ℕ):ℝ:=Real.exp (s*worthRock L)
variable {L:ℕ}{o:Seat n}{s:ℝ}
local notation "mL" => rockG L p o
lemma tollCrag (t:0≤ s)(i:Aura n)(v:o∈i.val):
   tact s p.B (αK mL i) ≤ lashCrag s L*tact s p.B i:=by
  have hg:i∈Cadre.blaze mL:=mem_filter.mpr ⟨mem_univ _,
    fun r=>Finset.disjoint_left.mp r (centreRock L p o) v⟩ -- orientation inspect
  apply (tact_αK (k:=p.B) t hg).trans
  have hk:coverNumber p.B (rockG L p o).val ≤ worthRock L:=
    Corona.tile _ _ _ p.B_pos
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hk) t))
    (Real.exp_pos _).le

def expand (L:ℕ) (p:BudgetPoint) (o:Seat n)(f:Bag n):Bag n:=∑ i:Aura n,
  fun j:Aura n=> if j=αK (rockG L p o) i then f i else 0
lemma giveExpand (L:ℕ)(p:BudgetPoint)(o:Seat n)(f:Bag n):
    (∑ j:Aura n,expand L p o f j)=∑ i:Aura n,f i:=by
  unfold expand
  simp_rw [Finset.sum_apply]
  rw [sum_comm]
  simp

variable {B:Support (More n)} {V:Bag n}
lemma mast (r:0≤ s) (w:Barrage p q B h V s a b)(e:o∈B) :
    Barrage p q (mL).val h (expand L p o V) s (lashCrag s L*a) (lashCrag s L*b):=by
  obtain ⟨g,k,ticket,fare,ha,hb⟩:=w.price
  refine (Barrage.whole Finset.univ _
    (fun i=>g i*tact s p.B (αK mL i))
    (fun i=>k i*tact s p.B (αK mL i))
    (fun i _=>Barrage.single _ _ ((ticket i).mantle subset_union_right) subset_union_left)).bigR ?_ ?_
  · apply le_trans _ (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le)
    unfold voyageB; rw [mul_sum]
    refine sum_le_sum fun i _=>?_
    rw [mul_left_comm (lashCrag s L)]
    by_cases u:B⊆i.val
    · exact mul_le_mul_of_nonneg_left (tollCrag r i (u e)) (ticket i).tube.price
    rw [(fare i u).2.1,zero_mul,zero_mul]
  apply le_trans _ (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
  unfold voyageB; rw [mul_sum]
  refine sum_le_sum fun i _=>?_
  rw [mul_left_comm (lashCrag s L)]
  by_cases u:B⊆i.val
  · exact mul_le_mul_of_nonneg_left (tollCrag r i (u e)) (voucher (ticket i))
  rw [(fare i u).2.2,zero_mul,zero_mul]
end YM.CF.Organdy
