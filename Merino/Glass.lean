import Merino.Cabinet
import Zephyr.Chern.Amber
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

variable {o:Site (More n)} {F:Oil n} {a b e B W:ℝ} {A:StemA n}

/-- trace response along angles. -/
def glaze (A:StemA n)(F:Oil n)(x:ℝ) : ℂ :=
    (F (profile (petals A x))).trace

/- The centered-temperate version of band_buds, not using
that the entries touch the center. -/

lemma traced (w:Oily a e B W)(t:Temper o A B)
    {S:Band n}{C:Toll (Single n)}
    (p:Piece e S C F)(r:o ∉ S→ C=0)(i j:Single n)(k:Fin 3):
    ‖wad F A i j k‖ ≤ W*(rent a S * C i j) := by
  by_cases u:C i j=0
  · simp [wad,(kernel_free p u w.s.ready A).bud_eq,u]
  have l:= t.above
  have a1:1≤B*(1+(S.card:ℝ)):=one_le_mul_of_one_le_of_one_le l (by simp)
  have h:o∈S:=by by_contra v; rw [r v] at u; exact u rfl
  obtain ⟨g,_,_⟩:= (p.expo i j).triggered u
  have e':∀ x∈leaks S, |A x|≤B*(1+(S.card:ℝ)) := fun x hx=>
    have ht := g.lim x.1 (mem_filter.mp hx).2.1 o h
    (t.grow x).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add_right (by exact_mod_cast ht.le) _)
        (zero_le_one.trans l))
  refine ((kernel_jet p w.s a1 e').2 k).trans ?_
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (p.nonn i j)
  refine (w.q S.card).trans (mul_le_mul_of_nonneg_left ?_ w.bound.le)
  rw [Branch.rent,Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_right (half_le_self w.hb.le) (Nat.cast_nonneg _)
lemma soak_glaze (u:Soak o F a b e)
    (w:Oily a e B W)(t:Temper o A B):
    Bud (glaze A F) ∧ ∀ k:Fin 3, ‖bud (glaze A F) k‖ ≤ W*b:=by
  obtain ⟨G,C,h,x,l,y⟩:=u
  let H:Band n→Oil n:= fun S x=> if hx:x∈Openc _ e then G S ⟨x,hx⟩ else 0
  have hu(S) : G S= fun x=> H S x.val:=funext fun x=> by simp [H,x.property]
  have hp(S) : Piece e S (C S) (H S):=by have p:=h S; rw [hu S] at p;exact p
  let D(S):=fun i:Single n=> wad (H S) A i i
  have hb:Bloom (glaze A F) (∑ S:Band n,∑ i:Single n,D S i):=by
    let P:Band n→ℝ→ℂ:=fun S x=> ∑ i:Single n,drip (H S) A i i x
    apply (Bloom.sum (u:=P) univ (v:=fun S=>∑ i:Single n,D S i) ?_).congr
    · filter_upwards [petals_open w.s.ready A] with v hv
      change (F (profile (petals A v))).trace=_
      rw [y ⟨_,hv⟩,Matrix.trace_sum]
      refine sum_congr rfl fun S _=>?_ 
      rw [hu S]
      rfl
    exact fun S _=> Bloom.sum univ fun i _=> (kernel_bud (hp S) w.s.ready).bloom
  refine ⟨hb.1,fun k=>?_⟩
  rw [hb.bud_eq]
  simp only [Finset.sum_apply]

  refine le_trans (norm_sum_le ..) (le_trans ?_ (mul_le_mul_of_nonneg_left l w.bound.le))
  rw [mul_sum]
  refine sum_le_sum fun S _=> ?_
  refine le_trans ((norm_sum_le ..).trans (sum_le_sum fun i _=> traced w t (hp S) (x S) i i k)) ?_
  simp_rw [ledgerV,mul_sum]
  refine sum_le_sum fun i _=>single_le_sum (f:=fun j=>W*(Branch.rent a S * C S i j))
    (fun j _=>mul_nonneg w.bound.le (mul_nonneg (rent_pos _ _).le ((h S).nonn i j)))
    (mem_univ i)
end YM.CF.Merino
