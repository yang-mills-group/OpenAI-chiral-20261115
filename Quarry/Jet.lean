import Zephyr.Chern.Tile
import Quarry.Bra

/-! # Quantified error on quadratic coefficient from truncation

For the actual Trunks priced in Nest. Not a per-entry error paid for every matter or
link seat in the body : these grow at unbounded volume at any height. Work with the
full trace using the *total* rooted Soak, thus pay only at the short-work (of the
long exponentially priced pieces) angular scale. -/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 560000
noncomputable section
namespace Zephyr.Chern
open YM YM.Lattice YM.CF Tulip Cube Lat Tenant Drapes Branch
open Swell Filter Topology Fock
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Finset
variable {N : Side}
local notation "Ω" => Single N
variable {a b d B W : ℝ} {X : Oil N} {o : Site (More N)} {A : StemA N}

/-- Extension object; only in germs on Openc. -/
noncomputable def displayK (F : Raw (Openc (More N) d) (Single N)) : Oil N :=
  fun x => if h:x∈Openc (More N) d then F ⟨x,h⟩ else 0
lemma displayK_on (F : Raw (Openc (More N) d) (Single N))(x : Openc (More N) d) :
    displayK F x.val=F x := dif_pos x.property

/-- The whole trace at any whitelisted location: no sum over an unrelated volume. -/
def turn (X : Oil N)(A : StemA N)(x : ℝ) : ℂ := (X (profile (petals A x))).trace

theorem soak_sole (h : Soak o X a b d) : Solo a b X d := by
  obtain ⟨F,C,P,H,w,K⟩ := h; exact ⟨F,C,P,tally_F (fun S=>(P S).nonn) w,K⟩
lemma turn_sol (h : Solo a b X d) (u : 0<d) (A : StemA N) :
    Bloom (turn X A) (∑ i:Single N, wad X A i i) := Bloom.sum _ fun _ _ => (solo_bud h u).bloom

/-- Variant of band_buds, grow by distance to *anchor*! -/
theorem atAnchor {S : Band N} {C : Toll (Single N)} (w : Oily a d B W) (p : Piece d S C X)
    (v : Temper o A B) (i j : Single N) (L : C i j ≠ 0 → o ∈ S) (k : Fin 3) :
    ‖wad X A i j k‖ ≤ W * (rent a S * C i j) := by
  by_cases g : C i j=0
  · simp [wad,(kernel_free p g w.s.ready A).bud_eq,g]
  obtain ⟨l,r,e⟩ := ((p.expo ..).triggered g)
  let dℓ : ℝ := B*(1+S.card)
  have e(x:Edge (Site (More N)))(p:x∈leaks S) : |A x| ≤ dℓ := (v.grow x).trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (by exact_mod_cast (l.lim x.1 (mem_filter.mp p).2.left o (L g)).le) _)
    (zero_le_one.trans v.above))
  have h : 1 ≤ dℓ := one_le_mul_of_one_le_of_one_le v.above (by simp)
  have hz : 0 ≤ C i j := p.nonn i j
  refine ((kernel_jet p w.s h e).2 k).trans ?_
  calc
    _ ≤ (W * Real.exp (a/2*S.card))*C i j := mul_le_mul_of_nonneg_right (w.q S.card) hz
    _ ≤ W * rent a S * C i j := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (rent_up (half_le_self w.hb.le) _) w.bound.le) hz
    _ = _ := mul_assoc ..

lemma turn_bound (h : Soak o X a b d) (p : Temper o A B) (w : Oily a d B W) (k : Fin 3) :
    ‖bud (turn X A) k‖ ≤ W*b := by
  obtain ⟨F,C,H,Y,Q,t⟩ := h
  let V(S:Band N) := displayK (F S)
  have hv (S:Band N) : Piece d S (C S) (V S) := by
    unfold Piece
    rw [show (fun x:Openc (More N) d=>V S x.val)=F S from funext (displayK_on _)]
    exact H S
  let T : Bough d a b X := ⟨V,C,hv,tally_F (fun S=>(H S).nonn) Q,fun x u=>
    (t ⟨x,u⟩).trans (sum_congr rfl fun S _ => Eq.symm (displayK_on (F S) ⟨x,u⟩))⟩
  have he (i:Ω) : wad X A i i k = ∑ S:Band N, wad (V S) A i i k := by
    rw [wad,(T.drip_sum A i i w.s.ready).bud_eq, Finset.sum_apply]
  rw [(turn_sol T.solo w.s.ready A).bud_eq, Finset.sum_apply]
  simp_rw [he]; rw [sum_comm]
  apply (norm_sum_le ..).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left Q w.bound.le); rw [mul_sum]; apply sum_le_sum; intro S _
  apply (norm_sum_le ..).trans; unfold ledgerV; simp_rw [mul_sum]; apply sum_le_sum; intro i _
  apply (atAnchor w (hv S) p i i (fun g => ?_) k).trans; swap
  · by_contra u; apply g; rw [Y S u]; rfl
  exact single_le_sum (f:=fun j:Ω => W*(rent a S * C S i j)) (fun i _ => mul_nonneg w.bound.le
    (mul_nonneg (rent_pos ..).le ((H S).nonn _ _))) (mem_univ _)

open Skye Scree RG
open scoped ContDiff
variable {K : Loom N} {q:ℕ} {t : ℝ} (R : BudgetPoint) (A : StemA N)
variable (x : Site N)

/-- Germ of the **actual masked scalar**. Only near identity, not a uniform t-neighborhood. -/
theorem germ_turn (X : SOp N) (L : Roof N t d q K) (hp : R.threshold ≤ t) :
    (topChip R K x X ∘ petals A)=ᶠ[𝓝 0] turn X A := by
  have p : ∀ᶠ z:ℝ in 𝓝 0,pingS R.threshold univ (petals A z) :=
    (cont_petal A).continuousAt.eventually (ping_o.mem_nhds (show pingS R.threshold univ (petals A 0) from petal_idle A ▸ ping_f R _))
  filter_upwards [p] with i pi
  let v := petals A i
  let σ := offsetMask R.B x
  have h : pingS R.threshold σ v := Vow.grow_b (subset_univ _) pi
  unfold topChip turn hatKernel; simp only [Function.comp_apply]
  rw [Set.indicator_of_mem (show _ ∈ _ from h)]
  suffices l : ∀ k:Ids N, K (v,k)=v by change Matrix.trace (X (profile (K (v,_))))= _; rw [l]
  intro k; funext j; apply L.lamp
  -- Health on WHOLE torus at p, hence also at t
  have he : pingS t univ v := fun i l => (pi i l).trans_le hp
  exact ((ping_le he : Disjoint Finset.univ (flags t v)).symm).mono_right (subset_univ _)
end Zephyr.Chern
