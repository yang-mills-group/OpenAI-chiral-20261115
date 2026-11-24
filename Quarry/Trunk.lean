import YM.SU5.Exchange.Pipe.Latch

/-! # Truncated kernel transport (on the complex Openc; before any Loom tests)

Carry the actual **short** representation of a Trunk when applying the sweep to move
it to a pose of the current. Retain exactly the rates and the length cutoff. Extends
Swell.jul_sells. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet
open Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire

variable {N : Side} {X : SOp N} {o : Seat N} {a b d : ℝ} {m : ℕ}
local notation "Ω" => Single N

/-- Version of `arm_v` retaining a card cutoff. -/
theorem armTrunk {ι : Type*} [Fintype ι] (F : ι → Sa N)
    (K : ι → Raw (↥(Openc (Cube.More N) d)) (Single N)) (V : ι → Toll (Single N))
    (h : ∀ i, Suite (badge _) (bail N d) (bail N d) (F i) (V i) (K i))
    (p : (∑ i, rent a (F i) * ledgerV (V i)) ≤ b)
    (u : ∀ i, V i ≠ 0 → o ∈ F i ∧ (F i).card < m)
    (g : ∀ i : Openc (Cube.More N) d, X i.val = ∑ j : ι, K j i) :
    Trunk o X m a b d := by
  refine ⟨arm_v F K V h p (fun i g => ?_) g, ?_⟩
  · exact Classical.not_not.mp fun v => g (u i v).1
  let Kc (S : Sa N) : Toll Ω := fun i j => ∑ y∈dest F S, V y i j
  refine ⟨_, Kc, fun S =>
    ⟨Ticket.sumT _ V K (fun i (v : i ∈ dest F S) => (mem_filter.mp v).2 ▸ (h i).toTicket),
      License.suppose _ _ _ (fun i _ => (h i).fuel)⟩, fun S x => ?_, le_trans ?_ p,
        fun i => Eq.trans (g i) (lump F _)⟩
  · by_contra s
    apply x; funext i j; exact sum_eq_zero fun k v => by
      have w := (mem_filter.mp v).2
      have vk : V k = 0 := Classical.not_not.mp fun t => s (w ▸ u k t)
      rw [vk]; rfl
  refine le_of_eq ?_
  rw [Branch.lump F]
  refine sum_congr rfl (fun i _ => ?_)
  unfold ledgerV Kc
  simp_rw [sum_comm (t:=dest F i) (s:=(univ:Finset Ω))]
  rw [mul_sum]
  exact sum_congr rfl (fun j u => by rw [show F j=i from (mem_filter.mp u).2])

/-- The pose prescription works for masked stencils too (complex profile step). -/
theorem Trunk.pose (s : Sweep N) (p : Trunk o X m a b d) :
    Trunk ((boxA s) o) (julStep s X) m a (Tenant.quota ^ 2 * b) d := by
  obtain ⟨F,W,v,l,u,k⟩ := p.home
  let Q := actY s⁻¹
  let A := noteU s⁻¹
  let V(T) := Mx s d (F T)
  let B(T) : Toll Ω := A (W T)
  let D := Tenant.quota
  have hx : 0 ≤ D := le_trans (by norm_num : (0:ℝ) ≤ 16) quota_bound
  refine armTrunk Q V B (fun i => mini _ _ _ _ (v i)) ?_ ?_ ?_
  · -- same charge as `jul_sells`
    apply le_trans _ (mul_le_mul_of_nonneg_left u (sq_nonneg D))
    rw [mul_sum]; apply sum_le_sum; intro i _
    rw [Branch.rent, show (Q i).card=i.card from card_map .., mul_left_comm]
    apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    unfold B A noteU ledgerV; simp_rw [normU,mul_sum]
    let L(x y j k : Ω) := jLL s⁻¹ x j * jLL s⁻¹ y k * W i j k
    change ∑ x:Ω,∑ y:Ω,∑ j:Ω,∑ k:Ω,L x y j k ≤ _
    simp_rw [sum_comm (f:=fun y (j:Ω) => ∑ k:Ω,L _ y j k)]
    rw [sum_comm]; apply sum_le_sum; intro j _
    simp_rw [sum_comm (f:=fun y k => L _ y j k)]; rw [sum_comm]
    apply sum_le_sum; intro k _
    unfold L; simp_rw [←Finset.sum_mul,←Finset.mul_sum]; rw [←Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ ((v i).nonn _ _)
    exact (mul_le_mul (ρ_K ..) (ρ_K ..) (sum_nonneg fun t _=>norm_nonneg _) hx).trans_eq (by ring)
  · intro i g
    have H : W i ≠ 0 := by
      intro h; apply g; unfold B A noteU; rw [h]; ext; simp
    obtain ⟨H,H'⟩ := l i H
    exact ⟨by simpa [Q,actY,sitU] using H, lt_of_eq_of_lt (card_map ..) H'⟩
  intro x; let z := Sour.fog s d x
  change ech s⁻¹ (X z.val) = _
  rw [k z]; unfold ech; rw [singT,win_sum,map_sum]; rfl

end YM.CF.Swell
