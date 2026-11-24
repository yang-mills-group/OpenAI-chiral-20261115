import GaugeFieldConstruction.Floats

/-! # The C-clover and matter-current selection rule: tensors

In the prescribed gauge convention of Interaction/N5, the C sector is a two-dimensional
hypercube sector. Positivity of its own two-point/spacetime experiment does not warrant a
nonzero *cross* experiment with a current. In particular this price transforms as spin 2
at axis separation; more than that, the SO(4)-orbit of the clover is contained in spins 2
at axis separation. We will work in a sum of SD-SD and ASD-ASD traceless symmetric tensor
slots. All calculations here on the actual GaugeFieldConstruction label spaces (where on-shell
identifications apply and labels need not be independent on input).

This file: allow the six spin coordinates of the orbit, and show how `enlarged` charges
GE as four tensor factors. Also record the action of the hypercube group for later
restrictions to the projector and spatial cube.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000

noncomputable section
namespace YM.GaugeFieldConstruction.Stage.CloverSymmetry
open Calibration Calibration.RawBank Floor Cauchy Row Phys Function Set Filter Finset Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology Matrix Matrix.Norms.Frobenius
open Angles
attribute [local instance] Stage.iA Stage.iG Stage.iX

/-- The gauge summand injection into degree 4. -/
def gin : UG four →ₗ[ℂ] UV four := LinearMap.inr ℂ _ _ ∘ₗ LinearMap.inl ℂ _ _

lemma ginSpin (s : Signed) (v) : spinFrame four s (gin v) = gin ((gauge four).moves s v) := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · exact funext fun _ => map_zero ((matter four).moves s)
  exact funext fun _ => map_zero ((mixed four).moves s)

lemma ginJ (B : Rotors) (v) : enlarged All four B (gin v) = gin (YG four B v) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rw [ruleG]
    exact one_smul ℂ _
  apply Prod.ext
  · ext1 b
    rw [ruleF]
    exact map_zero (EF (d:=four) All B _)
  ext1 b
  rw [ruleX]
  exact map_zero (EX (d:=four) All B _)

/-- Spin-ink `F_ab F_cd` without needing to pay blade sorting. -/
def ink (a b c d : Axis) : UG four := (DeckG four).issue (ket ((a,b), (c,d)))

lemma inkValue (a b c d : Axis) : (ink a b c d).val = Bose (F a b) (F c d) := Mint.paid_at ..

def ff (a b c d : Axis) : UV four := gin (ink a b c d)

@[simp] lemma leftDiag (a b c) : ff a a b c = 0 := by
  have h : ink a a b c = 0 := Subtype.ext (by rw [inkValue]; change Bose _ _ = 0; rw [U1.Gauge97.zero_angle]; simp [Bose])
  rw [ff,h,map_zero]
lemma pairExchange (a b c d) : ff a b c d = ff c d a b := by
  apply congrArg gin
  apply Subtype.ext
  rw [inkValue, inkValue, bose_swap]
@[simp] lemma rightDiag (a b c) : ff a b c c = 0 := by rw [pairExchange,leftDiag]
lemma leftSkew (a b c d) : ff a b c d = -ff b a c d := by
  rw [ff, ff, ← map_neg]
  apply congrArg gin
  apply Subtype.ext
  change _ = -(ink b a c d).val
  rw [inkValue, inkValue, U1.Gauge97.turnover a b]; simp only [Bose,map_neg,LinearMap.neg_apply,neg_add]
lemma rightSkew (a b c d) : ff a b c d = -ff a b d c := by
  rw [pairExchange a b c d,pairExchange a b d c,leftSkew c d a b]

lemma ffMotion (p : Signed) (a b c d : Axis) : spinFrame four p (ff a b c d) =
    pay (((p.flip a).xor (p.flip b)).xor ((p.flip c).xor (p.flip d))) (ff (p.perm a) (p.perm b) (p.perm c) (p.perm d)) := by
  let z : BoxG four := ((a,b), (c,d)); let D:= DeckG four
  change spinFrame four p (gin (D.issue (ket z))) = _
  rw [ginSpin, ← show D.issue (beacon D.label p (ket z)) = _ from Mint.respect D (gauge four).toCarries p _]
  unfold Cell.beacon
  rw [on_ket]
  change gin (D.issue (pay _ _)) = pay (D.label.cost p z) (gin (D.issue _))
  cases D.label.cost p z <;> simp only [pay_true,pay_false,map_neg]
  all_goals rfl

lemma ffCharge (r : Rotors) (a b c d : Axis) :
    enlarged All four r (ff a b c d) =
    ((∑ i:Axis, (r.val i a:ℂ) • ff i b c d) + ∑ i:Axis, (r.val i b:ℂ) • ff a i c d) +
    ((∑ i:Axis, (r.val i c:ℂ) • ff a b i d) + ∑ i:Axis, (r.val i d:ℂ) • ff a b c i) := by
  suffices H : YG four r (ink a b c d) =
    ((∑ i:Axis, (r.val i a:ℂ) • ink i b c d) + ∑ i:Axis, (r.val i b:ℂ) • ink a i c d) +
    ((∑ i:Axis, (r.val i c:ℂ) • ink a b i d) + ∑ i:Axis, (r.val i d:ℂ) • ink a b c i) by
    simp only [ff,ginJ,H,map_add,map_sum,map_smul]
  rw [show YG four r (ink a b c d) = _ from visitG four r (ket ((a,b),(c,d)))]
  apply Subtype.ext
  change jet page (PG.beta r (ket _)) = _
  rw [PG,fork_cost,Theta,fork_cost,fork_cost,motion,motion,motion,motion]
  simp only [AddSubgroup.coe_add, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower, inkValue]
  rfl

/-! ## Get actual action on a submodule, not just its index tables -/
lemma rotationMem (V : Submodule ℂ (UV four))
    (hV : ∀ B x, x∈ V → enlarged All four B x ∈ V) (s : SO) (x : UV four) (hx : x ∈ V) : ledger All four s x ∈ V := by
  let good (s : SO) := ∀ x : UV four, x ∈ V → ledger All four s x ∈ V
  have gen (B : Rotors) (t : ℝ) : good (rise B t) := by
    intro x hx
    let f (t : ℝ) := ledger All four (rise B t) x
    let A := enlarged All four B
    let Q := V.mapQ V A (show V ≤ V.comap A from @fun x hx => hV B x hx)
    have z (t : ℝ) : Sends (V.mkQ ∘ f) t (Q (V.mkQ (f t))) := by
      rw [show Q (V.mkQ (f t)) = V.mkQ (A (f t)) from Submodule.mapQ_apply ..]
      exact posts (Stage.cost All B (d:=four) x t) V.mkQ
    have h : V.mkQ (f 0) = 0 := by
      unfold f
      rw [show rise B 0 = 1 from Subtype.ext (YM.Work.A13.oneParameter_zero _), map_one,Module.End.one_apply]
      exact (Submodule.Quotient.mk_eq_zero V).mpr hx
    apply (Submodule.Quotient.mk_eq_zero V).mp
    exact congrFun (confined (V.mkQ ∘ f) z h) t
  have mul (s t : SO) (a : good s) (b : good t) : good (s*t) := by
    intro x u; rw [map_mul,Module.End.mul_apply]; exact a _ (b _ u)
  suffices w : good s ∧ good s⁻¹ from w.1 x hx
  refine SO_compute s (p:=fun s=> good s ∧ good s⁻¹) (fun B t=>⟨gen B t,?_⟩) ?_ ?_ (fun s h=>⟨h.2, (by simpa using h.1)⟩)
  · rw [show (rise B t)⁻¹ = rise B (-t) from Subtype.ext (param_inv B t)]
    exact gen B (-t)
  · simp [good]
  · rintro s t ⟨hs,hs'⟩ ⟨ht,ht'⟩; exact ⟨mul s t hs ht,(show good ((s*t)⁻¹) from by rw [_root_.mul_inv_rev]; exact mul _ _ ht' hs')⟩

end YM.GaugeFieldConstruction.Stage.CloverSymmetry
end
