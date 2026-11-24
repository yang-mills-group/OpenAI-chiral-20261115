import SatinStress.U3.Units
import SatinStress.U2.WickShapes

/-!
# Transfer and weak stress identification

Specialize U2/U3 transfer to the *Satin class calculations* (one gauge and two species
f and two mixed), c-real forms. Use of this for the field hierarchy awaits Q/R and Wick estimates
on the actual couplings. At present this is an implication, not an assertion of a system paying
its hypotheses. In particular for `ThetaBill` must compute even the annular prices and their
powers of ε, obtaining sector translations with exactly these normalizations (free offsets (97);
proofs so far are of the class calculus, not yet free `charges`).

Returns EXACT rank & left unit, INCLUDING the normalized component in the actual system
if it pays these hypotheses; no assertion of absence of passive sectors yet nor that the
unit acts on every local field as physical translations. The nondegeneracy and `payable`
conclusions apply to translations on supplies only.
-/
namespace SatinStress.U3.Weak
open U2 Shape ChainData Filter Function Coord Asymptote
open scoped Topology BigOperators

noncomputable section
local notation "ℭ" => Shape.chain ℝ
local notation "T₀" => TT0 ℝ
local notation "V₀" => VV ℝ
local notation "W₀" => WW ℝ

abbrev coordinates := (normalized ℝ).symm

/-- The **derivative action on sectors** with the exact Wick `J` coordinates (97).
    Here only on T's in the conserved space. -/
def penny (x : (ℭ).supply) : (ℭ).supply →ₗ[ℝ] (ℭ).supply :=
  (normalized ℝ).toLinearMap.comp ((LinearMap.mul ℝ _ (coordinates x)).comp (coordinates.toLinearMap))
lemma lifted (x y) : coordinates (penny x y)=coordinates x*coordinates y := by
  unfold penny; simp [coordinates]

def money : Left (ℭ).supply where
  toFun := penny
  map_add' x y := by ext1 z; apply coordinates.injective; simp [lifted,add_mul]  -- simp expansion
  map_smul' c x := by ext1 z; apply coordinates.injective; simp [lifted]

def joint : (ℭ).Insertion where
  theta := {
    toFun x := (ℭ).grad.comp ((ℭ).supply.subtype.comp (money x))
    map_add' x y := by ext1; simp
    map_smul' c x := by ext1; simp }
  closed x y := by
    simp only [LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk, Submodule.subtype_apply];
    have hh := (full ℝ).close ((money x y).val)
    rwa [previous_apply, show (ℭ).divg (money x y).val = 0 from (money x y).property] at hh
lemma joint_design (x y : (ℭ).supply) : joint.product (full ℝ) x y=money x y :=
  Subtype.ext ((full ℝ).injective_grad (joint.design (full ℝ) x y))
lemma pays (x y : (ℭ).supply) : coordinates (joint.product (full ℝ) x y) = coordinates x*coordinates y := by
  rw [joint_design]; exact lifted x y
-- checked `b` will require matching Θ at all these prices; avoids any arbitrary-product
-- hypothesis not identifying these normalizations.

variable {U V W Z J Y : Type*}
  [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  (C : ChainData ℝ U V W Z) (r : Scaling T₀ V₀ W₀ U V W ℕ atTop)
  (G : J → EndCost →ₗ[ℝ] ℝ) (F : ℕ → J → Z →ₗ[ℝ] ℝ)
variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  (t : CanCompare ℭ C r G F) (w : C.Closed)

include t
/- (95) after all internal species. This rank doesn't even need the closure W→Z in this step. -/
omit [FiniteDimensional ℝ V] in -- yes
lemma bound : 1 ≤ Module.finrank ℝ C.supply ∧ Module.finrank ℝ C.supply ≤ 3 := by
  obtain ⟨a,b⟩ := conservation_compare t
  rw [rankD, dim_supply,dim_W] at a
  rw [dim_supply] at b
  omega

include w
-- complete exactness in scale test coordinates
omit [FiniteDimensional ℝ U] in
lemma chain_full : C.Full := exact_at (full ℝ) t w

variable {G F} (P : C.Insertion) (a : P.Interchange Y) (b : ThetaBill r P joint)

/-- Main linear-stage result. "Active" here means potential active subset, extracted in
    these frames of the limit hierarchy. On these very hypotheses get the
    candidate generator in the same C, not a limiting-theory substitute for it.

    Scale convergence uses *nonzero fixed unit E on C*. Its coefficients under the displacement
    `r.left` with EPS^4 converge to unit indicator in the limiting frames, retaining which sectors
    are active at least in that comparison. To go further need the angular/lift and true-index
    assertions U4--5. -/
structure Paid (h : C.Full) (E : C.supply) (B : Asymptote C ℭ r) (x : C.supply) : Prop where
  unit : Left.IsUnit (P.product h) E
  unique (e : C.supply) : Left.IsUnit (P.product h) e → e=E
  nonzero : E ≠ 0
  component : B.address coordinates x = Indicator.unit (B.area coordinates)
  present : ∃ i, Indicator.lives (B.area coordinates) i
  payable (t : C.supply) : P.theta E t = C.grad t.val
  -- wick estimate
  mixing : Tends atTop (fun i =>
    WickVisit C r (B.route i) (((r.scale (B.route i))^4) • E)) (B.frame x).val

include w t a b -- needed

-- Use the SAME h for both stages
set_option maxHeartbeats 1200000 in
theorem linear_authority : ∃ (h : C.Full) (E : C.supply) (B : Asymptote C ℭ r) (x : C.supply),
    Paid C r P h E B x ∧ 1 ≤ Module.finrank ℝ C.supply ∧ Module.finrank ℝ C.supply ≤ 3 := by
  let h := chain_full C r G F t w
  obtain ⟨B⟩ := procure t.divgs
  have hr := bound C r G F t
  have hn : Nontrivial C.supply := Module.nontrivial_of_finrank_pos (R:=ℝ) (M:=↥C.supply) hr.1
  obtain ⟨x,E,hx,he,hy,ht⟩ := B.authorized h t.grads b pays a -- hx give implicit? compile
  refine ⟨h,E,B,x,⟨he,hy,?_,hx,B.active_exists hn, fun y => ?_,ht⟩,hr⟩
  · intro H
    obtain ⟨y,t⟩ := exists_ne (0:C.supply)
    exact t (by simpa [H] using (he y).symm)
  · rw [← P.design h,he]
end
end SatinStress.U3.Weak
