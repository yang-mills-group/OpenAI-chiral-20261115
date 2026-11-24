import SatinStress.U2.Packing
import SatinStress.U2.BlockBasis
import SatinStress.U3.ActiveUnit
/-!
# Weak comparison of the product and asymptotic frames (98), (99)

Use arbitrary monotone subsequences of the **same testing-height f**. A rotation
proof may again require passing to a further one, so keep all the coordinates
priceable. These are the finite-dimensional weak analysis proofs from the indicated
comparison on θ-prices. The hypothesis `ThetaBill` will call for position tests with
full scaling & annular support and matrix estimates in actual Wick-comparison frames;
at this point it remains a hypothesis. Here we prove, in particular, the product
estimate in (99), construction/closure of the limiting sub*space*, and convergence
of the product matrices in its chart. Need no algebra on the whole rank-3 shell of
the interacting phase.
-/
namespace SatinStress.U3
open U2 Filter Function ChainData Coord
open scoped Topology BigOperators

variable {T T' W W' V V' Z Z' J Y : Type*}
  [AddCommGroup T] [Module ℝ T] [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup T'] [Module ℝ T'] [AddCommGroup W'] [Module ℝ W'] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup Z'] [Module ℝ Z']

variable {A : ChainData ℝ T' V' W' Z'} {C : ChainData ℝ T V W Z}
variable (s : Scaling T V W T' V' W' ℕ atTop)
noncomputable def power (i : ℕ) := (s.scale i ^ 4)⁻¹
lemma power_pos (i) : 0 < power s i := inv_pos.mpr (pow_pos (s.positive i) _)

variable (A) in
/-- At the testing scale i, F^{-1} applied to the real conserved space. -/
noncomputable def WickVisit (i : ℕ) : A.supply →ₗ[ℝ] T := (s.left i).symm.toLinearMap.comp A.supply.subtype
-- price authority separately for θ. Kernels/equivariant frames etc. will be needed to feed it.
variable (P : A.Insertion) (Q : C.Insertion)
def ThetaBill := ∀ c : ℕ → ℕ, StrictMono c →
  ∀ x y : ℕ → A.supply, ∀ u v : C.supply,
    Tends atTop (fun i => WickVisit A s (c i) (x i)) u.val →
    Tends atTop (fun i => WickVisit A s (c i) (y i)) v.val →
    Tends atTop (fun i => s.scale (c i) •
      (s.middle (c i)).symm (P.theta (power s (c i) • x i) (y i))) (Q.theta u v)

variable (H : A.Full) (HX : C.Full)

lemma derivative_bill (j : ℕ) (a b : A.supply) :
    Scaling.hereGrad A s j (WickVisit A s j (power s j • P.product H a b)) =
        s.scale j • (s.middle j).symm (P.theta (power s j • a) b) := by
  -- transfer proof on gradient of product, not assuming left-unit or even that
  -- transformed product has a finite norm bound.
  rw [Scaling.hereGrad_apply]
  have e : s.left j (WickVisit A s j (power s j • P.product H a b)) = (P.product H (power s j • a) b).val := by
    simp [WickVisit]
  rw [e,P.design]

variable {P Q s}

section
variable [FiniteDimensional ℝ T] [FiniteDimensional ℝ V]
lemma attenuation (hg : Entries atTop (Scaling.hereGrad A s) C.grad) (b : ThetaBill s P Q)
    {c : ℕ → ℕ} (t : StrictMono c)
    (x y : ℕ → A.supply) (u v : C.supply)
    (p : Tends atTop (fun i => WickVisit A s (c i) (x i)) u.val)
    (q : Tends atTop (fun i => WickVisit A s (c i) (y i)) v.val) :
    Tends atTop (fun i => WickVisit A s (c i) (power s (c i) • P.product H (x i) (y i)))
      ((Q.product HX u v).val) := by
  apply recover (A:=Scaling.hereGrad A s ∘ c) (fun z => (hg z).comp t.tendsto_atTop) _ HX.injective_grad
  simp only [comp_apply,derivative_bill,Q.design]; exact b c t x y u v p q
end

-- Grassmannian. fixed type A.supply serves for basis: M sends it to C.supply.
variable (C A s) in
/-- Here the RHS of (98) is `(S.frame).range`. `route` already applied to the chosen heights.
Each `change` is an honest automorphism of **actual** supply, giving choices
of basis there before using e.g. (99) and $F^{-1}$. -/
structure Asymptote where
  route : ℕ → ℕ
  rising : StrictMono route
  change (j : ℕ) : A.supply ≃ₗ[ℝ] A.supply
  frame : A.supply →ₗ[ℝ] C.supply
  injective : Injective frame
  convergence : Entries atTop
    (fun j => WickVisit A s (route j) ∘ₗ (change j).toLinearMap) (C.supply.subtype.comp frame)

section
variable [FiniteDimensional ℝ T] [FiniteDimensional ℝ W]
lemma procure [FiniteDimensional ℝ T'] (hd : Entries atTop (Scaling.hereDiv A s) C.divg) : Nonempty (Asymptote A C s) := by
  obtain ⟨c,hc,g,M,hM,u⟩ := clipped (WickVisit A s) (fun j => (s.left j).symm.injective.comp Subtype.val_injective)
  have hs (x) : M x ∈ C.supply := by
    apply LinearMap.mem_ker.mpr
    have he : Tends atTop (fun _ : ℕ => 0) (C.divg (M x)) := by
      have hE : Entries atTop ((Scaling.hereDiv A s) ∘ c) C.divg := fun x => (hd x).comp hc.tendsto_atTop
      apply (hE.evolve (u x)).congr' ?_
      exact Eventually.of_forall (fun i => by simp only [comp_apply,Scaling.hereDiv_apply,WickVisit,LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply,LinearEquiv.apply_symm_apply]; simp)
    exact limit_unique he stationary
  exact ⟨⟨c,hc,g,M.codRestrict C.supply hs, (fun x y e => hM (congr_arg Subtype.val e)), u⟩⟩
end

namespace Asymptote
variable (B : Asymptote A C s)

noncomputable def tune (i : ℕ) := (power s (B.route i))
variable (P) in
noncomputable def cost (i : ℕ) : Left A.supply :=
  let e := B.change i
  { toFun x := B.tune i • (e.symm.toLinearMap.comp ((P.product H (e x)).comp e.toLinearMap))
    map_add' x y := by ext1; simp [smul_add]
    map_smul' c x := by ext1; simp [smul_comm (B.tune i) c] }
lemma cost_at (i : ℕ) (x y : A.supply) : B.cost P H i x y = B.tune i •
    (B.change i).symm (P.product H (B.change i x) (B.change i y)) := rfl

-- relation useful to descend left unit too
lemma price (i : ℕ) (x y : A.supply) : B.change i (B.cost P H i x y) =
    P.product H (B.tune i • B.change i x) (B.change i y) := by
  rw [B.cost_at]; simp

variable [AddCommGroup Y] [Module ℝ Y]
lemma commute (q : P.Interchange Y) (i : ℕ) (x y z : A.supply) : B.cost P H i x (B.cost P H i y z) = B.cost P H i y (B.cost P H i x z) := by
  apply (B.change i).injective; simp only [B.price, q.commutes H] -- simp perm lemma? perm sorting risk

variable [FiniteDimensional ℝ T] [FiniteDimensional ℝ V] [FiniteDimensional ℝ T']

/-- Transfer product, obtaining in one move both price convergence and exact subalgebra closure
in the limiting subspace. -/
theorem transferred (x y : A.supply) (hg : Entries atTop (Scaling.hereGrad A s) C.grad) (b : ThetaBill s P Q) :
    ∃ v : A.supply, B.frame v = Q.product HX (B.frame x) (B.frame y) ∧
      Tends atTop (fun i => B.cost P H i x y) v := by
  have e := attenuation H HX hg b B.rising (fun i=>B.change i x) (fun i=>B.change i y)
    (B.frame x) (B.frame y) (B.convergence x) (B.convergence y)
  have ht : Tends atTop (fun j => (WickVisit A s (B.route j) ∘ₗ (B.change j).toLinearMap)
        (B.cost P H j x y)) ((Q.product HX (B.frame x) (B.frame y)).val) := by
    apply e.congr' (Eventually.of_forall (fun j => ?_))
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,B.price,tune,map_smul,LinearMap.smul_apply]
  obtain ⟨v,t,h⟩ := recover_exists B.convergence ht (Subtype.val_injective.comp B.injective)
  exact ⟨v,Subtype.ext h,t⟩

variable {H HX} (hg : Entries atTop (Scaling.hereGrad A s) C.grad) (b : ThetaBill s P Q)

-- small support, but even if W division rank jumps we can price it via convergence
-- of bases -- not substituting a fixed normalization identifying all three tensors already.
variable (H HX)
noncomputable def target (x y) := (B.transferred H HX x y hg b).choose
lemma target_reached (x y) : B.frame (B.target H HX hg b x y)=Q.product HX (B.frame x) (B.frame y) :=
  (B.transferred H HX x y hg b).choose_spec.1
lemma converges (x y) : Tends atTop (fun i => B.cost P H i x y) (B.target H HX hg b x y) :=
  (B.transferred H HX x y hg b).choose_spec.2

noncomputable def waitLeft (x : A.supply) : A.supply →ₗ[ℝ] A.supply where
  toFun y := B.target H HX hg b x y
  map_add' x y := by apply B.injective; simp [target_reached]
  map_smul' c x := by apply B.injective; simp [target_reached]
noncomputable def limitCost : Left A.supply where
  toFun := B.waitLeft H HX hg b
  map_add' x y := by
    ext1 z
    change B.target H HX hg b _ z = B.target H HX hg b x z + B.target H HX hg b y z
    apply B.injective; simp [target_reached]
  map_smul' c x := by
    ext1 z
    change B.target H HX hg b _ z = c • B.target H HX hg b x z
    apply B.injective; simp [target_reached]
lemma represented (x y : A.supply) :
    B.frame (B.limitCost H HX hg b x y)=Q.product HX (B.frame x) (B.frame y) := B.target_reached H HX hg b x y
end Asymptote
end SatinStress.U3
