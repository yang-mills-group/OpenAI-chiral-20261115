import SatinStress.U3.Asymptote

namespace SatinStress.U3.Asymptote
open U2 Filter Function ChainData Coord
open scoped Topology BigOperators

variable {T T' W W' V V' Z Z' J Y : Type*}
  [AddCommGroup T] [Module ℝ T] [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup T'] [Module ℝ T'] [AddCommGroup W'] [Module ℝ W'] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup Z] [Module ℝ Z] [AddCommGroup Z'] [Module ℝ Z']
variable {A : ChainData ℝ T' V' W' Z'} {C : ChainData ℝ T V W Z} {s : Scaling T V W T' V' W' ℕ atTop}

variable {P : A.Insertion} {Q : C.Insertion}
variable (H : A.Full) (HX : C.Full)
variable (B : Asymptote A C s)
variable (give : C.supply ≃ₗ[ℝ] (Fin 3 → ℝ))

noncomputable section
/-- Asymptotic subspace, in the 3 concrete normalized coordinates. -/
def address := give.toLinearMap.comp B.frame
def area := LinearMap.range (B.address give)
lemma address_inj : Injective (B.address give) := give.injective.comp B.injective

variable [FiniteDimensional ℝ T] [FiniteDimensional ℝ V] [FiniteDimensional ℝ T']
variable (hg : Entries atTop (Scaling.hereGrad A s) C.grad) (b : ThetaBill s P Q)

variable {HX give} (rights : ∀ a c : C.supply, give (Q.product HX a c) = give a * give c)

include hg b rights H
lemma follows (x y : A.supply) :
    B.address give (B.limitCost H HX hg b x y) = B.address give x * B.address give y := by
  unfold address; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,
    B.represented H HX hg b x y,rights]
lemma made : Indicator.unit (B.area give) ∈ B.area give := by
  apply Indicator.made
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩; exact ⟨_,B.follows H hg b rights x y⟩
omit hg b H rights
omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ V] [FiniteDimensional ℝ T'] in
lemma active_exists (h : Nontrivial A.supply) : ∃ i, Indicator.lives (B.area give) i := by
  obtain ⟨x,hx⟩ := exists_ne (0:A.supply)
  exact Indicator.live (B.area give) ⟨x,rfl⟩ (fun he => hx (B.address_inj give (he.trans (map_zero _).symm)))
-- include give? implicit h infers via B
include H
omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ V] [FiniteDimensional ℝ T'] in
lemma unit_move (i : ℕ) (x : A.supply) : Left.IsUnit (B.cost P H i) x ↔
    Left.IsUnit (P.product H) (B.tune i • B.change i x) := by
  constructor
  · intro he y
    obtain ⟨y,rfl⟩ := (B.change i).surjective y; rw [← B.price, he]
  intro he y; apply (B.change i).injective; rw [B.price, he]

variable [AddCommGroup Y] [Module ℝ Y] (inter : P.Interchange Y)
include inter hg b rights

/-- Stability of the *left* unit via a cyclic vector. `power` multiplies
    the actor's normalization exactly as in (99). This version takes any of
    the convergent subspace frames B. Conclusions before using full field-space action.
    Use an injective `give` exactly on the free normalized labels. -/
theorem authorized : ∃ x E : A.supply,
    B.address give x = Indicator.unit (B.area give) ∧
    Left.IsUnit (P.product H) E ∧
    (∀ t, Left.IsUnit (P.product H) t → t=E) ∧
    Tends atTop (fun i => (WickVisit A s (B.route i) (((s.scale (B.route i))^4) • E))) (B.frame x).val := by
  obtain ⟨x,hx⟩ := B.made H hg b rights
  have he (y : A.supply) : B.limitCost H HX hg b y x=y := by
    apply B.address_inj give; rw [B.follows H hg b rights,hx,mul_comm]
    exact Indicator.unit_mul (B.area give) ⟨B.address give y,y,rfl⟩
  have hat : Entries atTop (fun i => (B.cost P H i).flip x) LinearMap.id := by
    intro y; change Tends atTop _ y
    -- target y only not all y's entering the seq
    convert! B.converges H HX hg b y x using 1
    exact (he y).symm
  have hy := Left.survive hat (fun i => B.commute H inter i) -- exists along this testing subseq
  obtain ⟨i,t,hi,hi'⟩ := hy.exists
  let E := B.tune i • B.change i t
  have hE : Left.IsUnit (P.product H) E := (B.unit_move H i t).mp hi
  let walk (j : ℕ) (v : A.supply) := (B.change j).symm (s.scale (B.route j) ^ 4 • v)
  have part j v : B.tune j • B.change j (walk j v) = v := by
    dsimp only [walk]; rw [LinearEquiv.apply_symm_apply, tune,power, smul_smul,inv_mul_cancel₀, one_smul]; exact pow_ne_zero _ (s.positive _).ne'
  have up j v (hv : Left.IsUnit (P.product H) v) : Left.IsUnit (B.cost P H j) (walk j v) :=
    (B.unit_move H j _).mpr (by rw [part]; exact hv)
  refine ⟨x,E,hx,hE,fun v e => ?_,?_⟩
  · calc v = B.tune i • B.change i (walk i v) := (part ..).symm
         _ = E := congr_arg (fun z => B.tune i • B.change i z) (hi' _ (up i _ e))
  have hz := Left.tends hat (fun i => walk i E) (Eventually.of_forall fun j => up j E hE)
  exact (B.convergence.evolve hz).congr' (by
    apply Eventually.of_forall; intro i; simp only [walk, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
end
end SatinStress.U3.Asymptote
