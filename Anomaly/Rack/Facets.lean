import Anomaly.Rack.ClockBuild
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}

lemma flight_budget (X:Aura n)(F:Firing n)(a b c d:ℝ)(p:Flight P q X h F a b)(t:a≤c)(v:b≤d)(u:0≤h) : Flight P q X h F c d:= p.large_r u t v

variable (f:I→ Bag n) (p q': I→ Aura n→ℝ) (T:∀ (i:I)(X:Aura n),Flight P q X h (f i X) (p i X) (q' i X))

def pinSeries (f:I→ Bag n)(z:Key I) : Bag n:= fun X=>∑ i:I,z i • f i X

def coatLie (p:I→Aura n→ℝ)(z:Key I) (X:Aura n):ℝ:= ∑ i:I, ‖z i‖*p i X

local notation "Zx" x:max=> pinSeries f x
include T
lemma pin_budget (z:Key I)(X:Aura n): Flight P q X h ((Zx z) X) (coatLie p z X) (coatLie q' z X):= Flight.whole _ _ _ _ fun _ _=> (T _ _).scR _

lemma industry (z:Key I) : ∀ X:Aura n,Title P h (cipherK q) ((pinSeries f z) X) X (coatLie p z X):=fun X=> (pin_budget f p q' T z X).tube.title

def zealPitch (T:∀ (i:I)(X:Aura n),Flight P q X h (f i X) (p i X) (q' i X))(z:Key I) : Rinse (Seat n) (Copy n):= (Title.powerQ _ _ (industry f p q' T z)).payX

-- Keep the Gamble: homogeneous in Keys, indeed exact global linear map
-- even at non-visible flags. Lean's Rinse is defined with real or unmarked tests;
-- check true key action at those Calls.
local notation "Vq" z:max=>zealPitch f p q' T z

lemma norm_key (x:Key I)(z:x∈hill I)(i:I):‖x i‖≤1 := (norm_le_pi_norm _ i).trans (mem_closedBall_zero_iff.mp z)

variable (hx:0≤ h) (w:3≤P.B)
include w hx

lemma zeal_ticket (z:Key I)(i:z∈hill I):
    Pitch P h (cipherK q) (zealPitch f p q' T z) (∑ i:I,p i) (fun x Y=> pinSeries f z Y x) := by
  let V:= Title.powerQ _ _ (industry _ _ _ T z)
  have H:= V.buys w hx
  have he(X:Aura n): coatLie p z X ≤ (∑ i:I,p i) X := by
    rw [Finset.sum_apply]; exact sum_le_sum fun j _=> mul_le_of_le_one_left (T j X).tube.price (norm_key f p q' T z i j) -- T unused include? tune check signature
  refine {H with dice := fun X=> (H.dice X).trans (he X), plays:= ?_}
  intro X D v Y l s F q; let t:=H.plays X D v Y l s F q
  exact {t with merit:= Medal.big t.merit (mul_le_mul_of_nonneg_right (he _) (q.merit.wage hx))}

lemma zeal_receipt (z:Key I)(i:z∈hill I)(X:Aura n):
    Fray P h (cipherK q) X ∅ ((Vq z) X ∅ X 1) ((∑ i:I,q' i) X) := by
  let t:= Vq z
  have hu: Bias.αt X X ∅ (cipherK q):= ⟨Subset.refl _, empty_subset _,by simp [Lattice.halo]⟩
  unfold zealPitch Bias.payX; rw [dif_pos hu]
  let H:= pin_budget f p q' T z X
  let F:= (Title.powerQ _ _ (industry _ _ _ T z)).scope _ _ _ hu.1 hu.2.1 hu.2.2
  apply Fringe.burn (F.toCrate)
  have he:= H.birth X (Subset.refl _)
  apply he.raise
  rw [Finset.sum_apply]; refine sum_le_sum (fun j _=> mul_le_of_le_one_left ?_ (norm_key f p q' T z i j))
  obtain ⟨_,h,_⟩:= (T j X).forms; exact h.price

omit hx w


def jetSlice (T:∀ (i:I)(X:Aura n),Flight P q X h (f i X) (p i X) (q' i X))(i:I): Rinse (Seat n) (Copy n):= (Title.powerQ _ _ fun X=>(T i X).tube.title).payX

lemma rindC (t:ℂ)(x:FC (Dwell n)): Sault.rind (t • x)= t • Sault.rind x:=map_smul ..

lemma zeal_scales (z:Key I)(X Y:Aura n)(D:Support (More n))(F:Copy n) :
    (Vq z) X D Y F=∑ i:I,z i • jetSlice f p q' T i X D Y F := by
  funext x; apply Subtype.ext; rw [Finset.sum_apply]; change (((Vq z) X D Y F) x).val=(Dough (Dwell n)).val _; rw [map_sum]
  unfold zealPitch Bias.payX
  split_ifs with d
  · change Sault.rind (coll_T P X D (pinSeries f z Y) x * (F x).val)= _
    simp_rw [jetSlice,Bias.payX,dif_pos d,Pi.smul_apply, Subalgebra.coe_val] -- tune
    change Sault.rind (coll_T P X D (pinSeries f z Y) x * (F x).val)=∑ i:I,z i • Sault.rind (coll_T P X D (f i Y) x * (F x).val)
    unfold coll_T; split_ifs; swap; · simp [Sault.rind]
    simp_rw [pinSeries,Finset.sum_apply,Pi.smul_apply,Finset.sum_mul, Algebra.smul_mul_assoc,Sault.rind,map_sum,map_smul]
  simp [jetSlice,Bias.payX,d]

lemma sliceLinear (i:I)(X Y:Aura n)(D:Support (More n)): ∃ H: Copy n →ₗ[ℂ] Copy n,∀ V,H V=jetSlice f p q' T i X D Y V := by
  let H:=jetSlice f p q' T i X D Y
  suffices ∃ L:Copy n→ₗ[ℂ]Copy n,∀ V,L V=H V from this
  refine ⟨⟨⟨H,?_⟩,?_⟩,fun _=>rfl⟩
  · intro x y; funext U; apply Subtype.ext; unfold H jetSlice Bias.payX; split; swap; · simp
    change Sault.rind (_ * ((x+y : Copy n) U).val) = Sault.rind _ + Sault.rind _
    simp only [Pi.add_apply,Subalgebra.coe_add,mul_add,Sault.rind,map_add]
  intro z x; funext U; apply Subtype.ext; dsimp only; unfold H jetSlice Bias.payX; split; swap; · simp
  change Sault.rind (_* ((z • x) U).val)=z • Sault.rind _
  rw [Pi.smul_apply,show ((z • (x U) : Cipher n)).val=z • (x U).val from rfl, Algebra.mul_smul_comm]; exact rindC f p q' T z _ -- tune


lemma zeal_series : Gamble (zealPitch f p q' T) := by
  intro X D _ Y t i F Q
  simp_rw [zeal_scales]
  refine Solvent.sum _ _ ?_
  intro j _; obtain ⟨L,w⟩:=sliceLinear f p q' T j X Y D
  simp_rw [← w]
  rw [Nat.add_comm i 1]
  exact Solvent.pair (LinearMap.lsmul ℂ (Copy n)) (Solvent.bill j) (Solvent.map L Q)

lemma zeal_plain (z:Key I) (F:ForceBudget n)(m:ℕ): Bake.Turf (fun X:Aura n=> layerN (settleK F) (Vq z) m X ∅):=by
  intro X V Z
  unfold layerN; simp only [Finset.sum_apply]; refine Finset.sum_congr rfl ?_
  intro i _; let K:= pinSeries f z; let Q:= Title.powerQ K _ (industry _ _ _ T z)
  refine clean_p (P:=P) (settleK F) _ V Q ?_ Z ?_ X i
  · intro Y X h W w j
    exact (pin_budget f p q' T z Y).tube.clean X h W w j
  intro X; rw [settle0]; rfl

lemma zeal_free (F:ForceBudget n) (m:ℕ) : layerN (settleK F) (Vq 0) m = settleK F := by
  have h: (Vq 0) = 0:= by funext X D Y F; rw [zeal_scales]; simp -- tune
  rw [h]; funext X D
  change (∑ i∈_, PowerSeries.coeff i (Cadre.chip 0 (settleK F) X D))=_
  rw [Finset.sum_eq_single (0:ℕ), Cadre.peg]
  · intro i _ j; cases i; contradiction
    nth_rw 1 [Cadre.peel]; rw [sprig,Cadre.ore]; simp
  simp

variable {σ:I→ Seat n}(hf:∀ i:I,∀ X:Aura n,σ i∉X.val → f i X=0)
include hf

lemma ringSlice (i:I)(X Y:Aura n)(D:Support (More n))(F:Copy n) (e:σ i ∉ Y.val):
    jetSlice f p q' T i X D Y F=0 := by
  funext W
  apply Subtype.ext; unfold jetSlice Bias.payX; split; swap; · rfl
  change Sault.rind (coll_T _ _ _ _ _*_)= 0
  rw [hf i Y e]; simp [coll_T,Sault.rind]

lemma coulomb (F:Copy n)(X Y:Aura n)(D:Support (More n)) (x y:Key I)(p':∀ i,σ i∈Y.val→ x i=y i):
    (Vq x) X D Y F=(Vq y) X D Y F := by
  rw [zeal_scales,zeal_scales]; refine sum_congr rfl ?_
  intro i _; by_cases v:σ i ∈ Y.val; rw [p' i v]
  rw [ringSlice f p q' T hf _ _ _ _ _ v]; simp

lemma keepsTune (F:ForceBudget n)(X:Aura n)(D:Support (More n))(i:ℕ): Hush σ X.val (fun z=> PowerSeries.coeff i (Cadre.chip (Vq z) (settleK F) X D)):=by
  induction i using Nat.strong_induction_on generalizing X D with
  | h i ih=>
    intro x hx y hy q
    cases i with
    | zero => simp_rw [Cadre.peg]
    | succ i =>
      dsimp only
      nth_rw 1 [Cadre.peel]
      nth_rw 1 [Cadre.peel D ((Vq y))]
      rw [sprig, sprig, Cadre.ore, Cadre.ore]; apply congrArg; refine sum_congr rfl ?_
      intro Y _; refine sum_congr rfl ?_
      intro G l; have hu:X.val=Y.val∪Palot.robe G:= (Cadre.drum_p ..|>.mp l).2.2
      rw [coulomb f p q' T hf _ _ _ _ x y (fun i w=> q i (hu.symm ▸ Finset.mem_union_left _ w))]
      apply congrArg; rw [coeff_prod,coeff_prod]; apply sum_congr rfl; intro k v; apply prod_congr rfl; intro s e
      exact ih _ (Nat.lt_succ_of_le ((single_le_sum (fun j _=> Nat.zero_le _) e).trans_eq (mem_finsuppAntidiag.mp v).1)) _ _ _ hx _ hy fun i w=>q i (hu.symm ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s,e,w⟩))

lemma zeal_hush (F:ForceBudget n)(m:ℕ)(X:Aura n)(D:Support (More n)) : Hush σ X.val (fun z=> layerN (settleK F) (Vq z) m X D) := by
  intro x hx y hy w; unfold layerN; exact sum_congr rfl fun i _=> keepsTune f p q' T hf F X D i x hx y hy w

end YM.CF.Vow.TreasuryFog
