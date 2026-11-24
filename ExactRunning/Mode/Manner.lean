import ExactRunning.Mode.Supply
/-!
# Full joint Hessian packets

The coarse penalty contributes also mixed entries, via a local
stencil with two background/change pairs. This uses the true
variation also on coarse links (exponentiate and left multiply).
Thus `closeBox` supplements the base stencils.

`merit` gives the corresponding film: apply `mariner` with the
coarse penalty as a lattice sum through two linear maps, for
backgrounds (`billZ` at `atJoint`) and for left tangents (`solid`,
with `rank` packaging).

`perfect` adds in the classical fine Hessian.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

open Pairing
variable (X)
open scoped Matrix.Norms.Frobenius

/-- Basis stencil for penalty / coarse site and axis -- stencils carry
internal tangent and external tangent independently. -/
def closeBox {P : Patch} (k : ℝ) (x : BassInput G P) (j : Axis) :=
  k * G.price ((pianoV true x j * pianoV false x j) * (poseBox true true x j)⁻¹)

def closeFace {P : Patch} (k : ℝ) (x : BassInput G P) := ∑ j, closeBox k x j

lemma tuneClose {P : Patch} {K : KernelChoices} (h : P.Branches K G) (k : ℝ) :
    ContDiffAt ℝ ω (closeFace (P:=P) (G:=G) k) 0 := by
  refine ContDiffAt.sum fun j _ => ?_
  have v (r) := (slot3 (A:=Audience.balcony P.Points) (G:=G) (P:=P) (n:=0) r (le_refl 0) j).listen P.center
  exact contDiffAt_const.mul
    (matrix_price_jet (((v true).mul (v false)).mul ((poseCast h true true).inv j)))

lemma close_pay (m : Side) :
    ∀ᶠ x in 𝓝 (0:Bang G m (X.up m)),
    tickets (X.S m) (input G m x.2.2 * input G m x.1.1)
        (X.Z m (Stationary.extend x.2.1 * headOn (X.S m) (X.choice m) true x))
    = ∑ i, closeFace X.kernel.penalty (pianist (X.S m) i x) := by
  have h : (X.S m).patch.Branches (X.S m).kernel G := X.branches
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr
    (fit_ward (X.S m) (X.choice m) h true true i))] with x hx
  unfold tickets
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum,closeFace,closeBox,direct_whip,hx,
    pulledOn (X.S m) (X.choice m)]
  simp [buffOn, atire, Z]; rfl

def rank (m : Side) : X.Hall m ≃L[ℝ] Corn (Co m X.Hold.tile) :=
  LinearEquiv.toContinuousLinearEquiv <|
    (cash (X.podium m)).trans (LinearEquiv.funCongrLeft ℝ ℝ (X.Hold.pack m).symm)

lemma rank_eq (y : X.Hall m) :
    X.rank m y = cash (X.podium m) y ∘ (X.Hold.pack m).symm := rfl

lemma first_rank (y : X.Hall m) :
    Pairing.first m (Entry G) (X.rank m y) = directX G (X.S m) y.1 := by
  simp only [direct_pay]
  rfl

lemma second_rank (y : X.Hall m) :
    Pairing.second m (X.Barrel.tile) (X.rank m y) = y.2 := rfl

-- insert tangents via solid: X.solid (X.rank y) = pav (0,y)
def bias : Eye X.Hold.tile (Acts G X.patch) :=
  Eyes.lhalf (fun _ => visibly X.patch true) (Entry G) +
  Eyes.rhalf (fun _ => velvetX X.patch) (X.Barrel.tile)

lemma bias_fresh : Fresh X.bias X.η :=
  Eyes.fresh_add (Eyes.freshL (Fresh.placed _) _) (Eyes.freshR (Fresh.placed _) _)

def solid (m) : Corn (Co m X.Hold.tile) →L[ℝ] Corn (Co m (Acts G (X.S m).patch)) :=
  (orbitR (G:=G) (X.S m) true).comp (Pairing.first (α:=X.Barrel.tile) m (Entry G)) +
  (orbitV (G:=G) (X.S m)).comp (Pairing.second m X.Barrel.tile)

lemma bias_path (m : Side) :
    Turns X.bias (X.solid m) :=
  Eyes.turns_add (Eyes.turnsL (orbit_path (G:=G) (X.S m) true) _) (Eyes.turnsR (velvet_path (X.S m)) _)

lemma solid_entry (y : X.Hall m) :
    X.solid m (X.rank m y) = pavilionB G (X.S m) (0,y) := by
  rw [solid,_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  erw [X.first_rank y,X.second_rank y]
  let J := pavilionB G (X.S m)
  let T := directX G (X.S m)
  change J (0,T.symm (T y.1),0)+J (0,0,y.2)=_
  rw [T.symm_apply_apply, ← map_add]
  simp [Prod.mk_add_mk]
  rfl

def foam (m : Side) (z : Box G m) (y : X.Hall m) :=
    tickets (X.S m) (input G m y.2 * co_bg G m z)
      (X.Z m (Stationary.extend y.1 * X.fg_bg m z))

def segment :=
  muralMap (X.S m) (closeFace (P:=(X.S m).patch) (G:=G) X.kernel.penalty)

def voyage (m : Side) (z : Box G m) := fun v =>
  X.segment (billZ (X.S m) (X.atJoint m) z + X.solid m v)

lemma voyage_eq (m) :
    ∀ᶠ z in 𝓝 0, X.foam m z =ᶠ[𝓝 0] (X.voyage m z ∘ X.rank m) := by
  let V := fun y : Box G m × X.Hall m => X.atJoint m y.1 + (0,y.2)
  have he : V 0=0 := by simp [V]
  have ht := (show Continuous V from ((X.atJoint m).cont.comp continuous_fst).add
    (continuous_const.prodMk continuous_snd)).continuousAt (x:=0)
  rw [ContinuousAt,he] at ht
  refine (ht.eventually (X.close_pay m)).curry_nhds.mono (fun z h => h.mono (fun y h => ?_))
  change X.foam m z y=X.voyage m z (X.rank m y)
  rw [voyage,solid_entry]
  let J := pavilionB G (X.S m)
  change X.foam m z y= X.segment (J (X.atJoint m z)+J (0,y))
  rw [← map_add, segment]

  unfold muralMap J
  simp_rw [rehearsing]
  have vb : headOn (X.S m) (X.choice m) true (V (z,y))=X.fg_bg m z := by
    rw [show headOn _ _ _ _ = headOn (X.S m) (X.choice m) true (X.atJoint m z) by
           simp [headOn,V]]
    exact X.joint_head z
  rw [vb, show (V (z,y)).2=y by simp [V,X.joint_snd],
     show (V (z,y)).1.1 = outer G m z by simp [V,X.joint_fst]] at h
  exact h

lemma ash (m : Side) : ContDiffAt ℝ ω (X.segment (m:=m)) 0 := by
  refine ContDiffAt.sum fun i _ => ?_
  have h := X.branches
  let F := rehearsal (G:=G) (X.S m) i
  exact (show ContDiffAt ℝ ω (closeFace X.kernel.penalty) (F 0) by
    rw [map_zero]; exact tuneClose h _).comp _ (f:=F) F.contDiff.contDiffAt

lemma windy (m : Side) :
    ∀ᶠ z in 𝓝 0, ContDiffAt ℝ ω (X.voyage m z) 0 := by
  let L := billZ (X.S m) (X.atJoint m)
  have h : Tendsto L (𝓝 0) (𝓝 0) := (map_zero L).symm ▸ L.cont.continuousAt.tendsto
  filter_upwards [h.eventually ((X.ash m).eventually (by simp))] with z hz

  let T := fun v => L z + X.solid m v
  exact (show ContDiffAt ℝ ω X.segment (T 0) by simp [T]; exact hz).comp _ (f:=T)
      (contDiffAt_const.add ((X.solid m).contDiff.contDiffAt))

def merit :
    Tray G X.Hold X.Hold (fun m z => damage (X.podium m) (X.foam m z) 0) where
  film := recitalX (sailor (closeFace X.kernel.penalty) X.eye X.bias)
  fit_strip := ⟨_,X.hη,cosmic_sail X.fresh X.bias_fresh _⟩
  ticket m := by
    refine mariner (X.S m) _ _ (X.turns m) (X.bias_path m) _
        (tuneClose X.branches _) ?_
    filter_upwards [X.voyage_eq m,X.windy m] with z h hz y v
    let Y := X.rank m
    obtain ⟨a,rfl⟩ := Y.surjective y
    obtain ⟨b,rfl⟩ := Y.surjective v
    change dotProduct (Y a) (repackM _ _ (damage _ _ 0) *ᵥ Y b)=iteratedFDeriv ℝ 2 (X.voyage m z) 0 ![Y a,Y b]
    have u := detracts (X.podium m) (X.foam m z) 0 a b
    rw [(h.iteratedFDeriv ℝ 2).self_of_nhds] at u

    let P := X.Hold.pack m
    rw [repack_dot P] at u
    rw [← repack_act P P] at u
    refine u.trans ?_
    let V := Y.toContinuousLinearMap
    have hx := wired V (f:=X.voyage m z) (x:=0) (by rw [map_zero]; exact hz.analyticAt) 2 ![a,b]
    rw [map_zero,show _ = (![Y a,Y b] : Fin 2 → _) from (show V ∘ ![a,b] = _
      from funext fun i => by fin_cases i <;> rfl)] at hx
    exact hx

@[simp] lemma fg_bg_zero (m : Side) : X.fg_bg m 0=1 := by rw [fg_bg,map_zero,lead_zero]
@[simp] lemma co_bg_zero (m : Side) : co_bg G m 0=1 := by rw [co_bg,map_zero,input_zero]
lemma fg_bg_lit (m : Side) : Thaw (X.fg_bg m) 0 :=
  Thaw.comp (w:=inner G m)
    (show Thaw (X.lead m) (inner G m 0) by rw [map_zero];exact lead_lit)
    (inner G m).contDiff.contDiffAt
lemma co_bg_lit (m : Side) : Army (co_bg G m) 0 :=
  Army.powL (outer G m).contDiff.contDiffAt

abbrev mainLeg (m : Side) :=
  πl (Lines G (X.up m) 1) (Lines G m 0) ℝ * πl (X.Barrel.key m) (Lines G m 1) ℝ

lemma main_leg (m) (x : X.Hall m) :
    X.mainLeg m *ᵥ cash (X.podium m) x = x.1.1 := by
  rw [mainLeg,show πl (Lines G (X.up m) 1) (Lines G m 0) ℝ= _ from (X.rear_place (m:=m)).symm]
  rw [← mulVec_mulVec,podium,halvesC (A:=helmets _ _ _)]
  rw [πl,fromCols_mulVec, zero_mulVec,one_mulVec,add_zero, Sum.elim_comp_inl,rear_cost]

lemma new_frame (m : Side) :
    ∀ᶠ z in 𝓝 0,
      (X.mainLeg m)ᵀ * flare E.p E.r (X.fg_bg m z).1 * X.mainLeg m +
        damage (X.podium m) (X.foam m z) 0 =
      X.full (X.fg_bg m z) (co_bg G m z) := by
  let L : X.Hall m→L[ℝ] Link G (X.up m) := (ContinuousLinearMap.fst ℝ _ _).comp
    (ContinuousLinearMap.fst ℝ _ _)
  filter_upwards [X.voyage_eq m,X.windy m,X.witness_lit (X.fg_bg_lit m) (by simp)] with z h hz ht
  let r := X.rank m
  have hp : ContDiffAt ℝ ω (X.foam m z) 0 :=
    ((show ContDiffAt ℝ ω (X.voyage m z) (r 0) from (map_zero r).symm ▸ hz).comp 0
     (f:=r) r.contDiff.contDiffAt).congr_of_eventuallyEq h
  let K := burn E.p E.r (X.fg_bg m z).1
  have hx : X.sitting (X.fg_bg m z) (co_bg G m z)=K ∘ L + X.foam m z := rfl
  have hu : ContDiffAt ℝ ω K (L 0) := by rw [map_zero];exact ht.known
  refine damage_eq (X.podium m) fun x y => ?_
  rw [full,detracts,Matrix.add_mulVec,dotProduct_add,detracts,hx,
    iteratedFDeriv_add_apply ((hu.comp _ L.contDiff.contDiffAt).of_le le_top)
      (hp.of_le le_top), _root_.add_apply,wired L hu.analyticAt,map_zero,both_cost,main_leg,main_leg]

  have hc := detracts (pocket _) K 0 x.1.1 y.1.1
  rw [cash_pocket,cash_pocket] at hc
  rw [show L ∘ ![x,y] = ![x.1.1,y.1.1] from funext fun i => by fin_cases i <;>rfl, ← hc];rfl

def perfect :
    Tray G X.Hold X.Hold (fun m z => X.full (X.fg_bg m z) (co_bg G m z)) :=
  let R := (Tub.fst (Du G) X.Scroll (Loom G)).mul (Tub.fst _ X.Barrel (Front G))
  ((((R.tr).mul X.sweet).mul R).plus X.merit).shift X.new_frame

end BlockTie
end ExactRunning
