import YM.SU5.FiniteGaugeData.Tapestry.Equivariant
import YM.CF.Matter.Mass

/-!
# The actual ascender and two matter pockets

These are on ALL arguments of the Mark (both panes). We use a tor mark price
here; designates one creation and one removal with separate pockets. Coefficients
can already sum over generations on a promotion; price their true **type** by
a (constant-center) character so `byMode` pays it. See also the `phase` choice
in `MacroSix.Bodies` for the original mark; on the fixed probing labels, it IS
the exact generation. No invariance of *separate* factorized raw predictions
is used to get the results in this file. No assumption that block factors the
extension of the insertion with its link coefficient!
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 470000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Pockets
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure
  Next.SectorChange Common Fock Satin Tapestry
attribute [local instance] opCStarAlgebra

abbrev wrapType (x : SU.Slot) := (Window.family x).2

lemma type_ten (u : Fin 3) (x : SU.Ten) : Window.family (u,.inl x) = (u,true) := rfl
lemma type_five (u : Fin 3) (x : SU.F) : Window.family (u,.inr x) = (u,false) := rfl

-- explicitly retain just the 2 irreducible-representation TYPES through stepping,
-- with the SU center Ward test as identifier.
def centerPay (b : Bool) := SU.z ^ (if b then 2 else 4 : ℕ)

lemma paysTag (b : SU.Slot) : SU.z^(charge b) = centerPay (wrapType b) := by
  obtain ⟨b,u|u⟩ := b <;> rfl

lemma center_injective : Injective centerPay := by
  intro i j h
  unfold centerPay at h
  have ht := z_prim.pow_inj (by cases i<;> decide) (by cases j<;> decide) h
  cases i <;> cases j <;> simp_all

lemma center_activated (b) : centerPay b ≠ 1 := fun h ↦ by
  have ht := z_prim.dvd_of_pow_eq_one _ h
  cases b <;> simp at ht

lemma center_scale (b) : ‖centerPay b‖=1 := by rw [centerPay,norm_pow,SU.z_n,one_pow]

section tor
open Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP

-- same center through a *constant total* use of ModeGauge (link arguments fixed)
-- adapted `CF/Prism/Gale:central_ok`
lemma constant_comm (g : SU.E) : SU.central*g=g*SU.central := by
  apply SU.group.mat_injective
  change fund (central*g)= fund (g*central)
  rw [fund_mul,fund_mul]
  change (Matrix.diagonal _) * _ = _ * Matrix.diagonal _
  ext i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm]

abbrev totalCenter (N : Side) : Seat N → SU.E := fun _ ↦ SU.central
local notation "T[" N:max "]" => tradew N (totalCenter N)

variable {N P : Side}
lemma gauge_constant (U : Pane N) : Lattice.gauge (totalCenter N) U = U := by
  funext i
  change SU.central*U i*SU.central⁻¹=U i
  rw [constant_comm,mul_inv_cancel_right]

lemma july_constant (G : Ratio N P) (x : Nom N P) : july G (totalCenter P) x = x :=
  Prod.ext (gauge_constant x.1) (gauge_constant x.2)

lemma tradew_constant (i k : Single N) : (T[N]).val i k =
    if i=k then centerPay (wrapType i.2) else 0 := by
  obtain ⟨a,b⟩ := i; obtain ⟨u,i⟩ := k
  change jump (Equiv.refl _) (fun _ ↦ (matter central).val) (a,b) (u,i)
    = if _ then _ else _
  rw [jump_apply]; simp only [Equiv.refl_apply]
  by_cases h : a=u
  · subst u
    rw [if_pos rfl,SU.by_charge]
    by_cases h : b=i
    · subst i; simpa using paysTag b
    simp [h]
  simp [h]

lemma charge_act (x : Ket (Single N)) (i : Single N) :
    (acts (T[N]).val x).ofLp i = centerPay (wrapType i.2) * x.ofLp i := by
  rw [act_at]
  change ∑ k, (T[N]).val i k * x.ofLp k = _
  rw [sum_eq_single i]; swap
  · intro j _ h; rw [tradew_constant,if_neg (Ne.symm h),zero_mul]
  swap; · simp
  rw [tradew_constant,if_pos rfl]

lemma center_coords {b : Bool} {x : Ket (Single N)} :
    acts (T[N]).val x=centerPay b • x ↔ ∀ i : Single N, x.ofLp i ≠ 0 → wrapType i.2=b := by
  constructor
  · intro h i p; refine center_injective (mul_right_cancel₀ p ?_)
    rw [←charge_act x i,h]; rfl
  intro h; apply PiLp.ext; intro i; rw [charge_act]
  change _ = _ * x.ofLp i
  by_cases p : x.ofLp i=0; · simp [p]
  rw [h i p]

lemma center_basis (i : Single N) : acts (T[N]).val (basisKet i) =
    centerPay (wrapType i.2) • basisKet i := center_coords.mpr (fun j h ↦ by
  contrapose! h
  exact (show (basisKet i).ofLp j=0 from (by
    rw [basis_apply]; exact if_neg (fun e ↦ h (by subst j; rfl)))))

structure Pinned (b : Bool) (S : Support (More N))
    (X : Finset (Single N)) (x : Ket (Single N)) : Prop where
  grade : withinM X x
  label_ : acts (tradew N (totalCenter N)).val x = centerPay b • x
  far_ : withinM (modesIn N S) x
variable {b : Bool} {S Q' U V : Support (More N)}

lemma Pinned.basis {i : Single N} {X : Finset (Single N)}
    (f : i ∈ X) (g : wrapType i.2=b) (u : node i.1.1 ∈ S) : Pinned b S X (basisKet i) :=
  ⟨within_basis X i f,g ▸ center_basis i,within_basis _ i ((modes_at ..).2 u)⟩

lemma Pinned.mono {x : Ket (Single N)} {X : Finset (Single N)}
    (p : Pinned b S X x) (h : S ⊆ V) : Pinned b V X x := ⟨p.grade,p.label_,
      (within_test ..).2 (fun i v ↦ (within_test ..).1 p.far_ _ (fun q ↦ v (modes_monotone h q)))⟩

variable (G : Ratio N P) (j : ℕ){R : ℕ}(p : LaurentRadius j G.count R)
  (ho : Odd G.count.val) (M : Male)(Q : Haro.SpaceM) (z : Nom N P)
local notation "Pad[" S:max "]" => padded G S (clothRadius G.count R)
include ho p
lemma Pinned.rise {x : Ket (Single N)} (h : Pinned b S (Tset N) x) :
    Pinned b Pad[S] (Tset P) (byMode G j Q.val M z true x) := by
  refine ⟨carried_up G j Q.val M ho z true h.grade, ?_, mode_support G j Q.val M ho S p h.far_ true⟩
  rw [modeGauge G (totalCenter P) j p ho M Q]
  rw [show scaleG G (totalCenter P)=totalCenter N from rfl,h.label_, map_smul,july_constant]

lemma Pinned.fall {x : Ket (Single N)} (h : Pinned b S (Tset N)ᶜ x) :
    Pinned b Pad[S] (Tset P)ᶜ (byMode G j Q.val M z false x) := by
  refine ⟨carried_down G j Q.val M ho z false h.grade,?_,mode_support G j Q.val M ho S p h.far_ false⟩
  rw [modeGauge G (totalCenter P) j p ho M Q]
  rw [show scaleG G (totalCenter P)=totalCenter N from rfl,h.label_,map_smul,july_constant]

omit ho p
/-- One chiral creation in `S`, one removal in `Q'`. Both orders included (no need
for sign computations when reflecting). Depends only on the tor version of the two pockets. -/
def torRibbon (b : Bool) (S Q' : Support (More N)) : Submodule ℂ (FC (Single N)) :=
  Submodule.span ℂ {A | ∃ x y : Ket (Single N), Pinned b S (Tset N) x ∧
    Pinned b Q' (Tset N)ᶜ y ∧ (A = create x * Fock.remove y ∨ A = Fock.remove y * create x)}

lemma torRibbon_lr {x y : Ket (Single N)} (h : Pinned b S (Tset N) x)
    (u : Pinned b Q' (Tset N)ᶜ y) : create x * Fock.remove y ∈ torRibbon b S Q' :=
  Submodule.subset_span (show _ ∈ _ from ⟨x,y,h,u,Or.inl rfl⟩)

lemma torRibbon_rl {x y : Ket (Single N)} (h : Pinned b S (Tset N) x)
    (u : Pinned b Q' (Tset N)ᶜ y) : Fock.remove y * create x ∈ torRibbon b S Q' :=
  Submodule.subset_span (show _ ∈ _ from ⟨x,y,h,u,Or.inr rfl⟩)

lemma torRibbon_mono (h : S ⊆ U) (g : Q' ⊆ V) : torRibbon b S Q' ≤ torRibbon b U V :=
  Submodule.span_mono (by
    rintro A ⟨x,y,p,q,e⟩; exact ⟨x,y,p.mono h,q.mono g,e⟩)

include ho p
lemma promote_ribbon {A : FC (Single N)} (h : A ∈ torRibbon b S Q') :
    subF G j Q.val M ho z A ∈ torRibbon b Pad[S] Pad[Q'] := by
  let L := torRibbon b Pad[S] Pad[Q']
  refine Submodule.span_induction (p:=fun x _ ↦ subF G j Q.val M ho z x ∈ L) ?_
    (by rw [map_zero]; exact L.zero_mem)
    (fun _ _ _ _ p q ↦ by rw [map_add]; exact L.add_mem p q)
    (fun a x _ p ↦ by rw [map_smul]; exact L.smul_mem a p) h
  rintro A ⟨x,y,u,v,w⟩
  have hx := fine_create x u.grade (within_univ _)
  have hy := fine_remove y v.grade (within_univ _)
  have he := u.rise G j p ho M Q z; have hw := v.fall G j p ho M Q z
  rcases w with rfl|rfl
  · rw [sub_mul _ _ _ _ _ _ hx hy,sub_create _ _ _ _ _ _ u.grade,
      sub_remove _ _ _ _ _ _ v.grade]; exact torRibbon_lr he hw
  rw [sub_mul _ _ _ _ _ _ hy hx,sub_remove _ _ _ _ _ _ v.grade,
    sub_create _ _ _ _ _ _ u.grade]; exact torRibbon_rl he hw

omit p ho
set_option linter.unusedSectionVars false in -- manual namespace focus
lemma torRibbon_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → FC (Single N)} (h : ∀ x, f x ∈ torRibbon b S Q') :
    ∫ x, f x ∂μ ∈ torRibbon b S Q' := by
  by_cases v : Integrable f μ
  · let T := (torRibbon b S Q').restrictScalars ℝ
    exact T.convex.integral_mem T.closed_of_finiteDimensional
      (show ∀ᵐ x ∂μ, f x ∈ T from Eventually.of_forall h) v
  rw [integral_undef v]; apply Submodule.zero_mem

include p ho
lemma push_ribbon (A : RG.StepData (More N) (More P)) (q : Chi) (d β : ℝ)
    (l : Loom N) {f : Mark N} (h : ∀ W, f W ∈ torRibbon b S Q') (x : Fields P) :
    pushMark G A j Q.val M ho q d β l f x ∈ torRibbon b Pad[S] Pad[Q'] := by
  let R := (torRibbon b Pad[S] Pad[Q']).restrictScalars ℝ
  unfold pushMark linkLaw; apply torRibbon_integral
  intro V; apply Submodule.smul_mem R; unfold Advance.assembled; apply torRibbon_integral
  intro i; apply Submodule.smul_mem R
  exact Submodule.sum_mem _ fun j _ ↦ promote_ribbon G _ p ho M Q _ (h _)
end tor
end YM.CF.Buffered.Afterglow.Pockets
namespace YM.CF.Buffered.Afterglow.Pockets
#print axioms push_ribbon
#print axioms center_basis
#print axioms center_coords
end YM.CF.Buffered.Afterglow.Pockets
