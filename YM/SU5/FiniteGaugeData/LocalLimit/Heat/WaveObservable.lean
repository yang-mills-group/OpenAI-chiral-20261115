import YM.CF.Vp929.Stage.Plant

/-!
# The canonical wave test is observable at one field

Factoring through particle-hole projection, and through a sea read at identity.
This file concerns rates for the *929-family Service* (see `Vp929/Stage/API`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit
/-- Observations through a possibly lossy observation into a finite-dimensional space. -/
theorem exists_observation_factor {D E F : Type*}
    [AddCommGroup D] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [Module ℝ D] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedSpace ℝ F] (L : D →ₗ[ℝ] E) (L' : D →ₗ[ℝ] F)
    (h : LinearMap.ker L ≤ LinearMap.ker L') : ∃ f : E →L[ℝ] F, ∀ x, f (L x) = L' x := by
  obtain ⟨V,hV⟩ := Submodule.exists_isCompl (LinearMap.range L)
  let f := (LinearMap.ker L).liftQ L' h
  let e := LinearMap.quotKerEquivRange L
  let P := L.range.projectionOnto V hV
  refine ⟨LinearMap.toContinuousLinearMap (f.comp (e.symm.toLinearMap.comp P)), fun x => ?_⟩
  change f (e.symm (P (L x))) = _
  rw [show P (L x) = e (Submodule.Quotient.mk x) from ?_, LinearEquiv.symm_apply_apply]
  · rfl
  rw [show P (L x) = ⟨L x,x,rfl⟩ from Submodule.projectionOnto_apply_of_mem_left hV ⟨x,rfl⟩]
  exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk L x).symm

variable {s : Side}

/-- The block of a coefficient with row in unoccupied modes and column in occupied modes. -/
def phBlock (P : Op (Single s)) : Op (Single s) →ₗ[ℝ] Op (Single s) where
  toFun A := (1-P)*A*P
  map_add' _ _ := by rw [mul_add, add_mul]
  map_smul' _ _ := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- For a sea at a fixed background the projected particle-hole coefficient is
recovered by a *continuous linear map* of the whole ket (here prior to exponentiation). -/
theorem observe_linear_trace {P : Op (Single s)} {y : Phys s} (hp : IsStarProjection P)
    (hy : Sea P y) :
    ∃ f : Phys s →L[ℝ] Op (Single s), ∀ X : Cipher s,
      f (acts (tank P X) y) = phBlock P (orbitPH X) := by
  let L := ((tale_L y).comp (tankL P)).toLinearMap.restrictScalars ℝ
  let L' := (show (Cipher s : Type) →ₗ[ℝ] Op (Single s) from
    ⟨⟨orbitPH, orbP⟩, fun m x => Fixed.Voltage.orbit_smul m x⟩)
  exact exists_observation_factor L ((phBlock P).comp L')
    (fun X e => Test.Plum.stampK hp hy e)

/-- Divide out the sea component.  In contrast to a CapP partition denominator,
this projection on this specialized input is nonzero. -/
def onSea (y d : Phys s) : Phys s :=
  (inner ℂ y d)⁻¹ • d

lemma onSea_exp {P : Op (Single s)} {y : Phys s} (hp : IsStarProjection P)
    (hy : Sea P y) (a : ℂ) (X : Cipher s) :
    let d := Complex.exp a • acts (tank P (exp X)) y
    inner ℂ y d ≠ 0 ∧ onSea y d - y = acts (tank P (exp (cloudless X)-1)) y := by
  let W := cloudless X
  have hW : Pastry.pane W = 0 := cloudless_two _
  let z : Cipher s := hollow (Pastry.pane X)
  let b := Complex.exp a * Complex.exp (Pastry.pane X)
  let T := (nursery P hp).cook
  have hb : b ≠ 0 := by unfold b; exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  intro d
  have hd : d = b • acts (tank P (exp W)) y := by
    have he : X=W+z := sub_add_cancel X z |>.symm
    letI : NormedAlgebra ℚ (Cipher s) := NormedAlgebra.restrictScalars ℚ ℝ (Cipher s)
    dsimp only [d]
    change Complex.exp a • acts (T (exp X)) y = _
    nth_rw 1 [he]; rw [exp_add,map_mul]
    change Complex.exp a • acts ((tank P (exp W))*tank P (exp z)) y = _
    rw [act_mul,show exp z = hollow (Complex.exp (Pastry.pane X)) from (Iva.yeaH (Pastry.pane X)).symm,
      Test.Plum.sinkH _ hp,act_smul,act_one,map_smul,smul_smul]
  have he : inner ℂ y d = b := by
    rw [hd,inner_smul_right,testTank hp hy,paneExp,hW,Complex.exp_zero,mul_one]
  refine ⟨he ▸ hb,?_⟩
  rw [onSea,he,hd,inv_smul_smul₀ hb]
  change _ = acts (T (exp W - 1)) y
  rw [map_sub,act_sub,map_one,act_one]
  rfl

theorem observe_trace {P : Op (Single s)} {y : Phys s} (hp : IsStarProjection P)
    (hy : Sea P y) :
    ∃ f : Phys s →L[ℝ] Op (Single s), ∀ X : Cipher s, ∀ a : ℂ,
      let d := Complex.exp a • acts (tank P (exp X)) y
      f (onSea y d - y) = phBlock P (orbitPH X) := by
  obtain ⟨f,H⟩ := observe_linear_trace hp hy
  refine ⟨f,fun X a=>?_⟩
  intro d
  rw [(onSea_exp hp hy a X).2, H,Moto.peak_l _ (cloudless_two X)]
  rw [cloudless,Moto.tail_K,Moto.hol_l,sub_zero]

/-- Admissible regular arrays at some price. We don't give this space a topology. -/
def regularSpace (p : BudgetPoint) (h : ℝ) (s : Side) : Submodule ℝ (RegBudget s) where
  carrier := { F | ∃ b, IncX Utrue F p h b }
  zero_mem' := ⟨0,(Vale.lye Utrue p h).1⟩
  add_mem' := by rintro x y ⟨b,hb⟩ ⟨c,hc⟩; exact ⟨_,Ione.addT p hb hc⟩
  smul_mem' := by rintro a x ⟨b,hb⟩; exact ⟨_, Fixed.Voltage.crestV p _ hb a⟩

theorem detect_wave_block {L : Side} (M : Male) {j : ℕ} {h σ : ℝ} {p : BudgetPoint}
    (hp : p.power = 2) (hh : 1 ≤ h) (hl : 1 ≤ j) (hf : Frequency L s σ) :
    ∃ f : Op (Single s) →L[ℝ] SpaceM, ∀ F : RegBudget s, ∀ b : ℝ, IncX Utrue F p h b →
      f (phBlock (spar j M (1:Pane s)) (StackL F univ)) = waveTest σ F j M := by
  let D := regularSpace p h s
  let S := (Fixed.Voltage.frame_P (n:=s) univ).comp D.subtype
  let X := Test.TestW.pointC s j σ M
  let Y := phBlock (spar j M (1:Pane s))
  have H (x : D) (g : (Y.comp S) x = 0) : X (S x) = 0 := by
    obtain ⟨b,hb⟩ := (show ∃ b, IncX Utrue x.val p h b from x.property)
    have hg : Y (S x) = Y (S 0) := by rw [map_zero,map_zero]; exact g
    have hu : X (S x) = X (S 0) := Test.TestW.ovis p hb (Vale.lye Utrue p h).1 hg hh hp hh hp hf hl
    rw [map_zero,map_zero] at hu; exact hu
  obtain ⟨f,hf⟩ := exists_observation_factor (Y.comp S) (X.toLinearMap.comp S) (fun x e=> H x e)
  exact ⟨f,fun F b e=> hf (⟨F,b,e⟩ : D)⟩

variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m B : Side} {U : Grasp V.U B d} {W : GivenX V U}
  {F : Scree.Loom (mid m B)} {A : PathData SU.group}
local notation "Ω" => mid m B

/-- The full-stack wave test, not just a Pave jet. Observable off the solved wave,
already continuous assuming just physical continuity of the field (at one point!).
This is why the lower canonical step can be used after the heat burn-in. -/
lemma continuous_wave_of_dens {I : Interest (mid m B)} {L : Side} {p : BudgetPoint}
    {h σ x : ℝ} {k : ℕ} {kL : Clip} (hp : p.power=2) (hh : 1 ≤ h)
    (hl : 1 ≤ K.j) (hf : Frequency L (mid m B) σ) (u : Roof (mid m B) x d k F)
    (hR : U.roundZ ≤ (mid m B).val) (hq : p.threshold ≤ x)
    {T : Type*} [TopologicalSpace T] (G : T → Corr (mid m B)) (v β : T → ℝ)
    (o : T → ℂ) (tags : Ids (mid m B))
    (H : Continuous fun t=> denZ (construct p A kL I (β t) (G t) (o t)) U F (1,tags))
    (hG : ∀ t, IncX Utrue (G t).1 p h (v t)) :
    Continuous fun t=> waveTest σ (G t).1 K.j I.M := by
  let y : Orbit Ω := (1,tags)
  have he : flags p.threshold y.1 = ∅ := UVNext.CouplingReset.flags_one p
  have hy : F y = 1 := Vale.Grace.Robes.solar _ F u p hq he
  let P := spar K.j I.M (F y)
  let r := changeM U (F y) I.M
  let Z := Hest.boat (I.P.den (F y))
  let X(t) := construct p A kL I (β t) (G t) (o t)
  let E(t) := Test.Plum.traceWater y p (G t) F I
  let D(t) := denZ (X t) U F y
  have hr : Sea P r := Spire.sea_g hR (F y) (u.paid y) I.M
  have ht := (U.broadness (mid m B) hR I.M).projection (F y) (u.paid y)
  have hD t : D t = Complex.exp ((X t).betaL F y) • acts (tank P (exp (E t))) r :=
    Test.Plum.sun_reader y he hR (u.paid y)
  have hO : Continuous fun t=> onSea r (D t) := (((continuous_const.inner H).inv₀ (fun t=> by
    change inner ℂ r (D t) ≠ 0
    rw [hD]; exact (onSea_exp ht hr ((X t).betaL F y) (E t)).1))).smul H
  obtain ⟨f,g⟩ := observe_trace ht hr
  obtain ⟨l,w⟩ := detect_wave_block I.M hp hh hl hf
  have hx t : f (onSea r (D t)-r) = phBlock P (StackL (G t).1 univ) + phBlock P (orbitPH Z) := by
    have he : orbitPH (E t) = StackL (G t).1 univ + orbitPH Z := by
      rw [Test.Plum.harvest_stack p]; exact Haro.orbP ..
    rw [hD, g, he, map_add]
  refine (show Continuous fun t=> l (f (onSea r (D t)-r) - phBlock P (orbitPH Z)) from
    l.continuous.comp ((f.continuous.comp (hO.sub continuous_const)).sub continuous_const)).congr (fun t=>?_)
  rw [hx, add_sub_cancel_right]; unfold P; rw [hy]; exact w _ _ (hG t)

end LocalLimit
end YM.CF.Py.Rate
