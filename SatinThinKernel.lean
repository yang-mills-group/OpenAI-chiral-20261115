import SatinFixedContrastNovember4

import SatinThinWall

/-!
# A thin bilocal-composite experiment: IV. point prices

Connect to the literal continuum-position Euclidean readings of the purchased
`commonWell` also, at **each width**, on strict-separation budgets. We will test
against the point (finite-width) and gap criteria in the references with this.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon

open MacroGrid Set

section
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "M" => timeMesh P.par
local notation "H" => P.ColorHil 3 ξ
local notation "ω" => P.colorZero 3 ξ
local notation "S" => P.physicalEnergy 3 ξ
local notation "E" => (S).E
local notation "Γ" => P.truck 3 ξ
local notation "G" => P.ManyF 3 ξ
local notation "Ω" => P.heaven 3 ξ
local notation "R" => P.seasons 3 ξ
local notation "V₀" => P.cartage 3 ξ
local notation "π'" => P.wealth 3 ξ
local notation "λ'" => (P.enter 3 ξ)

variable (A : P.Apron) (eA : P.birthF 3 A.s A.F)
local notation "Y" => P.thinOrigin x A eA
local notation "w" => A.realWidth P 3

theorem thinCenterEntry : flashY x A 3 = (R).E ((w).toNNReal) (π' Y) :=
  (congrArg (π') (P.thinRawEntry x A eA)).trans (P.bankHeat 3 ξ _ _)

omit eA in
private lemma thin_thermal {X:Hilbert} (v:X.Op) (R':OS.Semigroup X (3:Axis))
    (t g u b:ℝ≥0)(x y:X)(h:∀ (a:ℝ≥0)(z:X), R'.E a (v z)= v (R'.E a z))(r:t+(g+u)=b) :
    inner ℂ (R'.E t x) (R'.E g (v (R'.E u y)))= inner ℂ x (v (R'.E b y)) := by
  have hu (t u:ℝ≥0)(z:X) : R'.E t (R'.E u z)= R'.E (t+u) z := by rw [R'.time]; rfl
  rw [OS.Semigroup.swing,h,h,hu,hu,add_assoc,r]

-- general unequal widths
variable (B:P.Apron)(eB:P.birthF 3 B.s B.F)
local notation "w'" => B.realWidth P 3
local notation "Z'" => P.thinOrigin x B eB
local notation "Ψ" => usher (A.kiss P 3) B
local notation "L" => ([false,true]:List Bool)
local notation "K" => P.commonWell 3 x Ψ

/-- Formula for the ordered (plus) kernel even between two different
heights. True continuous positions on x. We've simply accounted for (not
altered) the heat through the widths. -/
lemma thin_kernel (p q:Vantage)(J:P.Ellis 3 x)(h:p (3:Axis) + (w) < q 3 - (w')) :
    K (usher p q) L =
      inner ℂ (π' Y) (V₀ (q-p) ((R).E ((q 3-p 3).toNNReal) (π' Z'))) := by
  let F:= Ψ; let a:=usher (0:Vantage) (q-p); let d:ℝ:= (q-p) 3
  have hd:d=q 3-p 3:=rfl
  have hr:(w)+(w')< d:=by linarith only [hd,h]
  have paid : P.Turnstile 3 Ψ L a:= List.pairwise_pair.mpr (show 0+(w) < d - (w') by linarith only [hr])
  have shift:usher p q=settler a p := by funext i; cases i; exact (add_zero _).symm; exact (show q=p+(q-p) by abel)
  rw [shift]; apply Eq.trans (P.common_shift 3 x Ψ a L J ⟨3,L,List.Perm.refl _, paid⟩ p).2
  let u:= (w).toNNReal; let v:=(w').toNNReal; let g:=(d-((w)+(w'))).toNNReal
  let A':=V₀ (q-p);
  have hz:u+(g+v)=(q 3-p 3).toNNReal:= by
    ext; have ha:= A.real_width_pos P 3; have hb:= B.real_width_pos P 3
    have hq : 0 ≤ d - ((w)+(w')) := sub_nonneg.mpr hr.le
    simp only [u,v,g,NNReal.coe_add,← hd,Real.coe_toNNReal, ha.le,hb.le,hq,
      (show 0≤d from (add_pos ha hb).le.trans hr.le)]
    ring
  exact (avail_cross x (A.kiss P 3) B 3 (q-p) J hr).trans ((congrArg₂ (inner ℂ)
    ((flashY_glare x A 3).trans (P.thinCenterEntry x A eA))
    (congrArg (fun y:G => (R).E g (A' y)) (P.thinCenterEntry x B eB))).trans
      (thin_thermal A' R u g v _ (π' Y) (π' Z') (P.warm_drive 3 ξ (q-p)) hz))

section
private lemma thin_film {X:Hilbert} (U:OS.Semigroup X (3:Axis))(x y:X)(Y' Z W:X.Op)(a b t:ℝ≥0)
    (e: Y'.adjoint.comp Z=W)(he:∀ z:X, U.E a (W z)=W (U.E a z))(p:t=a+b):
    inner ℂ (Y' (U.E a x)) (Z (U.E b y))= inner ℂ x (W (U.E t y)):= by
  rw [← ContinuousLinearMap.adjoint_inner_right]; rw [←ContinuousLinearMap.comp_apply Y'.adjoint,e,
    U.swing,he,p,U.time]; rfl
end

lemma thin_pair_well_price (p q:Vantage)(a:p 3 + (w) < 0)(b:(w') < q 3)(J:P.Ellis 3 x) :
    K (usher p q) L = inner ℂ (P.thinRay x A eA (opposeR 3 p)) (P.thinRay x B eB q) := by
  have he: (V₀ (opposeR 3 p)).adjoint.comp (V₀ q)= V₀ (q-p) := by
    rw [P.cart_mirror,P.cart_reverses,← P.cart_paves,sub_eq_add_neg, add_comm]
  have ht: (q 3-p 3).toNNReal = ((opposeR 3 p) 3).toNNReal + (q 3).toNNReal:= by
    rw [show (opposeR 3 p) 3= -p 3 from if_pos rfl, show q 3-p 3= (-p 3)+q 3 by ring]
    exact Real.toNNReal_add (by linarith [A.real_width_pos P 3]) ((B.real_width_pos P 3).trans b).le
  exact (P.thin_kernel x A eA B eB p q J (by linarith only [a,b])).trans
    (thin_film R (π' Y) (π' Z') _ _ _ _ _ _ he (fun _=> P.warm_drive 3 ξ _ _ _) ht).symm

private lemma thin_early_change_integral (F : SampleDose) :
    (P.thinKet x A eA (flipDose F 3)) =
      ∫ p:Vantage, (F.val p:ℂ) • P.thinRay x A eA (opposeR 3 p) := by
  let f(p:Vantage):=((flipDose F 3).val p:ℂ) • P.thinRay x A eA p
  have he: MeasurePreserving (poseMirror 3).toMeasurableEquiv volume volume:= opposite_money 3
  refine (he.integral_comp' f).symm.trans (integral_congr_ae (Eventually.of_forall fun p=>?_))
  exact congrArg (fun b:ℝ => (b:ℂ) • P.thinRay x A eA (opposeR 3 p)) (congrArg F.val (reflectPose_twice 3 p))
private lemma thin_scaled (X:Hilbert)(v q:X)(a b:ℝ): inner ℂ ((a:ℂ) • v) ((b:ℂ) • q) = (a:ℂ)*(b:ℂ)*inner ℂ v q:=by
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal,mul_assoc]
lemma thin_contPrice (F U:SampleDose)(a:P.WallBefore A F 0)(b:P.WallAfter B U 0)(J:P.Ellis 3 x) :
    inner ℂ (P.thinKet x A eA (flipDose F 3)) (P.thinKet x B eB U) =
      ∫ p,∫ q,(F.val p:ℂ)*(U.val q:ℂ)* K (usher p q) L := by
  rw [thin_early_change_integral]
  refine (both_integral G
    (weightedMoney F G (P.thinRay x A eA ∘ opposeR 3) ((P.thinRay_cont x A eA).comp (mirrorPose 3)))
    (weightedMoney U G _ (P.thinRay_cont x B eB))).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun p=> integral_congr_ae (Eventually.of_forall fun q=>?_))
  dsimp only [Function.comp_apply]
  rw [thin_scaled G]; by_cases hF : F.val p=0; · rw [hF,Complex.ofReal_zero,zero_mul,zero_mul,zero_mul]
  by_cases hU:U.val q=0; · rw [hU,Complex.ofReal_zero,mul_zero,zero_mul,zero_mul]
  exact congrArg ((F.val p:ℂ)*(U.val q:ℂ)*·) (P.thin_pair_well_price x A eA B eB p q
    (a p (subset_closure hF)) ((zero_add _).symm.trans_lt (b q (subset_closure hU))) J).symm
end
#print axioms thin_kernel
#print axioms thin_contPrice
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
