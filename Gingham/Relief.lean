import Gingham.Color
import YM.SU5.Registration.Rise.EntireCanvas
/-!
# A finite budget approach to the divergence purchase

Emphasis *positive budgets*. Suppose one pays the activated height
of (128), even with tolerances instead of limits of the participating
coefficients. At one fixed appointment under the election, gauge and
matter channels must already be earned. Attribute parts to field
prices `Weight` (gauge coefficient, supported by any estimate of
the error **against a continuum field realization**, e.g., near
saturation from a microscopic Gram calculation in a one-dimensional
sector after field transport). The axial costs use only
`Braid`: some scalars and spatial poses, *current* prices also at
positive heat. Time displacement can be paid simply by using that
field at accordingly different positive heat. There's no need to
take the challenging derivative limit of (128) or even assert that
this is transporting a divergence *equation* to the continuum. Though
(134) is highly relevant to other goals!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

open SatinRegistration
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "ω₁"=> P.heaven 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "𝓢"=> P.seasons 3 ξ
local notation "T"=> (𝓢).E
local notation "V"=> P.cartage 3 ξ
local notation "D"=> (𝓢).muslin
local notation "Ω"=> P.firstTulle 3 ξ

local notation "𝓟"=> toll P x

abbrev nugget (d:ℝ≥0)(b:P.Apron): G :=
   jut ω₁ (P.stageG 3 ξ b d d)

/-- Ward stamp split or any exact linear identity at a height where
it's a literal one in P.Test (also allow parts from earlier heights,
via promotion). Clearance includes whole apron. -/
structure Plaque {ι:Type}
    (D0:P.Apron)(I:Finset ι)(A:ι→P.Apron)(rate:ι→ℂ)(d:ℝ≥0): Prop where
  arrives:∀i∈I,(A i).s≤D0.s
  gather:D0.F=∑ i∈I, rate i • (A i).full P D0.s
  covers:∀i∈I, (A i).allowance P 3 ≤ D0.allowance P 3
  paid:D0.allowance P 3 < d

section
variable {ι:Type}{D0:P.Apron}{I:Finset ι}{A:ι→P.Apron}{rate:ι→ℂ}{d:ℝ≥0}

lemma plaque_signal (z: Plaque P D0 I A rate d):
    nugget P x d D0 = ∑ i∈I, rate i • nugget P x d (A i) := by
  have v: P.stageG 3 ξ D0 d d=∑ i∈I,rate i • P.stageG 3 ξ (A i) d d:=by
     unfold stageG
     rw [P.canvasing (3:Axis) ξ A rate I D0 D0.s z.arrives rfl z.gather z.covers d d
           z.paid.le z.paid.le,map_sum]
     simp only [map_smul]
  let f : (G).Op→ₗ[ℂ](G).space := {
    toFun:= jut ω₁
    map_add':=by
       intro a b
       rw [jut,jut,jut,shred,shred,shred,_root_.add_apply,
         inner_add_right, add_smul]; abel
    map_smul':=by
       intro c a
       simp [RingHom.id_apply,jut,shred,inner_smul_right,smul_sub,smul_smul]
  }
  show f (P.stageG 3 ξ D0 d d)= ∑ i∈I, rate i • f (P.stageG 3 ξ (A i) d d)
  simp only [v,map_sum,map_smul]

end


abbrev Braid {J:Type}(m:J→Hook P x):=
   Submodule.span ℂ (hearsay 𝓢 ω₁ (𝓟 ∘ m))
abbrev gauged (g:Hook P x)(d:ℝ≥0):= jut ω₁ (𝓟 g d)

/-- Budget at a height. Terms at right of
Y = Z + (currents with poses) can themselves be approximated (within
cost on vacuum vectors priced directly). `grope`, `wrinkle`
permit independently budgeting the entire Ward price and each stamp's
approximation. The use here of a strict bound with the G norm at
fixed pad is suited to approximation of a **nonzero line**; its inputs
must afford that, not just a microscopic test.
-/
structure PressProxy {J ι : Type}(g: Hook P x)(m:J→ Hook P x)
    (D0:P.Apron)(I:Finset ι)(A:ι→P.Apron)(rate:ι→ℂ)(d:ℝ≥0)
    (c:ι→ℂ)(r:ι→ℝ)(R:ℝ):Prop where
  base:Plaque P D0 I A rate d
  grope:‖nugget P x d D0‖≤ R
  wrinkle:∀i∈I,∃v∈Braid P x m,
    ‖nugget P x d (A i) - (c i • gauged P x g d + v)‖ ≤ r i
  caught:R + (∑ i∈I, ‖rate i‖ * r i) <
      ‖∑ i∈I, rate i * c i‖ * ‖gauged P x g d‖


theorem proxy_signal {J ι : Type}(g: Hook P x)(m:J→ Hook P x)
    {D0:P.Apron}{I:Finset ι}{A:ι→P.Apron}{rate:ι→ℂ}{d:ℝ≥0}
    {c:ι→ℂ}{r:ι→ℝ}{R:ℝ}
    (p:PressProxy P x g m D0 I A rate d c r R) :
    mistrial 𝓢 ω₁ (𝓟 g) (𝓟 ∘ m):=by
  classical
  let r0:=∑ i∈I, ‖rate i‖ * r i
  let y:=nugget P x d
  let X:=gauged P x g d
  let z:=∑ i∈I, rate i * c i
  have s (i): ∃v∈Braid P x m,
      i∈I→ ‖y (A i) - (c i • X + v)‖ ≤ r i:=by
     by_cases h:i∈I
     · obtain ⟨v,t,u⟩:=p.wrinkle i h
       exact ⟨v,t,fun _=>u⟩
     exact ⟨_,(Braid P x m).zero_mem,fun k=> (h k).elim⟩
  choose w b a using s
  let l:=∑ i∈I, rate i • w i
  have e : ‖ y D0 - (z • X+l)‖ ≤ r0:= by
     unfold r0 l z y
     rw [plaque_signal P x p.base,Finset.sum_smul,←Finset.sum_add_distrib,
       ←Finset.sum_sub_distrib]
     refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i k=>?_))
     rw [← smul_smul,← smul_add, ← smul_sub,norm_smul]
     exact mul_le_mul_of_nonneg_left (a i k) (norm_nonneg _)

  have e': ‖z • X+l‖ < ‖z‖ * ‖X‖ := by
     refine lt_of_le_of_lt ?_ p.caught
     calc _ = ‖y D0 - (y D0 - (z • X+l))‖ := by rw [sub_sub_cancel]
          _ ≤ _ := (norm_sub_le ..).trans (add_le_add p.grope e)
  have j:0< ‖z‖:=by
     by_contra! h
     have := (mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg X))
     exact not_lt_of_ge this ((norm_nonneg _).trans_lt e')
  have nz:z≠0:= norm_pos_iff.mp j
  have e : l∈ Braid P x m:= (Braid P x m).sum_mem fun i _=>(Braid P x m).smul_mem _ (b i)
  refine ⟨d,(show (0:ℝ≥0) ≤ D0.allowance P 3 from bot_le).trans_lt p.base.paid,_, (Braid P x m).neg_mem
     ((Braid P x m).smul_mem z⁻¹ e),?_⟩
  change ‖X - -(z⁻¹ • l)‖ < ‖X‖
  refine lt_of_mul_lt_mul_left ?_ j.le
  rw [← norm_smul z,sub_neg_eq_add,smul_add,smul_smul,mul_inv_cancel₀ nz,one_smul]
  exact e'




/-- Application. Any one sufficiently funded Ward appointment
buys a joint assessment and placements with real sector operands even
exposing in the coupled theory the non-product test, not a raw-label
interpretation. -/
theorem infer_stress (e:P.Ellis 3 x) {J ι : Type}(g: Hook P x)
    (t:clean P x true g)
    (m:J→ Hook P x)(v:∀i,clean P x false (m i))
    {D0:P.Apron}{I:Finset ι}{A:ι→P.Apron}{rate:ι→ℂ}{d:ℝ≥0}
    {c:ι→ℂ}{r:ι→ℝ}{R:ℝ}
    (p:PressProxy P x g m D0 I A rate d c r R) :
    ∃ a δ i, IntrinsicTwo P x a (g.west P x) (m i) δ :=
   div_income P x g e t m v (proxy_signal P x g m p)

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

