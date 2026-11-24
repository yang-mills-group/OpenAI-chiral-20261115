import YM.Sextet.Body
import YM.SU5.Cheer.Chapel
import YM.SU5.Aria.Personnel

/-!
# Linearity in the enclave on the buffered positive side; the signal of the difference ticket

Exact identification before and after continuous-sector projection. This is also why taking the
difference **in the source dictionary** retains a price accessible to the spectral zoom law,
without recentering by any family-dependent operator counterterm.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine

private theorem linear_gram {T : Type*} [AddCommGroup T] [Module ℂ T]
    {H:Hilbert} (v:T→H) (B:T→T→ₗ[ℂ]ℂ)
    (h:∀g f, inner ℂ (v g) (v f)=B g f) :
    (∀ f g,v (f+g)=v f+v g) ∧ ∀ (a:ℂ) f, v (a • f)=a • v f := by
  constructor
  · intro f g
    have h (x:T) : inner ℂ (v x) (v (f+g)-(v f+v g))=0 := by simp [h]
    refine sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp ?_)
    rw [inner_sub_left,inner_add_left,h,h,h]; simp
  intro a f
  have h (x:T) : inner ℂ (v x) (v (a • f) - a • v f)=0 := by
    simp [h]
  refine sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp ?_)
  rw [inner_sub_left,inner_smul_left,h,h]; simp

section Linearity
variable (P : Spine) (j : Axis) (x : P.Spectrum0 j) (s : ℕ)

def birthTicket : Submodule ℂ P.Test where
  carrier := setOf (P.birthF j s)
  zero_mem' := ⟨⟨0,(enclave P.calibration).zero_mem⟩,rfl⟩
  add_mem' := by
    rintro _ _ ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨⟨f.val+g.val,add_mem f.property g.property⟩,rfl⟩
  smul_mem' := by
    rintro a _ ⟨f,rfl⟩
    exact ⟨⟨a • f.val,Subalgebra.smul_mem _ f.property a⟩,rfl⟩

def ticketView : P.birthTicket j s →ₗ[ℂ] (P.ColorHil j x).space := by
  let v := fun g : P.birthTicket j s => P.viewF j x s (f:=g.val) g.property
  let B : P.birthTicket j s → P.birthTicket j s →ₗ[ℂ]ℂ := fun g=>
    { toFun := fun f =>P.singleState j s x (P.reflectTest j g.val * f.val)
      map_add' := by intros; simp only [Submodule.coe_add,_root_.mul_add,map_add]
      map_smul' := by intros; simp only [Submodule.coe_smul,_root_.mul_smul_comm,map_smul,RingHom.id_apply] }
  have H := linear_gram (H:=P.ColorHil j x) v B (fun g f=>P.released_gram j x s g.property f.property)
  exact { toFun := v, map_add' := H.1, map_smul' := H.2 }

lemma birthSub {f g:P.Test} (a:P.birthF j s f) (b:P.birthF j s g) : P.birthF j s (f-g) :=
  (P.birthTicket j s).sub_mem a b

lemma sextet_view_sub {f g:P.Test} (a:P.birthF j s f) (b:P.birthF j s g) :
    P.viewF j x s (P.birthSub j s a b)=P.viewF j x s a-P.viewF j x s b := by
  have t:=map_sub (P.ticketView j x s) ⟨f,a⟩ ⟨g,b⟩
  exact t

/-- An arbitrary finite set of price obligations, summed linearly, still produces a
`birthTicket` with Gram identity in the very same realization. One must meet `birthF`
once per nonzero summand, against the full shield width. -/
lemma birth_sum {α:Type*} (f:α→P.Test) (p:∀i,P.birthF j s (f i)) (U:Finset α) :
    P.birthF j s (∑i∈U, f i) :=
  (P.birthTicket j s).sum_mem fun i _=>p i

lemma sextet_view_sum {α:Type*} (f:α→P.Test) (p:∀i,P.birthF j s (f i)) (U:Finset α) :
    P.viewF j x s (P.birth_sum j s _ p U)=∑i∈U, P.viewF j x s (p i) := by
  let F : α→P.birthTicket j s := fun i=>⟨_,p i⟩
  have h : (⟨∑i∈U,f i, P.birth_sum j s _ p U⟩:P.birthTicket j s) = ∑i∈U,F i :=
    Subtype.ext (by simp [F])
  exact (congrArg (P.ticketView j x s) h).trans (map_sum (P.ticketView j x s) F U)
end Linearity

/-! `eq:dark`, part 1. The removed part includes the *entire* zero energy space (spectral
formula later). Do not change realization: the descriptive projection factors through
`P.enter` into the original `ColorHil`. -/
private lemma cloudProjector {j:Axis} {H G:Hilbert} (π:H.space→L[ℂ]G.space)
    (E:OS.Semigroup H j) (E':OS.Semigroup G j)
    (h:∀ t:ℝ≥0,∀ x,π (E.E t x)=E'.E t (π x)) (ω:G)
    (w:∀ t:ℝ≥0,E'.E t ω=ω) (t:ℝ≥0) (y y':H) (x:G) (a:ℂ)
    (he:y'=y-E.E t y) (hy:π y=x+a • ω) :
    π y'=x-E'.E t x := by
  rw [he,map_sub,h,hy,map_add,map_smul,w]
  abel

variable (P : Spine) (x : P.Spectrum0 3) (Z : Lead.Clan) (s n:ℕ)
local notation "ξ" => P.advocate 3 x 3
local notation "E" => P.physicalEnergy 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "π" => P.wealth 3 ξ

def sourceVector : (P.ColorHil 3 ξ).space :=
  P.viewF 3 ξ s (P.timeDifference_birth Z s n)

def macroVector := (π) (P.sourceVector x Z s n)

theorem sourceVector_formula :
    P.sourceVector x Z s n =
      P.shard x Z s n - (E).E (P.advanceHeat s n) (P.shard x Z s n) := by
  let u:= P.brightC Z s n
  exact (P.sextet_view_sub 3 ξ s u (P.passesLater 3 s (P.timeJump n) u)).trans
    (congrArg ((P.shard x Z s n)-·) (P.releasedLater 3 ξ s (P.timeJump n) u))

theorem macroVector_formula :
    P.macroVector x Z s n =
      P.birthCloud x Z s n - (S).E (P.advanceHeat s n) (P.birthCloud x Z s n) :=
  cloudProjector (π) (E) (S) (P.bankHeat 3 ξ) (P.heaven 3 ξ) (P.heaven_hot 3 ξ)
    (P.advanceHeat s n) _ _ _ _ (P.sourceVector_formula x Z s n) (P.halo_split ..)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
