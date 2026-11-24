import Organdy.Gliss
import Organdy.Freestyle
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU Tulip Lat
open Vale Buffered
open Swell Hom

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine) (i k t:ℕ)
local notation "Λ"=>P.par
local notation "x'"=> Vale.hat (Λ).R.L (Λ).x t
local notation "N'"=> age P.run i t
local notation "KL"=> (P.run.voyage i).CapeT t
local notation "R✤"=>RootBook P.run i k t
local notation "p'" => (R✤).p
local notation "q'" => (Λ).J.n
local notation "h'" => (Λ).h

variable (s:Sweep (age P.run i t))
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single N'
local notation "Fz"=> FC (Dwell N')
local notation "⚓"=> Spire.arum T B₁ D₁ (mateK N')
local notation "θ"=> sailQ B₁ D₁ T
local notation "ι₁"=> suit_Y s


section
variable (g:Sweep n)(x:Orbit n)

lemma outback : yellA g (yellA g⁻¹ x)=x:=
   Prod.ext (by change flashA g (flashA g⁻¹ _) = _; rw [lights,inv_mul_cancel,rev1]) (by
    simpa using (tuftT g⁻¹ x.2))

lemma toback : yellA g⁻¹ (yellA g x)=x:= Prod.ext (revB ..) (tuftT ..)

lemma yodelTags (h:Injective (priorP x.2)):
    Injective (priorP (yellA g x).2):=
  h.comp (boxA g).injective

lemma whirlJ (V:Bag n):
    ∑ i:Aura n, whirlB g V i (yellA g x)=roll g (∑ i:Aura n,V i x):=by
  symm
  rw [map_sum]
  exact sum_equiv (moldA g) (by simp) fun i _=>by
     change roll _ _=roll _ (V ((moldA _).symm _) _)
     rw [Equiv.symm_apply_apply,toback]

lemma voltaT (V:phy n):
    voltaU g V (yellA g x)=Hive.teen g (V x):=by unfold voltaU;rw [toback]
end

variable (u:Holidays P i k t)
include u
lemma relays {V:phy (age P.run i t)} {D:Bag (age P.run i t)}
    (h:smoothRide P i k t V D):
    smoothRide P i k t (voltaU s V) (whirlB s D):=by
 intro x g y
 obtain ⟨v,f,rfl⟩:∃ v:Orbit N',Injective (priorP v.2)∧yellA s v=x:=
     ⟨yellA s⁻¹ x,yodelTags s⁻¹ x g,outback s x⟩
 obtain ⟨z,rfl⟩:=sailOnto B₁ D₁ T y
 let A:= ∑ i:Aura N',D i v
 have hp: barefoot P i k t v (acts A z)=acts (V v) (barefoot P i k t v z):=by
   have hv:=h v f z
   rw [covered,covered,map_smul] at hv
   let a:=Complex.exp ((RootBook P.run i k t).betaL ((P.run.voyage i).CapeT t) v)
   have t:=congrArg (a⁻¹ • ·) hv
   rw [show Complex.exp _=a from rfl, inv_smul_smul₀ (show a ≠ 0 from Complex.exp_ne_zero _), inv_smul_smul₀ (show a≠0 from Complex.exp_ne_zero _)] at t
   exact t
 have d:=congrArg ⚓ hp
 rw [Spire.arum_act,liftsStage P i k t s u v f,liftsStage P i k t s u v f,sail_move] at d
 rw [covered,covered,map_smul,voltaT,whirlJ]
 exact congrArg (_ • ·) d
