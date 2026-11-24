import Gingham.Ruff.Bedding
import YM.SU5.Registration.Rise.Handling
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s

variable {P a c μ d s}
    {ν:ℕ→ℕ}{F:ℕ→Fleece P.calibration}(β:Lander P a c μ d ν F)
set_option linter.unusedSectionVars false
open Footlight

variable {n:ℕ}(α:Sailing P a c μ d ν s n)

local notation "iₙ"=>irr P (ν n)
local notation "kₙ"=>uvv P (ν n)
local notation "N"=>Journey.side P.run iₙ s
local notation "Rₙ"=>RootBook P.run iₙ kₙ s
local notation "Aₙ"=> (P.run.voyage iₙ).CapeT s
local notation "Δ"=>denZ Rₙ P.par.U Aₙ
local notation "𝒢"=>Scree.city N
local notation "χ"=>partitionZ Rₙ P.par.U Aₙ
local notation "𝒳"=>fun f:Family P.calibration=>exhibit Y P.large s iₙ f


open VelourBoard
namespace VoyageB_Board
variable (z:ℝ)
local notation "𝕊"r:max=>Letter.summon (P:=P) z r
local notation "V"r:max=> Letter.bill s F (𝕊 r)


variable (r:Stamp)
include β
def Hilt (β:Lander P a c μ d ν F)(s:ℕ)(z:ℝ)(r:Stamp):P.Test:=
    ⟨Letter.bill s F (.summon z r) none, (marque K).mpr (aux_test ((Letter.admission β s (.summon z r)).landing))⟩
lemma whichcase (w:ℕ)(o:Cell)
    (e: VelourBoard.Parcel P.calibration w o 0 (Letter.scope s (𝕊 r)))
    (j:Axis)(p:o j=0):
   P.InCase j s w (Hilt β s z r):=by
   have a:= (β.promenade s r z).1
   refine InCase.sized P j s w ((enclave_spec _).mpr (a.pays none).2.1)
      (Letter.admission β s (𝕊 r)).landing ?_
   specialize e j
   unfold Wall at e
   simp only [Pi.zero_apply,p,mul_zero,zero_add,mul_one] at e
   exact e

#check IcePath
lemma crystal
   (ice:IcePath P.run (irr P) (uvv P))
   {θ:ℝ} {w D:ℕ} (v:salt P s≤D) (p:0<w) (q:0<θ)
   (t:TestPrice P a c μ d ν s w D z θ)
   (b:∀ᶠ n in atTop,Sailing P a c μ d ν s n)
   {o:Cell}(h:Secured K w o D 0 (roost r))
   (j:Axis)(e:o j=0) :
    ∃ u:P.InCase j s w (Hilt β s z r),
       ‖P.Box j s w p u.card‖≤4*θ∧
       ∀x:P.Spectrum0 j, ‖u.charges x p‖≤4*θ:=by

    let S:=Letter.scope s (𝕊 r)
    have E:=scudding v h z
    let u:=whichcase β z r w o E j e
    have H:‖P.Box j s w p u.card‖≤4*θ:= by
      have a: BQueue S (fun n=>(V r) (some n)) u.card.val.val:=by
         rw [show u.card.val.val=(V r) none from
           congrArg (fun f:P.Test=>f.val) u.entry]
         exact Letter.admission β s _
      exact boardPrice P.run P.large P.law s P.projection j w _ S _
        β.grew.tendsto_atTop o ice E e p θ q (seabed β z h v t b)
        (P.room j) u.card a
    exact ⟨u,H,fun x=>(u.cap x p).trans H⟩

#print axioms crystal


omit β
/-- violent convenience: clearance demanded in edge units, choose passages
    of at least that many ticks. -/
def transport (P:Spine) (j:Axis)(D:ℕ): Stamp :=
    [(j,gaugeT P.calibration D),(j,0)]
def horizon (j:Axis)(D:ℕ):Cell:=fun k => if k=j then 0 else -(D:ℤ)
lemma harbor (P:Spine)(j:Axis)(D:ℕ):Secured P.calibration (D+D) (horizon j D) D 0
    (roost (transport P j D)):=by
 intro i
 rw [transport,roost_step,roost_step,fling_move,fling_move,
   roost_nil]
 unfold Wall horizon
 have b: (1:ℤ)≤ ruler P.calibration.B:=by have v:=ruler_gene P.calibration.B; omega
 have c:=ruler_offset P.calibration (↑D)
 have g:D≤ ruler P.calibration.B * (↑D):=
    le_mul_of_one_le_left (by positivity) b
 by_cases t:j=i
 · subst i
   simp only [Pi.zero_apply, mul_zero, zero_add, mul_one, neg_zero, if_true]
   push_cast
   constructor <;> linarith
 simp only [t,Ne.symm t,Pi.zero_apply,mul_zero, zero_add,add_zero,mul_one,if_false]
 push_cast
 constructor <;> linarith


include β
abbrev tissues (P:Spine)(s:ℕ) (F:ℕ→Fleece P.calibration)(z:ℝ):=
   wingtip (z:ℂ) (F s) none

lemma dock
   (ice:IcePath P.run (irr P) (uvv P))
   {θ:ℝ} {D:ℕ} (v:salt P s≤D) (p:0<D+D) (q:0<θ)
   (t:TestPrice P a c μ d ν s (D+D) D z θ)
   (b:∀ᶠ n in atTop,Sailing P a c μ d ν s n)
   (j:Axis) :
    (Hilt β s z (transport P j D)).val=
      relocate P.calibration j D (tissues P s F z) ∧
    ∃ u:P.InCase j s (D+D) (Hilt β s z (transport P j D)),
       ‖P.Box j s _ p u.card‖≤4*θ∧
       ∀x:P.Spectrum0 j, ‖u.charges x p‖≤4*θ:=
   ⟨rfl,crystal β z _ ice v p q t b (harbor P j D) j (if_pos rfl)⟩

#print axioms dock

