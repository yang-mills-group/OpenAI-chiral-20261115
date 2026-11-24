import ZecaGait
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)


open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola)

open DoseTravel Set


open Hierarchy.Seld.Poin Hierarchy.Seld.Zeca.Monument
open Boundary
variable {ι:Type}(N:P.Tent x ι)


open Hierarchy.Seld.Zeca.Gilt
open Hierarchy.Seld.Poin.Gem Hierarchy.Seld.Poin.Galleon
-- careful Ambiguous Spot, Job, beam
variable (A:P.Shiver x N)(Y:N.Chip→ℕ→P.Apron)
local notation "Wₑ"=> P.Centripetal x
local notation "ωₑ"=>P.Sphere x
local notation "Kₑ"=>P.Retinue x


variable {n:ℕ}(M:Axis→List (Fin n))
 (u:Fin n→ι)(w:Galleon.Palette (K:=P.Retinue x) N u)
 (b:SpaceAxis)(p:Points n)(t:ℝ)

open Dai

abbrev Salary (k:ℕ)(j:Dai.Job n):Fin n→P.Apron:=
 P.Sched x N Y (Dai.race (K:=Kₑ) N u w b t j) k

/-- One placement choice: shared pitch within all patient jobs paying at k. -/
structure Livery where
 pitch:ℕ→ℕ
 cover:ℕ→Dai.Job n → Fin n → Cover
 fee:(∀k j i,(P.Salary x N Y u w b t k j i).s ≤ pitch k)
 exact_pose:∀j i,Tendsto (fun k=>P.gridSpot (pitch k) (cover k j i)) atTop
               (𝓝 (atPosition (Dai.room b p t j) i))


lemma livery : Nonempty (P.Livery x N Y u w b p t):=by
  choose d hd using (fun j i=>P.spot_seek (atPosition (Dai.room b p t j) i))
  let r (k:ℕ)(ji:Dai.Job n × Fin n):=(P.Salary x N Y u w b t k ji.1 ji.2).s
  let h k:= max k (Finset.univ.sup (r k))
  have c:Tendsto h atTop atTop:=tendsto_atTop_mono (f:=id) (g:=h) (fun k=>le_max_left k _) tendsto_id
  exact ⟨⟨h,fun k j i=>d j i (h k),fun k j i=>
     le_trans (Finset.le_sup (f:=r k) (mem_univ (j,i))) (le_max_right ..),
     fun j i=>(hd j i).comp c⟩⟩

def stirUp (L:P.Livery x N Y u w b p t)(k:ℕ) : ℂ :=
 Dai.beam b p (fun j=>P.enamel x M (P.Salary x N Y u w b t k j) (L.pitch k) (L.cover k j))

#print axioms livery

variable {P x N A Y}
lemma stiff (q:P.Ellis 3 x)(l:P.Regalia x N A Y)
   (L:P.Livery x N Y u w b p t)
   (d:∀j,Dai.room b p t j ∈ debut n M):
 Tendsto (P.stirUp x N Y M u w b p t L)
    atTop (𝓝 (blush (K:=Kₑ) Wₑ N ωₑ A u w b p t)):=by
 rw [ballast]
 refine ((beam_c b p).tendsto (x:=Buoy (K:=Kₑ) Wₑ N ωₑ A u w b p t) |>.comp
    (f:=fun k j=>P.enamel x M (P.Salary x N Y u w b t k j) (L.pitch k) (L.cover k j))
    (tendsto_pi_nhds.mpr (fun j=>?_)))
 rw [show Buoy (K:=Kₑ) Wₑ N ωₑ A u w b p t j = _ from
      Galleon.honor (K:=Kₑ) Wₑ N ωₑ A _ _ _ _ _ (d j 3)]
 exact mint q l M (Dai.room b p t j)
        (Dai.race (K:=Kₑ) N u w b t j)
        (d j) L.pitch (fun k=>L.cover k j) (fun k i=>L.fee k j i)
        (L.exact_pose j)
#print axioms stiff
