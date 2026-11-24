import ZecaSceptre
import ZecaStage
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


variable {P x N A Y}{n:ℕ}
    (q:P.Ellis 3 x) (l:P.Regalia x N A Y)
    (M:Axis→List (Fin n))(p:Points n)(u:Fin n→N.Chip)
    (v:ℕ→Fin n→Vantage)
    (h:∀i,Tendsto (fun k=>v k i) atTop (𝓝 (atPosition p i)))
    (e:p∈ Dai.debut n M)

include l h e

lemma fits_up:∀ᶠ k in atTop, ∀j:Axis,P.Turnstile j (P.Sched x N Y u k) (M j) (v k):=
 eventually_all.mpr fun j=>
   (P.memorial_quote j _ ((coin (K:=Kₑ) N A j) ∘ u)
       (P.Sched x N Y u) (atPosition p) v
        (fun i=>l.buys _ (u i)) h _ (e j).2).1
#print axioms fits_up

omit h
def enamel (P:Spine)(x:P.Spectrum0 3){n:ℕ}
   (M:Axis→List (Fin n))
   (Y:Fin n→P.Apron)(t:ℕ)(d:Fin n → Cover): ℂ:=
  P.singleState 3 t x (P.fullScroll t Y d (M 3))

include q
lemma mint (t:ℕ→ℕ)(d:ℕ→Fin n → Cover)
    (b:∀k i,(Y (u i) k).s ≤ t k)
    (h:∀i,Tendsto (fun k=>P.gridSpot (t k) (d k i)) atTop (𝓝 (atPosition p i))):
 Tendsto (fun k=>P.enamel x M (P.Sched x N Y u k) (t k) (d k)) atTop
    (𝓝 (evaluate (K:=Kₑ) p Wₑ N ωₑ A u (M 3) 3)):= by
  let v k := P.gridSpot (t k) ∘ d k
  rw [←coronet (L:=M 3) _ _ _ _ 3 p _ (e 3).2]
  refine (reigning q l 3 p u (M 3) _ (.refl _) v h (e 3).2).congr' ?_
  exact (fits_up l M p u v h e).mono fun k s=>
       (P.spot_full _ _ _ _ q _ (fun i _=>b k i) (s 3)
              ⟨fun j=>⟨M j,(e 3).1.trans (e j).1.symm,s j⟩⟩).symm

#print axioms mint
#print Plenum
