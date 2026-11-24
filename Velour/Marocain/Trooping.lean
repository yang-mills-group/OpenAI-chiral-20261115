
import Velour.Marocain.Curls
import Velour.Marocain.Flush
import Velour.Gathers.Rush
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 110000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "D"=> (Σ₁).muslin
local notation "Φ"=> (Σ₁).Detector
local notation "U"=> (Σ₁).unit.translation
local notation "Ω"=> P.heaven j x



variable {n:ℕ}
local notation "s"=>P.seasons j x
local notation "𝓛" => Fin n → ℝ≥0
local notation "𝒜" => Fin n → P.Bobbin j x
local notation "𝒦" => Fin n → ℕ
local notation "𝓙" => Joint n


def bobMarch (b:𝒜): Fin n→ Φ:= fun i=>P.detects j x (b i)
def plumeMarch (b:𝒜):= fun i=>P.bobQuote j x (b i)

lemma bobToast (b:𝒜): toasted (P.bobMarch j x b):=fun i=>by
 obtain ⟨k,X,p⟩:=(s).cashed (b i).ribbon.cash
 exact ⟨k,X,(b i).ribbon.delivery.common ((s).hatch_welcome p) Filter.EventuallyEq.rfl⟩
def troop (b:𝒜): 𝓛 → 𝓛 → (s).Invitation n:= cortege (P.bobToast j x b)
lemma troop_on (b:𝒜)(l r:𝓛) :
  (s).Invites ((s).roofing (P.bobMarch j x b) l r) (P.troop j x b l r):=
 cortege_on ..

lemma troop_zero (b:𝒜):
  (s).Invites (P.bobMarch j x b) (P.troop j x b 0 0):=
 cortege_base ..



lemma troop_opposite (b:𝒜)(F:Joint n):
  (s).Faces (P.troop j x b 0 0 F)
    (P.troop j x (fun i=>(b i.rev).windBack) 0 0 (OS.Semigroup.tip F)):=
 Invites.facing (u:=fun i=> P.detects j x (b i).windBack)
    (P.troop_zero ..) (P.troop_zero ..) (fun i f=>(b i).op_star f) F

lemma troop_accompanies (b:𝒜)(F:Joint n)(z:E4):
 (s).liftL z * P.troop j x b 0 0 F =
    P.troop j x b 0 0 (ahead (points fun _=>z) F) * (s).liftL z:=
 (P.troop_zero j x b).sways
    (fun y i g=>((b i).ribbon.delivery.translates y g).symm) _ _

lemma troop_price (b:𝒜){l r:𝓛}(u:openAir l)(v:openAir r):
 P.troop j x b l r= (s).banners ((s).fleet (P.plumeMarch j x b) l r):=
 cortege_fleet _ (fun i=> (b i).ribbon.delivery) u v

def follow (b:𝒜)(k:𝒦)(l r:𝓛): (s).Invitation n:=
 (s).banners (fun i=>(b i).quietSlot P j x (k i) (l i) (r i))




theorem march_first (b:𝒜)
 {L J:ℕ→Fin n→ℝ≥0}{l r:𝓛}
 {k:ℕ→Fin n→ℕ}(p:∀a,Tendsto (fun i=>k i a) atTop atTop)
 (e:Tendsto L atTop (𝓝 l))(g:Tendsto J atTop (𝓝 r))
 (u:openAir l)(v:openAir r)
 {V:ℕ→Joint n}{F:Joint n}(t:Tendsto V atTop (𝓝 F)):
 (s).Surges atTop (fun i=>P.follow j x b (k i) (L i) (J i) (V i)) (P.troop j x b l r F):=by
 let c:𝒜:=fun a=> (b a).restring (p a)
 have y: P.troop j x b l r=P.troop j x c l r:=by
    have h:=P.troop_on j x c l r
    have H: P.bobMarch j x c=P.bobMarch j x b:=funext fun a=>(b a).preserved _
    rw [H] at h; exact ((P.troop_on ..).unique h)
 rw [y,P.troop_price j x c u v]
 exact (s).banner_surge
    (p:=fun i a=>(b a).quietSlot P j x (k i a) (L i a) (J i a))
    (fun a=>by
       let w:ℕ→ℝ:= fun i=> ((b a).spool (k i a)).realWidth P j
       have h: Tendsto w atTop (𝓝 0):=(c a).thin j


       have X:=h.add (NNReal.tendsto_coe.mpr (tendsto_pi_nhds.mp e a))
       have Y:=h.add (NNReal.tendsto_coe.mpr (tendsto_pi_nhds.mp g a))
       rw [zero_add] at X Y
       exact ((c a).ribbon.squeeze (u a) (v a) X Y).agree
          (Eventually.of_forall (fun i=>((b a).knocks P j x (k i a) (L i a) (J i a)).symm))) t

lemma march_second (b:𝒜)
 {L J:ℕ→Fin n→ℝ≥0}{l r:𝓛}
 (e:Tendsto L atTop (𝓝 l))(g:Tendsto J atTop (𝓝 r))
 {V:ℕ→Joint n}{F:Joint n}(t:Tendsto V atTop (𝓝 F)):
 (s).Surges atTop (fun i=>P.troop j x b (L i) (J i) (V i)) (P.troop j x b l r F):=
 cortege_removes (P.bobToast j x b) e g t
#print axioms troop_opposite
#print axioms march_first
#print axioms march_second
end Spine

