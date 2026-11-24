import ZecaEider
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster





open _root_.YM.ZecaSky


variable
  (F:P.Nib 3 (P.advocate 3 x 3))
  (c:ℕ→ℂ)
section
variable (h:P.Bottle 3 (P.advocate 3 x 3) F)
variable (p a:Plume_LocalFieldBounds) (d:a.tar+1≤p.tar)
variable (y:P.ontoRoof a)
include d h y
lemma stern_vel:
 ∀ᶠ r:ℕ in atTop,
 ‖P.kestrel x F c p r - P.zecaStern x p F c f r‖≤
 P.curlCost f r * ‖P.zecaStern x a F c f r‖:=by
 filter_upwards [P.at_half (f:=f)] with r e
 let t:=P.mWarp f r a
 let v:=P.mWarp f r p
 let w:=P.jetS r*p.tar
 let δ:=P.jetS r
 have htw:t+δ≤v:=by
   have ht:=mul_le_mul_of_nonneg_left d (P.jetS_pos r).le
   unfold t δ v mWarp
   linarith only [e,ht]
 have hd:w-v= (P.granPos f r [] 3):=by unfold w v mWarp; ring
 have h':=P.kestrel_speed (r:=r) x F c h t w v δ (P.stern_hot a y e) (P.jetS_pos r)
      (htw.trans (show v≤w from sub_le_self _ P.fly_time_stem)) htw
 rw [hd,abs_of_nonneg P.fly_time_stem] at h'
 unfold zecaStern kestrel kestrelRig
 rw [← map_sub,P.cart_norm,P.cart_norm]
 exact h'

variable {seq:ℕ→ℕ}
lemma zecaBow (e:Tendsto seq atTop atTop)
 {B:ℝ}(b:∀ᶠ i:ℕ in atTop, ‖P.zecaStern x a F c f (seq i)‖≤B):
 Tendsto (fun i=> ‖P.kestrel x F c p (seq i) - P.zecaStern x p F c f (seq i)‖)
 atTop (𝓝 0):=by
 have h':=((P.curl_go (f:=f)).comp e).mul_const B
 rw [zero_mul] at h'
 apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ h'
 filter_upwards [e.eventually (P.stern_vel (f:=f) x F c h p a d y),b] with i t hb
 exact t.trans (mul_le_mul_of_nonneg_left hb
    (mul_nonneg (div_nonneg (by norm_num) (P.jetS_pos _).le) P.fly_time_stem))
end

variable {err:ℕ→ℝ} (n:P.Nick f x F c err) (g:Tendsto err atTop (𝓝 0))
   (W₀:5∣P.par.R.L.val)(J:P.Ellis 3 x)
   {seq:ℕ→ℕ}(T:P.Nepenthe seq x) (y:P.Umber x seq)
   (h:P.Bottle 3 (P.advocate 3 x 3) (P.twinNib 3 (P.advocate 3 x 3) F))
include n g W₀ J T y h
local notation "F'"=>P.twinNib 3 ξ F
lemma stern_comparison (p:Plume_LocalFieldBounds)(hp:P.aboveRoof p):
 Neighbor
   (P.kestrel x F' (star c) p ∘ seq) (fun i=> P.plover x f (seq i) p):=by
 let a:Plume_LocalFieldBounds:=⟨0,fun _ => (P.roof:ℤ)+1, by
   change (0:ℤ)<(P.roof:ℤ)+1; positivity⟩
 have ha:a.tar=P.roof+1:=by
    change ((↑((P.roof:ℤ)+1):ℝ)/5^(0:ℕ))=(P.roof:ℝ)+1
    push_cast; simp
 have h₂:P.ontoRoof a:= ha.ge
 unfold aboveRoof at hp
 have h₀:P.ontoRoof p:= by unfold ontoRoof;linarith only [hp]
 have d:a.tar+1≤p.tar:= by linarith only [hp,ha]
 obtain ⟨B,e⟩:=fam_gramBound (P.plover_gram (f:=f) x a a W₀ T J)
 have z:=(P.stern_nick x a F c h₂ n g y.sky).trans (P.white_mates (f:=f) x a W₀ y)

 refine Neighbor.trans ?_
    (Neighbor.trans (P.stern_nick x p F c h₀ n g y.sky) (P.white_mates (f:=f) x p W₀ y))
 exact P.zecaBow (f:=f) x F' _ h p a d h₂ y.sky (Neighbor.bounded z e)
lemma mach_star: P.Mach x F' (star c) seq:= by
 intro p q u v
 obtain ⟨B,e⟩:=fam_gramBound (P.plover_gram (f:=f) x p p W₀ T J)
 obtain ⟨C,z⟩:=fam_gramBound (P.plover_gram (f:=f) x q q W₀ T J)
 exact Neighbor.pairs (P.stern_comparison x F c n g W₀ J T y h p u)
    (P.stern_comparison x F c n g W₀ J T y h q v) e z (P.plover_gram x p q W₀ T J)
#print axioms mach_star
