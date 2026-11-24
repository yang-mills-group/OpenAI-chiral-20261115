import ZecaProng
import ZecaCeviche
import ZecaMirin
import ZecaSpindrift
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



open Hierarchy.Seld.Zeca
open Hierarchy.Seld (parabola)
open OS.Semigroup
open Boundary

local notation "Δr"=> P.jetS
variable (F:P.Nib 3 (P.advocate 3 x 3)) (sc:ℕ→ℂ)(seq:ℕ→ℕ)(d:Vantage)


def Colada:=fun d:Vantage=>Salud z' SU.group (WithLp.toLp 2 d)

/-- UV abscissa cost against fixed pitch d -/
def Orange : ℕ→ℂ→ℂ:=fun i=>
 let r:=seq i
 oceanRun Η (P.kestrelSeed x F sc r) (poseSp 3 (Δr r • d)) (Δr r)

lemma oranges_hot
 (a:P.Bottle 3 (P.advocate 3 x 3) F) (b:P.Ebb x F sc seq):
 Seaward (P.Orange x F sc seq d):=by
 obtain ⟨k,B,q,v⟩:=b
 refine ⟨fun n=>oceanRun_d Η _ _ _ (P.kestrel_scale x F sc a) (P.jetS_pos _),
    2*k, (B^2*2*4^k),by positivity,fun i z p=>?_⟩
 refine le_trans ?_ (deeper q (show 0<z.re from p) k)
 unfold Orange oceanRun
 refine le_trans (norm_inner_le_norm ..) ?_
 rw [OS.Semigroup.unitary,OS.Semigroup.life,mul_div_assoc,←sq]
 have h:=v i _ (half_pos (show 0<z.re from p))
 exact pow_le_pow_left₀ (norm_nonneg _) h _
#check P.cart_tandem
#check P.uses_cart

lemma root_orange
 (p:d 3=0) (b:Pentadose d)
 (h:P.Mach x F sc seq)
 {t:Plume_LocalFieldBounds}(e:P.aboveRoof t):
 atReef (P.Orange x F sc seq d) (Colada d) ↑(2*t.tar):=by
 obtain ⟨q,y⟩:=echolocation t b 0 1
 have y':q.pose=t.pose+d:=by
   rw [y];funext i
   by_cases a:i=3 <;>simp [reecho,a,p]
 have z:q.tar=t.tar:=by simp only [Plume_LocalFieldBounds.tar,y',Pi.add_apply,p,add_zero]
 have a:tendril t q=Aquavit (WithLp.toLp 2 d) (2*t.tar):=by
    apply congrArg (WithLp.toLp 2)
    funext i
    by_cases c:i=3
    · simp [c,y',Plume_LocalFieldBounds.tar,p]; ring
    simp [y',c]
 have r:lyric t q=Colada d ↑(2*t.tar):=by
    rw [lyric,a,sangre _ _ _ (by exact p)
       (mul_pos (by norm_num) t.hot)]
    rfl
 have hb:=h t q e (by unfold aboveRoof;rw [z];exact e)
 rw [r] at hb
 refine hb.congr fun n=>?_
 rw [Orange,oceanRun_real]
 unfold kestrel kestrelRig warpPose
 rw [z,y',smul_add,P.cart_expandwing,P.cart_tandem,P.uses_cart]
#print axioms root_orange
#check Filter.frequently_iff_seq_frequently
#check Filter.Tendsto.frequently
#check tendsto_nhdsWithin_iff

def tipRise (n:ℕ) :=((n:ℝ)+2)
def tipKep (n k:ℕ):Plume_LocalFieldBounds:=
 ⟨k,fun _=>((n:ℤ)+2)*5^k+1,by show 0<((n:ℤ)+2)*5^k+1;positivity⟩
def tipWave (n k:ℕ):ℝ:=tipRise n + (1/5:ℝ)^k
lemma tip_cost(n k:ℕ):(tipKep n k).tar=tipWave n k:=by
 unfold tipKep Plume_LocalFieldBounds.tar Plume_LocalFieldBounds.pose tipWave tipRise; dsimp;push_cast
 rw [div_pow]; field_simp;simp
lemma tip_le (n k:ℕ) : tipRise n<tipWave n k:=lt_add_of_pos_right _ (by positivity:0 < (1/5:ℝ)^k)
lemma tip_go (n:ℕ): Tendsto (tipWave n) atTop (𝓝 (tipRise n)) :=by
 have a:=tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤(1/5:ℝ) by norm_num)
          (by norm_num)
 unfold tipWave; simpa using a.const_add (tipRise n)

lemma oranges_splash
 (a:d 3=0)(b:Pentadose d)(h:P.Mach x F sc seq):
 Splash (P.Orange x F sc seq d) (Colada d):=by
 let n:=P.roof
 let c:ℂ:=↑(2*tipRise n)
 have pc:c∈Inlet:=by change 0<c.re; rw [show c.re=2*tipRise n from rfl]; unfold tipRise; positivity
 refine ⟨salud_hot z' SU.group _, c,pc,?_⟩
 have u: Tendsto (fun k=> ↑(2*tipWave n k):ℕ→ℂ) atTop (𝓝[≠] c):=by
   refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp ((tip_go n).const_mul 2),
        Eventually.of_forall fun k=>?_⟩
   change ¬(↑(2*tipWave n k):ℂ)=c
   exact fun e=> (tip_le n k).ne' (by
      have:=Complex.ofReal_injective e;linarith only[this])
 exact u.frequently (Frequently.of_forall fun k=>by
    rw [←tip_cost]
    apply root_orange P x F sc seq d a b h
    unfold aboveRoof; rw [tip_cost];exact (tip_le n k).le)
#print axioms oranges_splash
