import Gingham.Ruff.Argent
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



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false

namespace Regalia
variable {S:Finset Cover}{A:Cluster P.calibration}
 {ν:ℕ→ℕ}{w:ℕ}{o:Cell}{j:Axis}
local notation "Λ"=>Regalia P ρ s ν S
variable (r:Regalia P ρ s ν S A q)

def ticket (r:Regalia P ρ s ν S A q):P.Test:=
 inLeaf r.queue.landing
lemma sash 
 (g:Tendsto ν atTop atTop)
 (frost:IcePath P.run (irr P) (uvv P))
 (h:∀ᶠ e:ℕ in atTop,Patina P ρ s (irr P e) (uvv P e))
 (p:Parcel P.calibration w o 0 S)(u:o j=0)(x:0<w):
    ∃a:P.InCase j s w r.ticket,
       ‖P.Box j s w x a.card‖ ≤ CoinPrice P s w q ∧
       ∀z:P.Spectrum0 j, ‖a.charges z x‖ ≤ CoinPrice P s w q :=by
  have hz(d:ℝ)(y:0<d): ∃a:P.InCase j s w r.ticket,
       ‖P.Box j s w x a.card‖≤CoinPrice P s w (q+d):=by
       have t:= r.raise (le_add_of_nonneg_right y.le)
       obtain ⟨a,h,_⟩:= gilding g h t.late (add_pos_of_nonneg_of_pos r.pos y) p r.queue j u x frost r.legal
       exact ⟨a,h⟩
  obtain ⟨a,_⟩:=hz 1 one_pos

  have e : ‖P.Box j s w x a.card‖ ≤ CoinPrice P s w q:=by
     have k:Continuous (fun t:ℝ=>CoinPrice P s w (q+t)):= by unfold CoinPrice RegisterPrice; fun_prop
     let l:= nhdsWithin (0:ℝ) (Set.Ioi 0)
     haveI:NeBot l := by unfold l; infer_instance
     apply ge_of_tendsto (
        show Tendsto (fun d:ℝ=>CoinPrice P s w (q+d)) l
                    (𝓝 (CoinPrice P s w q)) from
         (by simpa only [ContinuousWithinAt,add_zero] using k.continuousWithinAt (x:=0) (s:=Set.Ioi (0:ℝ))))
     filter_upwards [show Set.Ioi 0∈l from self_mem_nhdsWithin] with t g
     exact (hz t g).choose_spec -- proof irrelevance
  exact ⟨a,e,fun z=>(a.cap z x).trans e⟩
#print axioms sash

#check stage_slope

open BProof Pressure.Worth 
#check r_meter
#print r_meter
open Pressure
#check radiusB
#check coin
#check coin_budget
#check stage_slope
#check turnover


end Regalia
open BProof Pressure
def notch(P:Spine)(s:ℕ):ℝ:=
    BProof.coin (hat P.par.R.L P.par.x s) (1/6000) 0 0

lemma smallSeams (P:Spine)(d:ℝ)(u:0<d):
 ∀ᶠ s in atTop, ∀w:ℕ, (w:ℝ)≤notch P s→ Fee P s w ≤d:=by
 let B:ℝ:=32*(P.par.block.val)
 have v:=Pays.compare d u (Pays.scale 14 (Pays.times (Pays.whole r_meter 0 0)
     (Pays.pot (Pays.scale B (Pays.whole (1/6000) 0 0)) 4)))
     (Or.inl (show _<(0:ℝ) from (by unfold r_meter; norm_num)) : Earlier _ _ _ 0 0 0)
 filter_upwards [(turnover P.par).eventually v] with s t w e
 simp only [coin_zero,mul_one] at t
 rw [show Fee P s w=14*(meterC (hat P.par.R.L P.par.x s)*(B*w)^4) from
     (by unfold Fee B; ring)]
 unfold notch at e
 have ht: 0≤B:=by unfold B; positivity
 refine le_trans ?_ ((le_abs_self _).trans t)
 unfold meterC
 have h:=coin_pos (hat P.par.R.L P.par.x s) r_meter 0 0
 gcongr
#check Pays.rising


-- purchases any polynomial width in b
lemma tallLaces(P:Spine)(d:ℝ)(l:ℕ):
 ∀ᶠ s in atTop, d*(1+(radiusB (hat P.par.R.L P.par.x s):ℝ))^l ≤ notch P s:=by
 have a:=Pays.plus (Pays.merit (Pays.constant 1) (Or.inr (Or.inr
      (show ((0:ℝ)=0 ∧ (0:ℝ)=0 ∧ (0:ℝ)<2) from ⟨rfl,rfl,by norm_num⟩)))) Pays.rising
 exact (turnover P.par).eventually (Pays.leap (Pays.scale d (Pays.pot a l))
      (Or.inl (show (0:ℝ)*l<1/6000 from by norm_num)))
#print axioms smallSeams

