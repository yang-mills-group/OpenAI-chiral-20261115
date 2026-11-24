import Bay.D.Cake
import Bay.Deck.Stage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Py Py.Rate LocalLimit Preparation Papal
open Vale clocks


variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
  (s i k:ℕ)
local notation "z"=>hat P.R.L P.x s
local notation "Pe"=>P.V.L.mood (Y.uv k-s)
local notation "PiM"=>P.V.L.tied (Y.uv k-s)
local notation "n"=>count Y s i
local notation "N"=>More (count Y s i)
local notation "Gx"=>gram Y s i k
abbrev Lease {R:Type}[NormedAddCommGroup R][NormedSpace ℝ R][MeasurableSpace R][BorelSpace R]
    (o d:Site N)(F:Yn N R)(W:Chalk N R):=
 Candle Pe PiM (Gx).p z (Gx).beta o d F W
abbrev beans(W:Chalk N ℝ):=flavor Pe PiM W

theorem ivory:
 ∀ᶠ s in atTop, ∀ (i k:ℕ), s≤Y.uv k →
   ∀ {I:Type} [Fintype I] (o d:Site (More (count Y s i))) (gs:I→Kite (More (count Y s i)))(F:Yn (More (count Y s i)) ℝ)(W:Chalk (More (count Y s i)) ℝ),
   Lease Y s i k o d F W → Packed gs o d →
   ∀ (b:ℝ), |b|≤ thetaB (hat P.R.L P.x s) →
   ∀ {m:Side}(G:Ratio m (More (count Y s i))), Portal G (hat P.R.L P.x s) P.R.L →
   VisiblePolar Y s i k 1 b
      (Fintype.card I*(b*beans Y s i k W + titheB (hat P.R.L P.x s))) G (gusts gs F):= by
 filter_upwards [(stage_slope P.V P.x).eventually waveBurn,
    (stage_slope P.V P.x).eventually (slip P.R.L)] with s v t i k l I _ o d gs F W y h b j m G q
 change Ion _ _ _ _ _ _ _ _ _ _ _ _ _ at y
 have he:= (prices_plot Y s i k l).1
 have hp:(gram Y s i k).p.B= clocks.height (hat P.R.L P.x s):=he ▸ (Y.meter.boot s).2.1
 refine ⟨y.gust_env gs,fun a=>?_⟩
 let J:= fun c=>(⟨a,0⟩: Kite (More (count Y s i)))*gs c
 have hi:Packed J o d:=packed_shift h _
 intro f; have hg:f=gusts J F:=funext fun V=> gusts_shift gs ⟨a,0⟩ F V
 rw[hg]
 let U:ℝ:=Fintype.card I
 let Q:=U*(|b| * Ei (hat P.R.L P.x s))
 let TC:=U*(b*beans Y s i k W)
 refine ⟨y.gust_scale J,picks J W,U*Ni (hat P.R.L P.x s),Li (hat P.R.L P.x s)*Real.sqrt U,Q,y.gust_fine J,
 
  y.gust_arc J,y.gust_lip J hi,?_,?_⟩
 · have hv: panorama Y s i k b (picks J W)=TC:=
     y.gust_fee J ((P.V.L.roof (Y.uv k-s)).2.1 _)
           ((P.V.L.roof (Y.uv k-s)).2.2 _) b
   rw[hv]
   have hu:0≤U:=Nat.cast_nonneg _
   rw[mul_pow (Li (hat P.R.L P.x s)),Real.sq_sqrt hu]
   calc _= TC+ U * (|b| *Ei (hat P.R.L P.x s) + Regis.trend *Li (hat P.R.L P.x s)^2*b^2):=by unfold Q;ring
        _≤ TC+ U * titheB (hat P.R.L P.x s):= add_le_add le_rfl (mul_le_mul_of_nonneg_left (tithe_le y _ j) hu)
        _ = _:= (mul_add ..).symm
 intro α T
 rw [←hp,one_mul]
 have hv: |b| * (Mi (hat P.R.L P.x s) + Ni (hat P.R.L P.x s)) ≤1:=(mul_le_mul_of_nonneg_right j (add_nonneg y.perks.1 y.perks.2.1)).trans v
 exact y.gust_foot G hv hi q.odd (by rw [hp];exact t _ q.span) α T _
end YM.CF.Bay.D
