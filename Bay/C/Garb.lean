import Bay.C.Mint
import Bay.C.Raygun
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Lor Py.Rate.BScale Push.Uniform
open Pressure SectorNext.Remainder Nor
open Push.AbsoluteSums Trees Roots
open BPress (NPL PL lscale lscale_late lscale_one)
local notation "VΔ" => Buffered.Afterglow.Tower.VacuumSelection.Spine
open Salt SU Swell QuadClock Mew Vow.TreasuryFog
open BProof.Bide

variable {w:Berth}{a b c:ℝ}{x:Site w.side}{o:Seat w.side}{m t:ℕ}{f:w.First}

open D hiding quiver
open Carol Zephyr.Chern

structure Outfit where
  a:ℝ
  c:ℝ
  b:ℝ
  F:ℝ→ℝ
  m:ℕ
  D:ℝ
  r:ℝ
  T:ℝ
  e:ℝ
abbrev tY(P:VΔ)(g:Outfit):=till129 P g.a g.c g.b g.m
abbrev dY(P:VΔ)(g:Outfit):=reserve129 P g.a g.c g.b g.m
abbrev Duo(P:VΔ)(g:Outfit):ℝ→ℝ:=fun x=>
 |quoteJ P g.a g.b g.c x|+|quoteZ g.b g.D g.T x|

abbrev Funds(P:VΔ)(g:Outfit)(t:ℕ):ℝ→ℝ:=fun x=>|tY P g x|+(meltZ t x * Duo P g x)*pinpr P.par.R.L x

abbrev Dosage(P:VΔ)(g:Outfit)(t:ℕ):ℝ→ℝ:=fun x=>|dY P g x|+meltZ t x * Duo P g x
abbrev Year(P:VΔ)(g:Outfit)(M L t:ℕ):=icedCost P M L g.F (Dosage P g t)
abbrev σq(w:Berth)(g:Outfit)(t:ℕ):=(Grant w (Funds w.P g t) (Dosage w.P g t))

structure FleetX(w:Berth)(g:Outfit)(M L t:ℕ):Prop where
 prop:w.Rig g.a g.c g.m
 tall:w.Tall
 fuel:∃r,w.Thermal M L g.F (Funds w.P g t) (Dosage w.P g t) r
 haul: Canal w g.a g.D g.r g.T g.e

variable {g:Outfit}{M L:ℕ}

namespace FleetX

def OrderT (w:Berth)(g:Outfit)(t:ℕ)(x:Site w.side)(o:Seat w.side)(f:w.First)
 (v: Sour.Bag w.side)
 (J: Axis→Sour.Bag w.side) : Prop :=
 σq w g t (seam w x o f g.m g.b v) ∧
 (∀ i,σq w g t (mineJ w x o f i g.b t (J i))) ∧
 σq w g t (mineX w x o f g.b g.D g.T t) ∧
 ∀i y, (watch (reverseCab (y-x)) (mineJ w x o f i g.b t (J i))).shown=
    ((meltZ t w.x):ℂ) • w.Jpose x f i y

variable (q:FleetX w g M L t)
include q

lemma order (u:w.Before g.a g.b g.m x f) (k:o∈ grooveB 24 w.p (node x))
 {v:Sour.Bag w.side}
 (h:w.WearY g.m x f g.a g.c g.b v):
  ∃J,OrderT w g t x o f v J:=by
 choose Z hh using fun i=>givenJ q.prop u q.tall i t k
 let q₀:=Duo w.P g w.x
 have d:0≤q₀:= add_nonneg (abs_nonneg _) (abs_nonneg _)
 let z:=meltZ t w.x
 have z0:= (show 0<z from meltPos ..).le
 have e:lamCoal w.P g.a g.b g.c t w.x ≤z*q₀:=mul_le_mul_of_nonneg_left
   ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))) z0
 have y:lamRuby g.b g.D g.T t w.x ≤z*q₀:=mul_le_mul_of_nonneg_left
   ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))) z0
 have qp:=q.prop.qq.le
 refine ⟨Z,(seamL q.prop q.tall h k).bigger q.prop ?_ ?_,fun i=>(hh i).bigger q.prop ?_ ?_,(givenZ q.haul q.prop u q.tall _ k).bigger q.prop ?_ ?_, fun i y=> seatsJ q.prop u i y⟩
 · exact (le_abs_self _).trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg z0 d) qp))
 · exact (le_abs_self _).trans (le_add_of_nonneg_right (mul_nonneg z0 d))
 · exact (mul_le_mul_of_nonneg_right e qp).trans (le_add_of_nonneg_left (abs_nonneg _))
 · exact e.trans (le_add_of_nonneg_left (abs_nonneg _))
 · exact (mul_le_mul_of_nonneg_right y qp).trans (le_add_of_nonneg_left (abs_nonneg _))
 exact y.trans (le_add_of_nonneg_left (abs_nonneg _))

variable {S:SealV w.side}
lemma sweeping (h:σq w g t S)(θ)(v:Velvet θ):σq w g t (watch θ S):=
 h.watchful q.prop _ v

lemma pins {s:ℕ}(h:σq w g t S)(u:1≤M)(v:w.lampCap ≤ s):
 ∃U V,Dons w (soloS w S) L s (Year w.P g M L t w.x) U V∧
     Native w S L s (twinB U V 0):=by
 obtain ⟨_,z⟩:=q.fuel
 exact nativeRoot z q.prop q.tall u h v


lemma quay {I:Type}[LinearOrder I][Fintype I]{s:ℕ}
 (T:I→SealV w.side)(d:w.GaugeBill M (gr T))
 (z:∀i,σq w g t (T i))(l:w.lampCap ≤ s):
 ∃U V,Dons w T L s (Year w.P g M L t w.x) U V:=by
 obtain ⟨_,r⟩:= q.fuel
 exact licensing r q.prop q.tall d z l
end FleetX

structure Helm (P:VΔ)(g:Outfit):Prop where
 Dp:0<g.D
 Tp:0<g.T
 ready : ∀n:ℕ, ∀ᶠ t in atTop,
   NPL (Funds P g t) ∧ HopsRate P.par.R (Dosage P g t) n ∧
   ∀M L:ℕ, WaitZ P.par.R (powZ n) (Year P g M L t) ∧
   Dry P (fun w=>w.Rig g.a g.c g.m → FleetX w g M L t)

lemma plabs{f:ℝ→ℝ}(h:PL f): PL (fun x=>|f x|):= h.mono (Eventually.of_forall fun i=> by rw [abs_abs])
lemma nabs{f:ℝ→ℝ}(h:NPL f): NPL (fun x=>|f x|):= h.mono (Eventually.of_forall fun i=> by rw [abs_abs])

theorem pattern {P:VΔ}(F:ℝ→ℝ)(I:Ice P F)
 (q:NPL (till129 P a c b m))(h:NPL (reserve129 P a c b m))
 (p:0<a):
 ∃ D r T e, Helm P ⟨a,c,b,F,m,D,r,T,e⟩:=by
 obtain ⟨D,r,T,e,f,i,k⟩:=aqueduct P _ p
 let g:Outfit:=⟨a,c,b,F,m,D,r,T,e⟩

 have v:PL (Duo P g):= (plabs (quoteP _ _ _ _)).add (plabs (quoteZP _ _ _))
 have w(t):NPL (Funds P g t):= (nabs q).add (((meltPL _).mul v).times (chill_iff.mp (Till.cool_q P.par.R)))
 refine ⟨D,r,T,e,f,i,fun n=>?_⟩
 filter_upwards [slope P.par.R n (nabs h) v] with t y
 refine ⟨w _,y,fun M L=>?_⟩
 let R:= runoff M L n I (w t) y
 refine ⟨R.rate,?_⟩
 filter_upwards [k,R.ready,
   (Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop 20] with s l hq z
 filter_upwards [l,hq] with i v u k hk r
 let w:=takeUp P s i k
 have tall:20≤(takeUp P s i k).p.B:=r.sizeB.symm ▸ z
 exact ⟨r,tall,u _ hk (Berth.readyRails r),v k hk _ _ r⟩
