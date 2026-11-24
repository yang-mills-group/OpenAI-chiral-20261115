import SatinPP.AzureLight

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ" j:max => P.advocate 3 x j
local notation "K₁" j:max => P.ManyF j (P.advocate 3 x j)
local notation "Π'" j:max=>P.wealth j (P.advocate 3 x j)
local notation "Sh"=>Shrine (P.houses x)
local notation "W"=>P.socials x
local notation "ω"=>P.lights x

open Hierarchy.Seld Silk
section
variable {H:Hilbert}{j:Axis}{S:OS.Semigroup H j}{A:Stamp H}{B:H.Op}{d:ℕ}(K:Silk.Role S d A B)

include K
lemma return_Wire {f:ℕ→ℝ}
   (p:Tendsto f atTop (𝓝 0))(q:∀i,0<f i):
   Land.Wot (fun i=>Silk.Wrap S d (A (f i) (f i))) B:=by
 simp_rw [K.wear _ _ (q _) (q _)]
 refine ⟨⟨‖B‖,Eventually.of_forall fun i=> jacket_cost ..⟩,fun x y=>?_⟩
 have h:Tendsto (fun i=>(f i).toNNReal) atTop (𝓝 0):=by simpa using! continuous_real_toNNReal.continuousAt.tendsto.comp p
 have z(x:H):Tendsto (fun i=>S.E (f i).toNNReal x) atTop (𝓝 x):=by
    have a:= (S.continuousE x).continuousAt.tendsto.comp h
    rw [S.eZero] at a;exact a
 have u:= (z x).inner (𝕜:=ℂ) (B.continuous.continuousAt.tendsto.comp (z y))
 refine u.congr ?_; intro i
 exact S.swing ..
end
-- Widths to 0 via spacings
variable {x}{P}{A:ℕ→P.Apron}{B:ℝ}{D:P.Concert x}


variable (C:P.ConcertPlays x A B D)(l:List Axis)
local notation "h'" j:max=>P.seats j x (D j l)
/-- Rectangular dress at all axes at fixed size. -/
def tabs (D:P.Concert x)(l:List Axis)(a:ℝ≥0):Sh:=
  -- binder shadow problem!
  ⟨fun _=>a,fun j=>P.seats j x (D j l) a a⟩
include C
lemma tabs_in (a:ℝ≥0)(u:0<a):tabs D l a ∈ P.Cathedral x:=by
 let U:=P.Lore x
 let Z:=tabs D l a
 let Y:ℕ→Sh:=fun i=>P.allot x ((A i).pivot P l) (fun _=>a)
 have w(j:Axis):∀ᶠ i in atTop, ((A i).pivot P l).realWidth P j≤a:=
    (C.bought.price j l _ (lt_min zero_lt_one (show (0:ℝ)<a from u)) (min_le_left ..)).mono fun i t=>
       (Apron.pivot_w _ ..).le.trans (t.1.le.trans (min_le_right ..))
 refine ⟨Y,(eventually_all.mpr w|>.filter_mono final_reels).mono
    (fun i h=>⟨_,h,rfl⟩), ⟨fun _=> tendsto_const_nhds,fun j=>?_⟩⟩
 have h:=P.seating_Limited j x (C.provides j l a a u u)
 obtain ⟨c,_,k⟩:=h.uniform
 exact ⟨⟨c,k⟩,h.confirms⟩


/-- Celerity field, from Painted Elections. -/
structure Moonlight (D:P.Concert x)(l:List Axis)(T:Sh):Prop where
 thin : T.t=0
 centered(j:Axis):Silk.Role (W j) 6 (P.seats j x (D j l)) (T.f j)
 buys:T∈Magic W (P.Cathedral x) 6
lemma card_moons : ∃ T:Sh,Moonlight D l T:=by
 have a(j:Axis):∃Y,Role (W j) 6 (h' j) Y:=role_exists _ (P.seats_paid j x (C.paid j l))
 choose Y u using a
 let f(i:ℕ):ℝ:=1/(i+1)
 have p(i):0<f i:=by unfold f;positivity
 let g(i):ℝ≥0:=⟨f i,(p i).le⟩
 have t:Tendsto f atTop (𝓝 0):=tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
 refine ⟨⟨0,Y⟩,rfl,u,(fun i=>armor W 6 (tabs D l (g i))),
    fun i=>⟨_,tabs_in C l _ (show 0<g i from p i), rfl⟩,
    ⟨fun _=>NNReal.tendsto_coe.mp t,fun j=>return_Wire (u j) t p⟩⟩
#print axioms card_moons
