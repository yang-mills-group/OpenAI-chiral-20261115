import Gingham.Ruff.Cambric
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


local notation "mₙ"=>momentm P.run iₙ s

variable {o:Cell}{w D:ℕ}{r:Stamp}
variable (h:Secured P.calibration w o D 0 (roost r))
   {l:List (Tile P.calibration)}{L U:Cell}

def Storm (D:ℕ){t:Side}(x y:Site (More t)):=
     2*D≤ separation x y
def StormS (D:ℕ) (t:Side) (x y:Stamp):=
        Storm D (moteRoost t x) (moteRoost t y)
lemma storm_pave {C:Tile P.calibration}
   (b: Transit w o ((V r) (some n)) C)
    (e:Secured K w o D 0 (roost r)):
   ∃ x:Stamp,Shield K w o D C.plot (moteRoost N x)∧
              C.leaf=((V x) (some n)):=by
   induction b with
   | here=>exact ⟨_,⟨_,e,rfl⟩,rfl⟩
   | @turn t g i k ih=>
      obtain ⟨x,a,b⟩:= ih
      refine ⟨_,shield_step a i k,?_⟩
      change Tower.mirror _ _ _ t.leaf =_
      rw [b];rfl


abbrev sheet(P:Spine)(z:ℝ) (f:List Stamp):List (Letter P):= f.map (fun x=>Letter.summon z x)

include h
lemma bed (p:VelourBoard.Deck (momentm P.run (irr P (ν n)) s) w o
     ((V r) (some n)) l L U) :
 ∃ f:List Stamp,
    Representation l=Letter.cost s F (sheet P z f) (some n)∧
    Fill (pitch K w) (Journey.side Y iₙ s).val f.length ∧
    f.length=l.length∧ f.Pairwise (StormS D N):=by
  have e:P.calibration.c (momentm P.run iₙ s)=Journey.side P.run iₙ s:=terrain P.run P.large (P.run.ir iₙ) s
  have x:FitsSide K w N L U:= by rw [←e]; exact p.fits -- defeq?
  letI :Nonempty Stamp:=⟨[]⟩
  have E(x:Tile K): ∃ y:Stamp, x∈l→
     Shield K w o D x.plot (moteRoost N y) ∧ x.leaf=((V y) (some n)):=by
    by_cases h':x∈l
    · obtain ⟨t,a,b⟩:=storm_pave (ν:=ν) z (p.paved.homes x h') h
      exact ⟨t,fun _=>⟨a,b⟩⟩
    exact ⟨[],fun hp=>False.elim (h' hp)⟩
  let g x:=(E x).choose
  refine ⟨l.map g,?_,by rw [←e,List.length_map];exact p.fill,List.length_map _,?_⟩
  · unfold sheet Letter.cost VelourBoard.Representation
    rw [List.map_map,List.map_map]
    apply congrArg (List.prod (α:=Family P.calibration))
    exact List.map_congr_left fun y u=>((E y).choose_spec u).2
  rw [List.pairwise_map]
  exact p.paved.sorted.imp_of_mem
    (fun {a b} i j h=> VelourBoard.separates x (p.paved.places a i)
      (p.paved.places b j) h (((E a).choose_spec i).1) (((E b).choose_spec j).1))


#print axioms bed
omit h
/-- full ray test: all Stamp placements with center spacing including border
    and volume fill. -/
def TestPrice (P:Spine)(a c μ:ℝ)(d:ℕ)(ν:ℕ→ℕ)
      (s w D:ℕ) (z θ:ℝ) :=
   ∀ᶠ n in atTop, ∀ α:Sailing P a c μ d ν s n, ∀ l: List Stamp,
     Fill (pitch P.calibration w) (Journey.side P.run (irr P (ν n)) s).val l.length →
     l.Pairwise (StormS D (Journey.side P.run (irr P (ν n)) s)) →
     ‖Letter.oceanPrice α (sheet P z l)‖≤θ^l.length

include β h
lemma seabed {θ:ℝ}
   (v:salt P s≤D)
   (t:TestPrice P a c μ d ν s w D z θ)
   (b:∀ᶠ n in atTop,Sailing P a c μ d ν s n):
   Settle P.run P.large s P.projection w (fun n=>(V r) (some n)) ν o θ:=by
    filter_upwards [t,b,β.grew.tendsto_atTop.eventually (atHeight P s)]
       with n' x u q l L U p'
    obtain ⟨f,e,t,m,k⟩:=bed (ν:=ν) (F:=F) (n:=n') (L:=L) (U:=U) (l:=l) z h p'
    have g: (sheet P z f).Pairwise (Letter.Ocean u):= by
      rw [sheet,List.pairwise_map]
      exact k.imp (fun e=> avenue u z v e)
    rw [e,←m]
    have y:= x u f t k
    rw [(Letter.shoal β u _ q g).2.2] at y
    exact y

#print axioms seabed


