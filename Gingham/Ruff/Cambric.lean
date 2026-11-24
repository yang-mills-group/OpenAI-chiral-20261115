import Velour.Board.Relate
import Velour.Board.Birth
import Gingham.Ruff.Flagship
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
abbrev Stamp := List (Axis×ℤ)


def roost (x:Stamp):Cover:= (maidS x).motion 0
lemma roost_nil:roost []=0:= by
 change (incX 1).motion 0=0
 simp [incX,Shape.motion]

lemma roost_step(i:Axis)(k:ℤ)(x:Stamp):
   roost ((i,k)::x)=(plane i k).motion (roost x):=
     Nacre.palm .. -- ?
def moteRoost(t:Side)(x:Stamp):=wrap (More t) (roost x)
lemma shield_step {t:Side}{Z: Calibration}{w:ℕ}{o A:Cell}{d:ℕ}{x:Stamp}
  (e:Shield Z w o d A (moteRoost t x))
  (j:Axis)(k:ℤ) : Shield Z w o d (tipped j k A)
      (moteRoost t ((j,PaneCut Z w o j k)::x)):= by
  unfold moteRoost
  rw [roost_step,←Shape.anno]
  exact turned j k _ e

lemma plot_hook (t:Side)(g:BudgetPoint)(x:Stamp):
    GarlandBook.Pall g (maidS x) t=halo (2*g.B) {moteRoost t x}:=by
 change hoop (finale (maidS x) 0) _=_
 rw [hoop,bouton_finale, moteRoost,roost,←Shape.anno,map_zero,
     show bouton (0:Site t)=0 by rw [bouton,←Ratio.root_embed,map_zero]]


lemma plot_shapeB {p:BudgetPoint}{Z:Calibration}
   (x:Stamp){i:Cover}
   (h:i∈CF.Gingham.Ruff.stage x (frond Z p))
   (j:Axis): |i j - roost x j|≤((p.B:ℤ)+8+16*Z.B.val):=by
   induction x generalizing i with
   | nil=>
      change i∈ore _ 0 at h
      rw [ore_mem,sub_zero,box_test] at h
      rw [roost_nil,Pi.zero_apply,sub_zero, abs_le]
      have a:=h.1 j;have b:=h.2 j
      constructor
      · exact_mod_cast a
      exact_mod_cast b
   | cons a t ih =>
      obtain ⟨d,g⟩:=a
      -- reflect_stays: i j = if j=d
      obtain ⟨u,a,w⟩:=reflect_stays d g (CF.Gingham.Ruff.stage t (frond Z p)) h
      have m:=ih a
      rw [roost_step,fling_move,w j]
      by_cases f:j=d
      · subst j;simp only [ite_true]; rw [abs_le] at *
        constructor <;> linarith only [m.1,m.2]
      rw [if_neg f,if_neg (Ne.symm f)]; exact m

#check reflect_stays
#check halo_spec


def salt (P:Spine)(s:ℕ):ℕ:=
   3*(P.run.meter.a s).B+8+16*P.par.block.val+P.calibration.ℓ

variable {w:ℕ}{o:Cell}
lemma scudding {r:Stamp}{D:ℕ}
   (v:salt P s≤D)
   (sec:Secured K w o D 0 (roost r))
   (z:ℝ):
   Parcel K w o 0 (Letter.scope s (.summon (P:=P) z r)):=by
   intro j i h
   specialize sec j
   have t:=plot_shapeB (Z:=P.calibration) r (p:=P.run.meter.a s) h j
   rw [abs_le] at t
   rw [show P.calibration.B=P.par.block from rfl] at t
   unfold salt at v
   omega

lemma avenue (z:ℝ){D:ℕ}
   (v:salt P s ≤ D) {r t:Stamp}
   (e:2*D≤ separation (moteRoost N r) (moteRoost N t)):
   Letter.Ocean α (.summon z r) (.summon z t):=by
  let A:=moteRoost N r;let B:=moteRoost N t
  change Disjoint (GarlandBook.Pall _ _ _) (GarlandBook.Pall _ _ _)
  rw [plot_hook,plot_hook,Finset.disjoint_left]
  intro x a b
  obtain ⟨y,m,c⟩:=Lattice.halo_spec.mp a
  obtain ⟨u,m',f⟩:=Lattice.halo_spec.mp b
  obtain rfl:= Finset.mem_singleton.mp m
  obtain rfl:= Finset.mem_singleton.mp m'


  have hp:(Rₙ).p = ~p~ s:=
    (((P.run.voyage iₙ).X (P.run.uv kₙ)).pull.owns s α.ok.le).width.symm
  rw [hp] at c f
  have g:=separation_triangle (moteRoost N r) x (moteRoost N t)
  rw [separation_comm] at f
  unfold salt at v
  omega

