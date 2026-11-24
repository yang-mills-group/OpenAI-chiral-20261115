import Organdy.Aisle
import Organdy.Chart
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
namespace Hookah.Rake
open Regis.Head Etch Regis.Head.Garland
open scoped Classical
open Scree

open Organdy Optic Scree Push.Local
-- Bose probes
variable {W:Pane N→ℂ} {z o: Seat N} {s:Signed}{w : ℕ} {x a:ℝ}

open Larva (Domaine Chip)
open Gleam BProof
open Next.Rank.Spindle
open Pressure Worth
variable {A:Organdy.Ink (Chip (More N))}
     {R:Rules SU.group} {ζ b:ℝ}

lemma grow (u:ℕ):pdist (u • (step timeAxis:Site N)) ≤ u :=by
 induction u with
 | zero=> simpa [pdist,Lattice.lift]
 | succ v ih=> rw [succ_nsmul]; exact (pdist_triangle ..).trans (add_le_add ih (pdist_step ..))
lemma keep {u g:ℕ} (p:10*(u+w+10)≤g) (i:Axis):
 cows i (Lattice.halo 0 (hatch w (ice (More N) u))) g:=by
 let z:= ice (More N) u
 refine ⟨-(u:ℤ)-w-2,fun y h=>?_⟩
 have e:pdist z ≤u:=by unfold z Optic.ice; rw [pdist_neg]; exact grow u
 obtain ⟨v,f,r⟩:=halo_spec.mp h
 obtain ⟨t,a,s⟩:=halo_spec.mp f
 have g':separation 0 t≤u:=by
   rcases mem_insert.mp a with k|k
   · simp [k]
   rw [mem_singleton.mp k, separation, zero_sub, pdist_neg]; exact e
 have b: separation 0 y ≤ u+w+2 :=
    (separation_triangle 0 v y).trans ((add_le_add
       ((separation_triangle 0 t v).trans (add_le_add g' s)) r).trans_eq (by omega))
 rw [separation,zero_sub,pdist_neg] at b
 have b':=(component_le y i).trans b
 refine ⟨Lattice.lift y i,by omega,by omega,?_⟩
 exact congrFun (wrap_lift y) i
