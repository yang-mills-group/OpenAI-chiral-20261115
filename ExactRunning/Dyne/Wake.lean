import ExactRunning.Dyne.Yacht

/-!
# Identifying the charge

`owns` identifies q with the exact high coefficient (uncut) via
thermal matching. `comparison` identifies the cut version with the
difference of end coefficients, *same* intensive magnetic probe.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace Pylon
variable (E) {D : Latitude}

def kinetic : Law (Entry G) := fun _ => inputSeries E.p E.r
def kineticK := Picture.kin (slots E.B.metric G)

def spent : Law (Entry G) := fun _=> turnSeries E.r.loop
def spentK := Picture.kin (filing E.r)

def kinetic_plays (D : Latitude) :
    Playing D E.kinetic E.kineticK :=
  Picture.plays D (slots_cost E.house E.strip)
    (fun m=> according E.deck
      (low_columns E.paths E.attached (E.floor m) (E.sworn m)).2.2)
    (fun _=> (stain_knit _ _ E.paths).analytic)

lemma kinetic_price (i) : alphaK E.kineticK i=1 := by
  rw [kineticK, Picture.alpha (slots_cost E.house E.strip),alphaPay,tip_fuel i E.strip E.house
    (E.floor 1).starts]
  norm_num

lemma spent_stained (m) : Pointwise (E.spent m) :=
  stain_ink _ E.paths.width E.paths.two (fun i=> (E.paths.invariant i).1)

def spent_plays (D : Latitude) : Playing D E.spent E.spentK :=
  let h := filing_ready _ E.paths
  Picture.plays D (fun i j=> (h.1 i j).1) h.2 (fun _=> (E.spent_stained _).analytic)

lemma spent_price (i) : alphaK E.spentK i=0 :=
  let h := filing_ready _ E.paths
  Picture.alpha_zero (fun i j=> (h.1 i j).1) (fun i j=> (h.1 i j).2) i

lemma spent_ward (D : Latitude) : Lateral D E.spentK LinearMap.id := by
  let h := filing_ready _ E.paths
  have r m := turns_low (m:=m) E.r.loop E.hτ E.paths.two
  have he := withdrew walentes (tendsto_const_nhds (x:=(0:ℝ))) (fun i j=> (h.1 i j).1)
    (fun i=> by rw [mul_zero]; exact h.2 _)
    (fun _=> (E.spent_stained _).analytic)
    (fun _=> (E.spent_stained _).stained)
    (fun _=> (E.spent_stained _).guard)
    (fun _ j ha _=> (rays_jet (E.spent_stained _).analytic _).mp (r _) j ha)
  intro g;exact Picture.lateral D he.wall

end Pylon

namespace BlockTie
variable (X)

theorem owns (i : G.ColorIndex) : X.q = X.hValue (-1) i := by
  -- thermal VS draft
  set D := X.back (-1)
  have e := E.spent_plays D
  have p := I.kinetic_plays D
  have f := I.spent_plays D
  have h := X.re_fare i (X.cargo_song e i) (((p.bare i).smul X.q).add (f.bare i))
  rw [X.cargo_transfer e.score (E.spent_ward _),
      rQuad.add (((p.bare (lo:=0) i).smul X.q).smooth) (f.bare (lo:=0) i).smooth,
      rQuad.weight (p.bare (lo:=0) i).smooth,
      rQuad.mag,rQuad.mag,I.kinetic_price,I.spent_price,E.spent_price,
      add_zero, zero_add,mul_one] at h
  exact h.symm

theorem comparison {r : ℝ} (h : 0<r) (i) :
    X.hValue r i = epValue E.F (X.back r) i - epValue I.F (ridge r) i := by
  have y := Playing.through (E.endpoint.medium (D:=X.back r) h) (E.endpoint.data h)
  have a := X.cargo_transfer y.score (y.ground (fun _=> ep_magnet E _ X.simple h))
  exact eq_sub_of_add_eq (X.balanced h i (X.cargo_song y i) (a _))

end BlockTie
end ExactRunning
