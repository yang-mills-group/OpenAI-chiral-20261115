import Organdy.Rouge
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell


open Roots
variable {P:Spine}{s q k:ℕ}{c:Cuts}{d:Stores}
local notation "N'" =>kitGap P s q
local notation "Y'" => guineas P s
local notation "ι'" => (hueW P.par.R.L Y' * yInvoice c.b)
local notation "W✽" => prismPan P.par.R d.v Y'
local notation "R✽" => shaft P s

variable {I:Type} [LinearOrder I][Fintype I]{N:Side}
lemma parade_force(B:ℕ)(o:I→Site N)
 (b:∀ i j, i≠j → wireG B < separation (o i) (o j))
 {M:ℕ}(q:1≤M):
 Force_M B o M:=by
 unfold wireG at b
 constructor
 · intro i j g
   have a:=b i j (ne_of_apply_ne _ g)
   unfold cape_B
   omega
 intro y
 refine le_trans (Finset.card_le_one.mpr ?_) q
 intro i a j c
 by_contra h
 have u:= b i j h
 have v:=(mem_filter.mp a).2
 have w:=(mem_filter.mp c).2
 rw [separation_comm] at v
 have e: separation (o i) (o j)≤ separation (o i) y + separation y (o j):=separation_triangle _ _ _
 unfold cape_B at *
 omega

lemma garland(t:Seating P c d s q k) (g:1≤d.M) {J:List (Blush (kitGap P s q))}
 (f:J.Pairwise (Safe (shaft P s))) (a:∀ x∈J,Rouge P c s q k x):
 ‖take P s q k ((J.map (fun a=>a.A.x)).prod)‖ ≤ laserRent P.par (2/W✽) (1/2) s N' J.length J.length:=by
  let o (i:Fin J.length):= (J.get i).r
  let A(i:Fin J.length):= (J.get i).A
  let D (i):=(A i).x
  let H (i):=(A i).S
  let O:= node ∘ o
  let C (i):= a _ (J.get_mem i)
  have r (i j:Fin J.length)(g:i≠j): Distant (wireG R✽+1) (H i) (H j):=by
    rcases lt_or_gt_of_ne g with p|p
    · exact List.pairwise_iff_get.mp f i j p
    intro x hx y hy; rw [separation_comm]; exact List.pairwise_iff_get.mp f j i p y hy x hx
 
  have w(i j)(g:i≠j): wireG R✽<separation (O i) (O j):=
    r i j g _ ((C i).wears) _ ((C j).wears)
  choose U V e using fun i=>(C i).fare
  obtain ⟨_,K,l⟩:=ticketBooth (o:=o) (S:=H) (D:=D) P q k s t.reef
    (by rw [t.reef.clearing.radius]; exact parade_force _ _ w g) (U:=U) (V:=V) e
  let L:=List.finRange J.length
  have y : L.Nodup:=List.nodup_finRange _

  let z:ψS O L:= by
    apply y.map
    intro i j h; by_contra g
    have e:=w i j g;rw [h,separation_self] at e;omega
  have u:L.Pairwise (fun i j=>Disjoint (H i) (H j)):=by
    apply y.imp
    intro i j h
    apply Finset.disjoint_left.mpr
    intro x p q
    have a:=r i j h x p x q
    rw [separation_self] at a;omega

  have w₁:L.map D=J.map fun a=>a.A.x:=by
    conv_rhs =>
      arg 2
      rw [← List.ofFn_get J]
    rw [List.ofFn_eq_map,List.map_map]; rfl

  have b:= (l.reading t.fil.kickoff L z u).2.2.2
  rw [w₁, Fintype.card_fin,show L.length=J.length from List.length_finRange] at b
  exact b
#print axioms garland
