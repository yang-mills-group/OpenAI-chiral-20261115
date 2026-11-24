import Organdy.Rehearsal
import Organdy.Voe
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU Tulip Lat
open Roots
open Vale Buffered QuadClock Neon MeasureTheory
open Swell Hom

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine) (i k t:ℕ)
local notation "Λ"=>P.par
local notation "x'"=> Vale.hat (Λ).R.L (Λ).x t
local notation "N'"=> age P.run i t
local notation "KL"=> (P.run.voyage i).CapeT t
local notation "R✤"=>RootBook P.run i k t
local notation "p'" => (R✤).p
local notation "q'" => (Λ).J.n
local notation "h'" => (Λ).h

variable (s:Sweep (age P.run i t))


open BProof.Bide Py.Rate.BScale

abbrev moveFare (g:ℝ→ℝ)(x:ℝ):=uplift 6 * g x

lemma stored {v:Bag n} {A:Support (More n)} {r:ℝ}
    (w:Barrage p q A h v r a b):stale v:=by
 obtain ⟨u,z,x,_⟩:=w.price
 exact fun i g=>Chord.keys_of_chord (Chord.full ((x i).tube.body g))

variable {a' b':ℝ} {w m:ℕ}
 {o o':Site (age P.run i t)} {f g:ℝ→ℝ}
 {J J':Axis→SOp (age P.run i t)}{X Y:SOp (age P.run i t)}{v:Bag (age P.run i t)}

local notation "C"=> Coral (Λ).R.L x' KL p' o J X m
local notation "hue"=> hueW (Λ).R.L x'
local notation "U"=> ((hue:ℂ) • puffLine KL p' o J X m)
local notation "A"=> moveFare f x'
local notation "B"=> moveFare (scaledBirth P g) x'
variable (z:Tide P i k t m w a' b')(u:Agate P i k t m o a b f g J J' X Y v)

include z u
lemma moveTicket (r:Earlier s o o'):
    Barrage p' q' {node o'} h' (whirlB s v) (highLaunch p') A B:=by
 rw [show highLaunch p'=rScale p' by unfold highLaunch rScale biscuit;rw [z.strobe,div_eq_mul_inv]]
 have h:= u.glare.also s
 rw [z.orderP] at h

  -- prices agree because q
 have he:(boxA s).symm (node o)=node o':=(boxA s).symm_apply_eq.mpr r.symm
 have hv:node o∈grooveB 24 p' (node o):=halo_subset _ _ (mem_singleton_self _)
 exact joinsRoot (he ▸ (show (boxA s).symm (node o) ∈ actY s (grooveB 24 p' (node o)) from mem_map_of_mem _ hv)) h

lemma posed0 (e:0≤b):
   Guided P i k t o (Porch p' o) C U v (hue*yInvoice b) A B:=by
 have lens:smoothRide P i k t U v:=fun z _ x =>u.toSquid.flight.science ..
 have w₁:= coralSpring P i k t o z.hPos.le e z.strobe u.toSquid
 have ht:=moveTicket P i k t 1 z u (earlier_id _)
 rw [unspun v (stored u.glare.toBarrage)] at ht
 exact ⟨⟨⟨_,u.toSquid.appointment,lens⟩,w₁.plus,ht⟩, u.toSquid.appointment,lens⟩

lemma posed (e:0≤b)(r:t≤P.run.uv k)(g_:Earlier s o o'):
   Guided P i k t o' (actY s (Porch p' o)) (voltaM s C)
     (voltaU s U) (whirlB s v) (hue*yInvoice b) A B:=by
 have w₁:=posed0 P i k t z u e
 have z₁:=cymbalMoves s w₁.glow
 have y:=relays P i k t s (floats P i k t r) w₁.wire
 exact ⟨⟨⟨_,z₁,y⟩,w₁.plus,moveTicket P i k t s z u g_⟩, z₁,y⟩
end YM.CF.Organdy
