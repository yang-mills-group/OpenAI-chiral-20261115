import Organdy.Crown
import Organdy.Ballyhoo
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


abbrev floral{N:Side}(W:Pane N→ℂ)(z:Seat N)(w:ℕ)(x a:ℝ):Club N:=
 ⟨Broach W z w x a,fun _ h=>h.owner,fun _ _ _ h=>h.reflect ..⟩

/- Prices on all single states (spectrum axis unrestricted, pair on timeAxis). -/
section
variable {N:Side}{m r g:ℕ}{ψ ζ b a:ℝ}{A:Ink (Chip (More N))}
abbrev stair (m r:ℕ):ℤ:= -((2*r:ℕ):ℤ)-4*((m:ℤ)+6)-10
lemma frames (q:10*(2*r+(m+6)+10) ≤g)(j:Axis):
 boxed j (haloS r (mortise m)) (stair m r) g:=by
 have h (x:Cover)(t:x∈ mortise m):
   -((4*m+6:ℕ):ℤ)≤x j ∧ x j≤((4*m+6:ℕ):ℤ):=by
   obtain ⟨a,b⟩:=box_test.mp t
   exact ⟨a _,b _⟩
 unfold haloS stair
 intro k y
 rcases mem_union.mp y with y|y
 · obtain ⟨x,p,rfl⟩:=mem_image.mp y; specialize h _ p
   rw [fling_move _ _ j]
   split<;>omega
 specialize h _ y
 omega

local notation "z" => ice (More N) (2*r)
lemma framed (W:Pane N→ℂ)(d:harbor gaugeRules ζ b ψ)
 (v:Domaine (m+6) ζ (temp ψ) (stow ψ) b W A)
 (q:10*(2*r+(m+6)+10) ≤g)(j:Axis):
 Profiled j g 0 (stair m r) (floral W z (m+6) ψ a)
    (1+(a:ℂ) • planeM W ψ r):=by
 rw [markPlane]
 refine ⟨zoopN _ _ _ _ _,zoom (atHome v d z),rfl,?_,fun i _=>keep q _⟩
 intro y h
 have e:pdist z ≤2*r:=by rw [Optic.ice,pdist_neg]; exact grow _
 obtain ⟨u,f,r₁⟩:=halo_spec.mp h
 obtain ⟨t,b,s⟩:=halo_spec.mp f
 have R:separation 0 t≤2*r:=by
   rcases mem_insert.mp b with k|k
   · simp [k]
   rw [mem_singleton.mp k,separation,zero_sub,pdist_neg];exact e
 have b': separation 0 y≤ 2*r+(m+6)+2:= (separation_triangle 0 u y).trans ((add_le_add ((separation_triangle 0 t u).trans (add_le_add R s)) r₁).trans_eq (by omega))
 rw [separation,zero_sub,pdist_neg] at b'
 have x:=(component_le y j).trans b'
 unfold stair
 exact ⟨Lattice.lift y j,by omega,by omega,congrFun (wrap_lift y) j⟩
end
