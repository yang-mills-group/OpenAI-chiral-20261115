import Organdy.Streamers
import Organdy.Lemon
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

section
variable {n:Side}{s B D:ℕ}
abbrev rp (r:ℕ):Shape:= plane timeAxis (-(r:ℤ))
lemma lengthwise(r:ℕ)(h:4*r<n.val):
 separation (0:Seat n) ((rp r).anon n 0) = 2*r:=by
 let x:=rp r
 let z:=((rp r).motion 0)
 have e: x.anon n 0=wrap (More n) z:=by
   nth_rw 1 [←map_zero (wrap (More n))]
   exact Shape.anno ..
 have p (j:Axis): z j=if timeAxis=j then -(2*(r:ℤ)) else 0:=by
   unfold z rp
   rw [fling_move]
   simp

 have g:Lattice.lift (x.anon n 0)=z:=by
   apply lift_eq_iff.mpr ⟨e,?_⟩
   intro i; rw [p]
   have u:(More n).val=n.val*2:=rfl
   split<;>omega
 rw [separation,zero_sub,pdist_neg]
 change pdist (x.anon n 0)=_
 apply le_antisymm
 · unfold pdist; apply Finset.sup_le; intro j _
   rw [g,p]
   split<;>omega
 have u:=component_le (x.anon n 0) timeAxis
 rw [g,p] at u
 simp only [↓reduceIte] at u
 omega
end

abbrev Coast {n:Side}(B:ℕ)(S:Support (More n)):Prop:=∀ x∈S, separation 0 x≤4*B+6
abbrev drydock (B r:ℕ):Prop:= wireG B + 8*B+40 ≤ r
abbrev sill (r:ℕ) :ℤ:= -(5*(r:ℤ))

lemma inland (j:Axis){B r w:ℕ}(b:drydock B r)(q:10*r≤w):
 boxed j (haloS r (mortise B)) (sill r) w:=by
 have h (x:Cover)(t:x∈ mortise B):
   -((4*B+6:ℕ):ℤ)≤x j ∧ x j≤((4*B+6:ℕ):ℤ):=by
   obtain ⟨a,b⟩:=box_test.mp t
   exact ⟨a _,b _⟩
 unfold haloS sill
 unfold drydock at b
 intro k y
 rcases mem_union.mp y with y|y
 · obtain ⟨x,p,rfl⟩:=mem_image.mp y; specialize h _ p
   rw [fling_move _ _ j]
   split<;>omega
 specialize h _ y;omega

variable {r w:ℕ}

lemma backstage (j:Axis)(p:Seating P c d s q k)
 {e f:Blush (kitGap P s q)}
 (x: Rouge P c s q k e) (y: Rouge P c s q k f)
 (a: Coast (shaft P s) e.A.S) (b: Coast (shaft P s) f.A.S)
 (u:drydock (shaft P s) r)(v:10*r≤w)(l:4*r<(N').val):
 Profiled j w (wireG R✽) (sill r)
    (drew p) (reflMark timeAxis (-(r:ℤ)) e.A.x * f.A.x):=by
 
 let e':= e.spin timeAxis (-(r:ℤ))
 unfold drydock at u
 have y₀:(0:Seat N')=0:=rfl
 let g:= (rp r).anon N' 0
 have z:(separation (0:Seat N') g)=2*r:=lengthwise r l

 have a₀ (x)(v:x∈e'.A.S):separation g x ≤ 4*R✽+6:=by
    obtain ⟨y,e,rfl⟩:=mem_image.mp v
    change separation ((rp r).anon N' 0) ((rp r).anon N' y) ≤_
    unfold rp; rw [←rpt,←rpt,sitT]; exact a y e
 have d₀:Safe R✽ e' f:=by
    intro i j k p
    have h:=separation_triangle g i 0
    have h':=separation_triangle i k 0
    have e:=a₀ i j
    have f:=b _ p
    rw [separation_comm g 0,z] at h;rw [separation_comm 0 k] at f
    omega
 let A:Hookah (kitGap P s q):=
   ⟨e'.A.x*f.A.x,e'.A.S∪f.A.S,0⟩
 have u₁(j):chordy (Lattice.halo (wireG R✽) A.S) j (sill r) w:=by
    intro y r
    obtain ⟨z',h,g'⟩:=halo_spec.mp r
    have E:=separation_triangle (0:Seat N') z' y
    have F:=separation_triangle (0:Seat N') g z'
    rw [show separation 0 y=pdist y from by simp [separation]] at E -- may rw wrong
    unfold sill
    refine ⟨Lattice.lift y j,?_,?_,congrFun (wrap_lift y) j⟩
    all_goals
     have h':=component_le y j
     rcases mem_union.mp h with t|t
     · have d:=a₀ z' t; omega
     have d:=b z' t; omega

 exact ⟨A, ⟨e',f,x.tint p _ _,y,d₀,rfl,rfl⟩,rfl,u₁ j,
   fun i _=>⟨_,u₁ i⟩⟩
