import Lucent.Singers
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

set_option maxHeartbeats 380000
set_option linter.unusedSimpArgs false
open YM.Stationary (Gaia)
open Onyx Kea Flare Dial Ballad.Twah Cordial Emu Gist
open Regis Circuit
variable {I:Type}(Y:I→Role)
namespace Arity

open Stencil
structure Tariff (L:List I)(d:ℕ)(S:Stencil I):Prop where
   unveil(t):t∈S.out→ t.flash.map Prod.fst=L
   degree:S.degree L.length d
namespace Tariff
lemma atom (F:List (Tint I))(X:List (Loop I)): Tariff (F.map Prod.fst) X.length (mono F X):=
    ⟨fun t p=>by rw [List.mem_singleton.mp p]; rfl,(by rw [List.length_map]; exact mono_grade _ _)⟩
variable {L R:List I}{m n:ℕ}{S T:Stencil I}
lemma scale (p:Tariff L m S)(a:ℂ): Tariff L m (a • S):=by
 refine ⟨fun t v=>?_,degree.scale p.degree a⟩; change t∈S.out.map _ at v; obtain ⟨b,h,rfl⟩:=List.mem_map.mp v; exact p.unveil b h
lemma pool {α:Type*}[Fintype α](f:α→Stencil I)(h:∀ i,Tariff L m (f i)):
    Tariff L m (pack univ f):=by
 refine ⟨fun t v=>?_,degree.pack _ _ fun i _=>(h i).degree⟩
 obtain ⟨b,c,d⟩:= List.mem_flatMap.mp v; exact (h b).unveil _ d
lemma card (i:I)(F:List (Tint I))(X:Op Slot):Tariff (F.map Prod.fst) 1 (beaded F i X):=by unfold beaded; exact pool _ fun a=>pool _ fun b=> scale (atom F [(i,a,b)]) _ -- (atom F [..])

lemma v_fee (i:I): Tariff [i] 1 (V i):=pool _ fun p=>card i [(i,p)] _
lemma g_fee(u v:I):Tariff [u,v] 0 (G u v):=pool _ fun p=>atom [(u,p),(v,p)] []
lemma d_fee(k:I)(z:Window.Family):Tariff [] 1 (D z k):=card k [] _
lemma paid (p:Tariff L m S)(q:Tariff R n T) : Tariff (L++R) (m+n) (S*T):=by
 constructor
 · intro b h; change b∈S.out.flatMap _ at h; obtain ⟨a,g,h'⟩:=List.mem_flatMap.mp h
   obtain ⟨c,d,rfl⟩:=List.mem_map.mp h'
   change (a.flash++c.flash).map _=_; rw [List.map_append,p.unveil _ g,q.unveil _ d]
 rw [List.length_append]; exact degree.mul p.degree q.degree
lemma due [Fintype I](p:Tariff L m S)(x:FieldPlan I)(g:L.Pairwise (fun i j=>(x.hands i).p ≠ (x.hands j).p)): Dusty x S:=by
 intro b c; rw [← p.unveil b c, List.pairwise_map] at g; exact g
