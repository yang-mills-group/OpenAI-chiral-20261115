import Bay.Socket
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


open Buffered
variable {N:Side} {S T:footprint N}
 {c d:ℝ}{f h:Stencil N}{g y:phy N}

lemma Fits.oneF (S:footprint N):Fits S 1 (1:Stencil N):=
 ⟨AtSupport.oneM _,fun _ _=>(map_one _).symm,fun _=>norm_one.le⟩

lemma Fits.mulF (p:Fits S c f)(q:Fits S d h):Fits S (c*d) (f*h):=
 ⟨p.basis.mulM q.basis, fun _ _=>
   (congrArg₂ (α:=FC (Single N)) (β:=FC (Single N)) (·*·) (p.paid _ _) (q.paid _ _)).trans (map_mul _ _ _).symm, 
   fun t=>(norm_mul_le ..).trans (mul_le_mul (p.purse _) (q.purse _) (norm_nonneg _) ((norm_nonneg _).trans (p.purse t)))⟩

lemma commute0 {i j:FC (Single N)}(p:Sector (modesIn N S) false i)(q:Sector (modesIn N T) false j)(h:Disjoint S T):Commute i j:=by
 have d:Disjoint (modesIn N S) (modesIn N T):= disjoint_left.mpr fun _ g v=>disjoint_left.mp h (modes_ch.mp g) (modes_ch.mp v)
 change i*j=j*i
 rw [Sector.apart p q d];simp [Sector.grainB]
namespace Accompanies

lemma oneF(S:footprint N):Accompanies S 1 1 1:=⟨Fits.oneF _,fun _=>Sector.one,fun _=>rfl⟩


lemma mulF (p:Accompanies S c f g)(q:Accompanies T d h y)(t:Disjoint S T):Accompanies (S∪T) (c*d) (f*h) (g*y):=by
 let a:=p.enlarge (subset_union_left (s₂:=T))
 let b:=q.enlarge (subset_union_right (s₁:=S))
 refine ⟨a.pay.mulF b.pay,fun x=>(a.lives x).mul (b.lives x),fun x=>?_⟩
 have s:Sector (modesIn N S) false (f x.1):=(p.pay.basis.allV (x.1,x.1)).sector
 simp only [Pi.mul_apply]
 rw [star_mul,act_mul,p.mate,←act_mul,←star_mul,(commute0 s (q.lives x) t).eq, star_mul,act_mul,q.mate,←act_mul,←star_mul]
 have r:Sector (modesIn N T) false (h x.1):=(q.pay.basis.allV (x.1,x.1)).sector
 rw [(commute0 s r t).eq]
end Accompanies

-- list of supporters
variable {I:Type} (l:List I)
def stair (S:I→footprint N):footprint N:=(l.map S).foldr (· ∪ ·) ∅

lemma enterStair (A:footprint N)(W:I→footprint N)(
  z:∀i∈l,Disjoint A (W i)):Disjoint A (stair l W):= by
 induction l with
 | nil=> simp [stair]
 | cons i l v=>
   rw[List.forall_mem_cons] at z
   change Disjoint _ (_∪stair _ _)
   exact disjoint_union_right.mpr ⟨z.1, v z.2⟩

section
variable {A:I→footprint N}{C:I→ℝ}
  {m:I→Stencil N}{o:I→phy N}
  (p:∀i,Accompanies (A i) (C i) (m i) (o i))
abbrev independent (A:I→footprint N):Prop:= l.Pairwise (fun i j=>Disjoint (A i) (A j))

include p
lemma march (h:independent l A): Accompanies (stair l A)
 ((l.map C).prod) ((l.map m).prod) ((l.map o).prod):=by
 induction l with
 | nil=>exact Accompanies.oneF _
 | cons i l v=>
   obtain ⟨r,w⟩:=List.pairwise_cons.mp h
   exact (p i).mulF (v w) (enterStair l _ _ r)

lemma reorg (h:independent l A)(u:Orbit N):
  l.Pairwise (fun i j=>Commute (o i u) (o j u)):= h.imp fun {i j}=>commute0 ((p i).lives u) ((p j).lives u)
end

lemma collapsed (u:Orbit N)(o:I→phy N):
  (l.map o).prod u=(l.map (fun i=>o i u)).prod:= by induction l <;> simp_all
end YM.CF.Bay
