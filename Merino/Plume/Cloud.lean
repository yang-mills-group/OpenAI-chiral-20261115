import YM.CF.Buffered.Probes
import Merino.Shuttle
import YM.Lattice.Box
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}

abbrev Pin(m:ℕ):= ↥(box m) × Axis
abbrev Nib(m:ℕ):=Option (Pin m)
def dot (x:LinksC): Nib m→E
 | none=>1
 | some i=>x (i.1.val,i.2)
def hole (m:ℕ) (a:Edge (Seat n)):Nib m:=
  if h:lift a.1 ∈ box m then some (⟨_,h⟩,a.2) else none
def dark (n:Side)(m:ℕ) (x:LinksC):Pane n:=dot x ∘ hole m
lemma darkC: Continuous (dark n m):=by
 apply continuous_pi
 intro i; simp only [dark,comp_apply]
 cases hole m i
 · exact continuous_const
 exact continuous_apply _

lemma doorstep {x:Seat n}(h:x∈purse m 0): lift x∈ box m:=by
 have j:pdist x≤ m:=by
   obtain ⟨y,t,k⟩:=halo_spec.mp h;rw [mem_singleton] at t
   rw [t,separation_comm,separation,sub_zero] at k
   exact k
 rw [box_test]; constructor<;>intro i<;>
    have l:=(component_le x i).trans j<;> omega
lemma key {i:Edge (Seat n)} (x:LinksC) (h: i.1 ∈ purse m 0):
   dark n m x i=x (lift i.1,i.2):=by
 simp only [dark,comp_apply,hole,dif_pos (doorstep h),dot]



lemma knocker {i:Edge (Seat n)}
 (h:i.1 ∈ purse m 0)(z:m+1<n.val):
 lift i.1 + step i.2 = lift (i.1+step i.2):=by
 obtain ⟨a,b⟩:=box_test.mp (doorstep h)
 refine Eq.symm (lift_eq_iff.mpr ⟨by simp,fun j=>?_⟩)
 have r:(More n).val=n.val*2:=rfl
 specialize a j; specialize b j
 rw [Pi.add_apply, step_apply]
 split<;>omega

variable {f:Pane n→ℂ}(h:LocalOn (purse m (0:Seat n)) f)
include h
lemma local_dark:
 m+1<n.val→LocalOn (Lattice.box m) (f∘dark n m):=by
 intro z x y p
 refine h _ _ fun i a b=>?_
 rw [key _ a,key _ a]
 exact p _ (doorstep a) ((knocker a z) ▸ doorstep b)

lemma periodic (x:Pane n):
 (f∘dark n m) (onC n x)=f x:=by
 refine h _ _ fun i a _=>?_
 rw [key _ a,onC_spec]
 simp


lemma sang_dark (z:m+1<n.val)(g:GaugeInvariant f):
 GaugeInvariant (f∘dark n m):=by
 intro k X
 let U:=dark n m X
 let w:Seat n→E:=k∘lift
 refine Eq.trans ?_ (g w U)
 refine h _ _ fun i a b=>?_
 rw [key _ a,Lattice.gauge]
 obtain ⟨i,j⟩:=i
 change _= k (lift i)*dark n m X (i,j)*(k (lift (i+step j)))⁻¹
 have l:=knocker a z
 change lift i+step j=_ at l
 rw [key _ a, l]

omit h
lemma sang_full {f:LinksC→ℂ}(g:GaugeInvariant f)(n:Side):
 GaugeInvariant (f∘onC n):=by
 intro t x
 rw [comp_apply,comp_apply]
 let w:Cover→E:=t∘(wrap (More n))
 rw [←g w (onC n x)]
 congr 1
 
 funext ⟨i,j⟩
 simp [onC_spec,Lattice.gauge,w]

