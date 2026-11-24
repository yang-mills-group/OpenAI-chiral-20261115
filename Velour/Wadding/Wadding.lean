import Velour.Wadding.Wick
import Velour.Organza.Cocoon
/-! # The satin storage of bobbins

Register all vanishing-width apron sequences that are additionally Veloured
in our chosen rep. One muslin, one vacuum. Names for the family etc.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 110000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "D"=> (Σ₁).muslin
local notation "Φ"=> (Σ₁).Detector
local notation "U"=> (Σ₁).unit.translation
local notation "Ω"=> P.heaven j x

structure Bobbin where
 spool:ℕ→P.Apron
 thin (i:Axis) : Tendsto (fun n=>(spool n).realWidth P i) atTop (𝓝 0)
 ribbon: P.Veloured j x spool


abbrev invCrown :Prop:=
 ∀ v:𝓗, v∈Submodule.span ℂ {Ω} ↔
   (∀t:ℝ, (Σ₁).edge t v=v) ∧ (∀z:OS.Cross j, (Σ₁).U z v=v)

def detects : P.Bobbin j x → Φ:= fun b=> b.ribbon.socket
def bobQuote : P.Bobbin j x → ℝ≥0→ (𝓗).Op:= fun b=>b.ribbon.adorning
def firstTulle : D:= ⟨Ω, (Σ₁).muslin_vac (P.heaven_hot j x)⟩

lemma first_emperor (h:P.invCrown j x)(v:𝓗):
 v∈Submodule.span ℂ {Ω} ↔ ∀b:E4,U b v=v:=by
 rw [h]
 constructor
 · rintro ⟨a,c⟩ b; change (Σ₁).edge _ ((Σ₁).U _ v)=v; rw [c,a]
 intro g
 constructor
 · intro t
   have a:=g (t • basis j)
   change (Σ₁).edge ((t • basis j : E4) j)
    ((Σ₁).U ((SEP j) _) v)=_ at a
   rw [show SEP j (t • basis j)=0 from Subtype.ext (by
     change t • (basis j : E4)- _ = _
     simp), (Σ₁).uZero] at a
   simpa using a


 intro t
 have a:=g t.val
 have p:t.val j=0:= t.property
 have d:SEP j t.val=t:=by apply Subtype.ext; change t.val-t.val j • _=_; rw [p,zero_smul,sub_zero]
 change (Σ₁).edge _ ((Σ₁).U _ v)=_ at a
 rw [p,(Σ₁).birth,d] at a; exact a

lemma crown_vac(h:P.invCrown j x) :
 ∀b, U b (P.firstTulle j x).val=(P.firstTulle j x).val:=
 (P.first_emperor j x h Ω).mp (Submodule.subset_span (Set.mem_singleton _))

variable {P j x}

namespace Bobbin
def windBack (B:P.Bobbin j x): P.Bobbin j x where
 spool i := (B.spool i).kiss P j
 thin:=B.thin
 ribbon:=B.ribbon.mirror

lemma backward (B:P.Bobbin j x){d:ℝ≥0}(p:0<d):
 star (P.bobQuote j x B d)=P.bobQuote j x B.windBack d:=(B.ribbon.adorning_mirror p).symm

lemma op_star (B:P.Bobbin j x)(f:Test4):
 (Σ₁).Faces (P.detects j x B f) (P.detects j x B.windBack (bar f)):=
 (show (Σ₁).Instates (P.bobQuote j x B) (P.detects j x B) from B.ribbon.delivery).mirror
    B.windBack.ribbon.delivery ((eventually_mem_nhdsWithin.mono fun _ z=>B.backward z)) f

def restring (B:P.Bobbin j x) {m:ℕ→ℕ}(r:Tendsto m atTop atTop): P.Bobbin j x:= {
 spool := B.spool ∘ m
 thin := fun k=> (B.thin k).comp r
 ribbon := by
  obtain ⟨C,F,u,t,g⟩:=B.ribbon.bill
  exact ⟨(B.thin j).comp r,fun a p=>⟨_,(B.ribbon.printed p).glints r⟩,C,F,u,t,g.mono fun _ z=>r.eventually z⟩
}

lemma preserved {m:ℕ→ℕ}(B:P.Bobbin j x)(r:Tendsto m atTop atTop):
 P.detects j x (B.restring r)=P.detects j x B:=by
 change ((B.restring r).ribbon.socket= B.ribbon.socket)
 refine (B.restring r).ribbon.delivery.common B.ribbon.delivery ?_
 filter_upwards [self_mem_nhdsWithin] with d z
 let p:(0:ℝ)<(d:ℝ):=z
 let Q:=(B.restring r).ribbon
 have v:Gleams ℋ (fun i=> ((B.restring r).spool i).velour P j x d) (B.ribbon.printOp d):= (B.ribbon.printed p).glints r
 exact congrArg (P.tableau j x 0) (((B.restring r).ribbon.printed
        (show (0:ℝ)<(d:ℝ) from z)).unique v)

end Bobbin
variable (P j x)

theorem satin_storage : (Σ₁).Fray (P.bobQuote j x) (P.detects j x):=
 ⟨fun b=>b.ribbon.delivery,
  fun b=>⟨b.windBack,eventually_mem_nhdsWithin.mono fun _ z=> b.backward z⟩⟩



variable {ι κ:Type}
local notation "θ"=> P.detects j x
local notation "G₁"=> (Σ₁).heatL

/-- **First** send all widths to zero. Even with moving budget dials
and Schwartz tests converging (both limiting dials strictly positive),
and any cofinal width indices; convergence in all Muslin graphs. -/
lemma first_spin (L:List κ) (b:κ→P.Bobbin j x)(Y:κ→Test4)(l r:κ→ℝ≥0)
   (m:κ→ℕ→ℕ)(a c:κ→ℕ→ℝ)(f:κ→ℕ→Test4)
   (h:∀z∈L, Tendsto (m z) atTop atTop ∧
     Tendsto (a z) atTop (𝓝 (l z:ℝ)) ∧ Tendsto (c z) atTop (𝓝 (r z:ℝ)) ∧
     Tendsto (f z) atTop (𝓝 (Y z)) ∧ 0<l z ∧ 0<r z):
  (Σ₁).Surges atTop (fun i=> (L.map fun z=>
      (Σ₁).labelled (((b z).spool (m z i)).knock P j x (a z i) (c z i)) (f z i)).prod)
     (L.map fun z=> G₁ (l z)*θ (b z) (Y z) * G₁ (r z)).prod:=by

 refine Surges.per_word
    (F:=fun z i=>(Σ₁).labelled (((b z).spool (m z i)).knock P j x (a z i) (c z i)) (f z i))
    _ ?_
 intro z u
 obtain ⟨e,g,t,y,p,q⟩:= h z u
 rw [←(b z).preserved e]
 exact ((b z).restring e).ribbon.enlighten p q g t y

/-- Now consume all dials; Surges again. -/
lemma second_spin {w:Filter ι} (L:List κ) (b:κ→P.Bobbin j x)(Y:κ→Test4)
   (l r:κ→ι→ℝ≥0) (f:κ→ι→Test4)
   (h:∀z∈L, Tendsto (l z) w (𝓝 0) ∧ Tendsto (r z) w (𝓝 0) ∧
     Tendsto (f z) w (𝓝 (Y z))):
  (Σ₁).Surges w (fun i=>
     (L.map fun z=> G₁ (l z i)*θ (b z) (f z i) * G₁ (r z i)).prod)
     (L.map fun z=> θ (b z) (Y z)).prod:=by
  refine Surges.per_word
    (F:=fun z i=> G₁ (l z i)*θ (b z) (f z i) * G₁ (r z i))
    _ ?_
  intro z u
  obtain ⟨e,g,t⟩:= h z u
  exact ((P.satin_storage j x).1 (b z)).surge_warming t e g

#print axioms second_spin
#print axioms satin_storage
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

