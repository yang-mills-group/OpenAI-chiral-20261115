import Merino.Robe
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered StressExchange Dial

/-! A storable insertion. Decorations (`spool`) are NOT indexed by a configuration
or a direction of reflection. License it at its own root. -/
/-- Information needed to specify the sensor. Lengths of jumps in matter
sites (gauge mesh *two*). `origin` is a lower-corner central matter site
of the even block; distinguished gauge root is its node, not quite
the midpoint of the block. The scalar's trunk is based directly here.
Axis trunks based *here* will be transported by matter shifts,
including wrap convention, before masking at the translated node. -/
structure Spool (n:Side) where
 origin: Site n
 stepY:ℕ
 spin:Axis→SOp n
 color:SOp n

namespace Spool
variable (y:Spool n) (K:Scree.Loom n)(p:BudgetPoint)
abbrev post:Seat n:=node y.origin

abbrev scalar: Evaluation n:=sheen K p y.post y.color
abbrev jPole(a:Axis):Evaluation n:=flowHead K p y.post (y.spin a)
abbrev jShift(a:Axis)(x:Site n):Evaluation n:=
  flowHead K p (node x) (co_Ψ x y.origin (y.spin a))
abbrev rightY(a:Axis):Site n:= y.origin+gapPlus a y.stepY
abbrev leftY(a:Axis):Site n:= y.origin-gapPlus a y.stepY
abbrev jumps:Evaluation n:=∑ i:Axis,(y.jShift K p i (y.rightY i) - y.jShift K p i (y.leftY i))
def patchwork:Evaluation n:=y.scalar K p+y.jumps K p
def opening (fac:ℂ):Evaluation n:= fac • y.patchwork K p
abbrev canvas: Sa n := purse (p.B+12+2*y.stepY) y.post


variable {y K p}
lemma fit {x:Site n}(h:separation y.origin x ≤ y.stepY):casing p (node x) ⊆ y.canvas p:=by
 intro i v
 obtain ⟨z,a,l⟩:=halo_spec.mp v
 rw [mem_singleton.mp a] at l
 apply halo_spec.mpr
 exact ⟨y.post,mem_singleton_self _,(separation_triangle _ (node x) _).trans
   (by rw [post, Hove.ζdist]; omega)⟩

/-- Physical certificate including endpoints. -/
structure Hem (y:Spool n)(K:Scree.Loom n)(p:BudgetPoint)(a b d:ℝ):Prop where
 skylight:Skylit p d K
 sign:0≤a
 sip:Trunk y.post y.color (p.B/10) a b d
 spurt(i):Trunk y.post (y.spin i) (p.B/10) a b d
namespace Hem
variable {a b d:ℝ}(h:Hem y K p a b d)
include h
lemma scalar :LicenseY (y.canvas p) (y.scalar K p):=
 (sheen_licensed h.skylight h.sign h.sip).up (fit (by simp))
lemma jShift (i:Axis)(x:Site n): LicenseY (casing p (node x)) (y.jShift K p i x):=
 flow_licensed h.skylight h.sign (trunk_go y.origin x (h.spurt i))
lemma jPole (i:Axis): LicenseY (casing p y.post) (y.jPole K p i):=
 flow_licensed h.skylight h.sign (h.spurt i)

lemma jumps: LicenseY (y.canvas p) (y.jumps K p):=
 LicenseY.sumAll _ _ fun i=>((h.jShift i _).up (fit (stopBeam y.origin i y.stepY).1)).sub ((h.jShift i _).up (fit (stopBeam y.origin i y.stepY).2))


lemma patch:LicenseY (y.canvas p) (y.patchwork K p):=h.scalar.add h.jumps

lemma licensed (fac:ℂ):LicenseY (y.canvas p) (y.opening K p fac):=h.patch.scale fac

end Hem

abbrev rift (y:Spool n)(K:Scree.Loom n)(p:BudgetPoint) :=
 puffLine K p y.origin y.spin y.color y.stepY

/-- Paid unphysical operator use. Will be proved to have the same bra
effect as opening, with this very factor. -/
def release (y:Spool n)(K:Scree.Loom n)(p:BudgetPoint)(fac:ℂ):phy n := fac • y.rift K p

end Spool
end YM.CF.Merino

