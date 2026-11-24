import Merino.Cuff.Relief
import Merino.Cuff.Auburn
import Merino.Cuff.Fit
import Merino.Rind
import Merino.Glass
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n

open Push.Uniform Planned.JetPort Peaks
open scoped ContDiff
open _root_.Zephyr.Chern
lemma bud_re (f:ℝ→ℂ)(h: Bud f): (bud f 2).re=
 iteratedDeriv 2 (fun x=>(f x).re) 0/2:=by
 have e:=Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h.2.hasDerivAt
 have p: deriv (fun x=>(f x).re) =ᶠ[𝓝 0] fun x=>(deriv f x).re:=
   h.1.mono fun x u=> (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x u.hasDerivAt).deriv
 have r:deriv (deriv (fun x=>(f x).re)) 0 = (deriv (deriv f) 0).re:=
   p.deriv_eq.trans e.deriv
 rw [iteratedDeriv_succ,iteratedDeriv_one,r]
 change (deriv (deriv f) 0 / 2).re=_
 rw [Complex.div_ofNat_re]


variable {o:Seat n}{p:BudgetPoint}{X:Oil n}{a b d c C r:ℝ}
abbrev needle (n:Side):=hueInk∘ridge (N:=More n)
abbrev InkFace (n:Side):=Inky (Husk group (More n))

/-- Masked chart response over actual small-link panels, unshifted
post within 4 of literal gauge origin. -/
lemma tartan (h:Room d r C)(K:Scree.Loom n)(u:Skylit p d K)(t:Trunk o X (p.B/10) a b d)
    (ha:0<a)(ho:separation 0 o≤4)(l:4*(lead (p.B/10)+8)+1<n.val)
    (f:Bud (glaze (stream n) X)):
    ∃ T:InkFace n, Sheath 0 (4+lead (p.B/10)) (C*b*(tow a)^2) T ∧
      (bud (glaze (stream n) X) 2).re=dripQ T (needle n) (needle n) ∧
      ∀ (V:Pane n)(Y:Bows n),‖Y‖≤r → V ∈ pass p o →
        Agrees (purse (p.B/10) o) V (dyeB n Y) →
        |(masked K p o X V).trace.re - (traceX X 1+dripQ T (cseed Y) (cseed Y))| ≤
           C*b*‖Y‖^3:=by
 obtain ⟨Z,H,j,w⟩:=earned h ha.le t
 obtain ⟨T,k,g⟩:=H.cover ha (show lead (p.B/10)< _ by change _< n.val*2; omega)


 have e:Sheath 0 (4+lead (p.B/10)) (C*b*(tow a)^2) T:=
   ⟨k.flip,k.rent,fun i j v=>(separation_triangle _ o _).trans (add_le_add ho (k.abode i j v))⟩
 refine ⟨T,e,?_,?_⟩
 · unfold needle; rw [bud_re _ f,←seam_same e (by omega),←g,j]
   simp only [glaze, petals_zig,dyeB,traceX]
 intro V Y hy v ht; rw [mask_extension u ha.le t v (h.get _ hy) ht,←g]
 exact w _ hy

end YM.CF.Merino.Cuff
