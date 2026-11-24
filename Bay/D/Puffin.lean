import Bay.D.Cake
import YM.SU5.Regis.Hospitality
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

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group


open Next.Rank.Spindle Gleam.clocks Sleigh Paddled
namespace Cake
def sweet(x:ℝ):Prop:=
    (atRate 3 x)≤Mi x ∧ (atRate 42 x)≤Ni x ∧ atRate (-30) x ≤ Ei x ∧ atRate 22 x≤ Li x ∧
    (atRate 3 x)^2 ≤Mi x ∧ (atRate 42 x)^2 ≤ Ni x ∧
     (2*atRate 3 x+atRate (-30) x)*atRate (-30) x ≤ Ei x ∧
     2*atRate 42 x *atRate 22 x ≤Li x
lemma sweetness:∀ᶠ x in atTop,sweet x:=by
 filter_upwards [
    (bowl 3).food (b:=8) (by norm_num), (bowl 42).food (b:=85) (by norm_num),
    (bowl (-30)).food (b:= -24) (by norm_num), (bowl 22).food (b:=67) (by norm_num),
    ((bowl 3).bake 2 (b:=6) (by norm_num)).food (b:=8) (by norm_num),
    ((bowl 42).bake 2 (b:=84) (by norm_num)).food (b:=85) (by norm_num),
    ((((bowl 3).icing 2).honey ((bowl (-30)).raise (by norm_num))).stew
      (bowl (-30)) (d:= -27) (by norm_num)).food (b:= -24) (by norm_num),
    (((bowl 42).icing 2).stew (bowl 22) (d:=64) (by norm_num)).food (b:=67) (by norm_num)
 ] with x a b c d e f h t
 exact ⟨a,b,c,d,e,f,h,t⟩

end Cake
open Cake
abbrev Torch {n:Side} {q:Clip}{Z:PathData T4}{H:Bed}{η C S:ℝ}
 (B:Z.Bounds q η C S)(P:Attached H Z)(p:BudgetPoint)(x β:ℝ)
 (o:Site n)(F:Yn n ℂ)(W:Chalk n ℂ):Prop:=
 Ion B P p β (scant x) o o F W (atRate 3 x) (atRate 42 x)
      (atRate (-30) x) (atRate 22 x)
def WheelAward(q:Clip)(L r x:ℝ):Prop:=
 Cake.sweet x ∧ 0<x ∧
 ∀ {Z:PathData T4}{H:Bed}{η C S:ℝ}(B:Z.Bounds q η C S)(P:Attached H Z)
    (p:BudgetPoint), p.threshold=temp x → p.B=radiusB x →
    ∀(β:ℝ), x/2≤β→ β≤2*x → ∀(N:Side)(o:Seat N)(d:ℝ)
        (f:Pane N→ℂ)(A:Icey (Cella (More N))),
    Vessel p o (p.B/10) r d L f A →
     Torch B P p x β o
         (wheel (Real.sqrt x) f)
         (quay q (Real.sqrt x*coupling β) (bWindow x) A)
lemma wheelAwards(q:Clip)(L r:ℝ)(hp:0<r):∀ᶠ x in atTop,WheelAward q L r x:=by
 let R:Rules T4:=(charts T4).some

 have ht:Sugar (-99999) temp:=by
    unfold Sugar thinRate; rw [show (-99999/200000:ℝ)=-(1/2)+1/200000 by norm_num]; exact tempay (by norm_num)
 have v:=(((lemon.bake 2 (b:=200000) (by norm_num)).icing L).stew
    (ht.bake 2 (b:=-199998) (by norm_num)) (d:=2) (by norm_num)).food (b:=3) (by norm_num)
 have e:=((Cake.bowl 20).icing (L*ratioC q)).food (b:=22) (by norm_num)
 have g:=(((Cake.bowl 20).bake 2 (b:=40) (by norm_num)).icing L).food (b:=42) (by norm_num)
 have d0:= (park (-(2/5:ℝ))).lim (by norm_num)
 have t':∀ᶠ x in atTop,Tall (radiusB x/10):=by
    unfold Tall
    refine eventually_all.mpr fun i=>eventually_all.mpr fun s=>?_
    filter_upwards [ Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(budD i s).length)] with x h
    omega
 filter_upwards [sweetness, eventually_gt_atTop (0:ℝ), t',Work.E01.radiusB_tendsto.eventually_ge_atTop 100,v,g,(cake₁ R L).food (b:= -30) (by norm_num),e,
    d0.eventually (ge_mem_nhds (half_pos hp)), d0.eventually (ge_mem_nhds R.radius)
 ] with x sweet' h ht hg h1 h2 h3 h4 c r'
 refine ⟨sweet',h,?_⟩
 intro Z H η C S B P p a b β t u N o D f A h5

 have hx:2*scant x≤r:=by
   change scant x ≤ r/2 at c; linarith only [c]
 have he: Shutter p:=by unfold Shutter; rw [b]; exact ⟨hg,ht⟩
 have hu:= railB t u h
 have hl:=wheelIon (B:=B) (P:=P) R h5 he (by positivity) r' hx
      (show 0<bWindow x by unfold bWindow atRate; positivity) (Real.sqrt_nonneg x)
      ((half_pos h).trans_le t) (abs_le.mpr ⟨hu.1.trans' (by norm_num),hu.2⟩)
 refine hl.relax ?_ h2 ?_ h4
 · unfold mast; rw [a];exact h1
 unfold rope chia;rw[a];exact h3
#print axioms wheelAwards
end YM.CF.Bay.D
