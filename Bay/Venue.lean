import Bay.Cheer
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
variable {I:Type}[LinearOrder I][Fintype I] {w:Berth} {C:ℝ}
 {U:Mew.Key I→ RegBudget w.side} {V:Mew.Key I→ ForceBudget w.side}

namespace Berth
lemma Shrewd.tip (d:w.Shrewd U V C)(l:List I):
 RG.Envelope (w.winE U V l) ∧ ∀ x, ‖w.winE U V l x‖ ≤ ‖w.cap‖ * w.renormal C :=by
 have h x:= lance_bound (d.river x) l (fun z y=>(d.stroke z y).2 x) 0 roots
 exact ⟨⟨Mew.pot_m _ d.river (fun z y=>(d.stroke z y).1.meas) l _ roots,_,h⟩,h⟩

abbrev ovation(w:Berth)(U:Mew.Key I→ RegBudget w.side)(V:Mew.Key I→ ForceBudget w.side)(M:Mark w.side)(z:Mew.Key I):=
 markedRead M w.K (w.carrier U V z)
def Palladium (w:Berth)(U:Mew.Key I→ RegBudget w.side)
 (V:Mew.Key I→ ForceBudget w.side)(C:ℝ):Prop:=
  w.Shrewd U V C ∧
   ∀(M:Mark w.side), RG.Envelope M →
    River (w.ovation U V M) ∧
    ∀ (l:List I), Integrable (w.verse M (w.winE U V l)) (city w.side)∧
     tipI (w.ovation U V M) l=markedRead M w.K (w.winE U V l) ∧
     ∀b:ℝ,(∀x, ‖M x‖ ≤ b) →
       ‖tipI (w.ovation U V M) l/w.cap‖ ≤ b*w.renormal C


lemma letterBoss {n:Side}(X:FC (Single n))(v:Phys n):
 ‖letterRead X v‖ ≤ ‖X‖*‖v‖:=by
 change ‖inner ℂ (mateK n) (acts X v)‖ ≤ _
 refine (norm_inner_le_norm ..).trans ?_
 rw [(tickB _).2,one_mul,←Matrix.l2_opNorm_toEuclideanCLM]
 exact (acts X).le_opNorm _

lemma Shrewd.publishes (e:w.Shrewd U V C)(f:Measurable w.K):
 w.Palladium U V C :=by
 refine ⟨e,?_⟩
 intro M g
 let Y:=fun z:Mew.Key I=>w.verse M (w.carrier U V z)
 let E:=‖w.cap‖*w.renormal C
 have hC:0≤w.renormal C:=mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
 have q:=e.charged.valid
 have hp:0<‖w.cap‖:=norm_pos_iff.mpr q
 have z:0≤E:=mul_nonneg hp.le hC
 have claim(b:ℝ)(p:∀x,‖M x‖ ≤ b):
    River (w.ovation U V M) ∧ ∀ l:List I,
     Integrable (w.verse M (w.winE U V l)) (city w.side)∧
     tipI (w.ovation U V M) l=markedRead M w.K (w.winE U V l) ∧
     ‖tipI (w.ovation U V M) l/w.cap‖ ≤ b*w.renormal C :=by

   let T (x):=letterRead (M (Advance.drawn w.K x))
   have hb:0≤b:=(norm_nonneg _).trans (p (Classical.arbitrary _))
   have v(x):River (fun z=>Y z x):=sc_V (e.river x) (T x)
   have hr(z') (k:z'∈hill I) :AEStronglyMeasurable (Y z') (city w.side):=
     (mark_integrable f g (Integrable.of_bound
       ((e.stroke z' k).1.meas.aestronglyMeasurable) _ (Eventually.of_forall (e.stroke z' k).2))).aestronglyMeasurable
   have hu(z')(k:z'∈hill I)(x):‖Y z' x‖ ≤ b*E:=
     (letterBoss ..).trans (mul_le_mul (p _) ((e.stroke z' k).2 _) (norm_nonneg _) hb)
   have t(l):= rivA Y (city w.side) v hr (mul_nonneg hb z) (fun z' k=> ae_of_all _ (hu z' k)) l
   refine ⟨(t []).1,fun l=>?_⟩
   have r: (fun x=>tipI (fun z=>Y z x) l)= w.verse M (w.winE U V l) :=
     funext (fun x=> sim_H (e.river x) (T x) _ roots)
   obtain ⟨_,w₁,w₂⟩:= t l
   rw [r] at w₁
   refine ⟨w₁, w₂.trans (congrArg (fun F=>∫ x,F x∂city w.side) r), ?_⟩ -- w₂ rhs may defeq
   rw [norm_div]
   refine (div_le_iff₀ hp).mpr (le_trans ?_ (show b*E ≤ _ from by unfold E; ring_nf; exact le_rfl))

   refine lance_bound (t []).1 l (fun z' k=>?_ ) 0 roots
   refine le_trans (norm_integral_le_of_norm_le (integrable_const (b*E)) (ae_of_all _ (hu z' k))) ?_
   simp

 obtain ⟨b,p⟩:=g.cost
 refine ⟨(claim b p).1,fun l=>?_⟩
 obtain ⟨a,c,_⟩:=(claim b p).2 l
 exact ⟨a,c,fun u a=>((claim u a).2 l).2.2⟩
end Berth
end YM.CF.Bay
#print axioms YM.CF.Bay.Berth.Shrewd.publishes
