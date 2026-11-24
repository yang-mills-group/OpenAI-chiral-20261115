import Organdy.Viscount

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

open Hive Levier Urn

open BProof.Bide
abbrev fastPose (y:Cover):Shape:= ⟨1,y⟩
abbrev stageMove(K:Calibration)(y:Cover):Dome K→ₗ[ℂ] Dome K:=
 flounce K (fastPose y)
open BProof.Bide Reed

section
variable {n:Side}{K:Scree.Loom n}{p:BudgetPoint}
 {a b d:ℝ} {X:SOp n} 
lemma emeraldMove
 (w:StageSet K p d) (c:0≤a)
 (v:Trunk (node 0) X (p.B/10) a b d)
 (y:Cover):
  hmMark (fastPose y) (Jc K p 0 X)= Jd K p 0 (wrap _ y) X:=by
 let x:=wrap n y
 let s:=taxiPlus (x-0)
 have r:Levier.ray (veer (fastPose y)) (fastPose y)=s:= by
   rw [veer_sign]; unfold s;rw [sub_zero]
   change Sweep.mk _ x (detX 1)=_
   rw [det_i]
 have G(U:FC (Single n)): teen s U=twist (quantU (γS s)) U:=by
    change lotB false (detX 1) (γS s) U=_
    rw [det_i];rfl
 funext U
 unfold hmMark voltaM; rw [r,inv_inv]
 apply (twist (quantU (γS s))).injective
 change (twist (quantU (γS s))) ((teen s⁻¹) (Jc K p 0 X (voltaF s U)))= twist (quantU (γS s)) _
 rw [←G]
 have z:=poseJ (x:=x) c w v U
 rw [yetL]
 · have h:=standJ (dressing w) c v
   have t(F):Keys (Jc K p 0 X F):=
       Chord.keys_of_chord (Chord.full (h.realc.allV F).sector)
   rw [inv_mul_cancel, lot_i _ (t _)]
   exact z.symm
 exact Chord.keys_of_chord (Chord.full ((standJ (dressing w) c v).realc.allV _).sector)
end



variable {P:Spine}{c:Cuts}{s:ℕ}
 {I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "Hp"=> P.calibration
local notation "B"=> shaft P s
local notation "Hₛ"=>station P s
variable (p:Parade l P c d s i k X F x)


include p
lemma naming [l.NeBot]
 (T:Shape)(j t:Pin)
 (q:∀ r:I,hmMark T (modal P c s (i r) (k r) (X r) j)=modal P c s (i r) (k r) (X r) t):
 flounce Hp T (labeled p j)=labeled p t:=by
 apply Subtype.ext
 let S:=(Hₛ).image T.motion∪Hₛ
 have e:∀ᶠ r in l, Hosp S (tunnel P s i r):=
   p.rate.both ((Tower.turning P.run P.large s S).mono fun i h=>Eventually.of_forall fun k=>by
      rw [terrain P.run P.large (P.run.ir i) s] at h; exact h.hosp)
 have a:= (p.pins j).1.tangle T
 rw [funext q] at a
 have b:=(p.pins t).1
 let a':Gallon l P s i S (fun r=>modal P c s (i r) (k r) (X r) t)
        (fun r=>flick T (F j r)) (flick T (x j)):=⟨a.queue.sitePlus subset_union_left,a.sees⟩
 exact a'.accord (G:=(F t)) ⟨b.queue.sitePlus subset_union_right,b.sees⟩ e

abbrev gstride (m:ℕ)(u:Axis):Cover:= m • step u
lemma doubleReach [l.NeBot](a:0≤c.a)(u:Axis):
 stageMove Hp (gstride c.m u) (labeled p (.axis u))=labeled p (.plus u) ∧
 stageMove Hp (-gstride c.m u) (labeled p (.axis u))=labeled p (.minus u):=by
 constructor
 · refine naming p (fastPose _) _ _ fun t=>?_
   have v:=emeraldMove ((p.vintage t).reef.clearing.stages) a ((p.slot t).toSquid.toKit.medal u)
       (gstride c.m u)
   unfold gstride at v
   rw [map_nsmul,wrap_step] at v
   simp only [modal,tooled,zero_add]
   exact v
 refine naming p (fastPose _) _ _ fun t=>?_
 have v:=emeraldMove ((p.vintage t).reef.clearing.stages) a ((p.slot t).toSquid.toKit.medal u)
    (-gstride c.m u)
 unfold gstride at v
 rw [map_neg,map_nsmul,wrap_step] at v
 simp only [modal,tooled,zero_sub]
 exact v
