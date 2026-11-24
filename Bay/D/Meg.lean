import Bay.D.Barque
import Bay.D.Skiff
import Bay.D.Skin
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
open Buffered Lifted

structure Enroll(S:Finset Cover)(L:ℝ)(f:LinksC→ℂ):Prop where
   meas:Measurable f
   flat(x):‖f x‖≤L
   seated(x y):Agrees S x y→ f x=f y
   hue(t:Cover→E)(x):f (Lattice.gauge t x)=f x

lemma Enroll.zone {S:Finset Cover}{L:ℝ}{F:ℕ→LinksC→ℂ} {f:LinksC→ℂ}
    (h:∀i,Enroll S L (F i))(H:TendstoUniformly F f atTop):
    Enroll S L f:=by
 have x:=fun x=> H.tendsto_at x
 refine ⟨measurable_of_tendsto_metrizable (fun i=>(h i).meas) (tendsto_pi_nhds.mpr x),
    fun u=>le_of_tendsto ((x u).norm) (Eventually.of_forall fun i=>(h i).flat _),?_,?_⟩
 · intro u v w
   exact tendsto_nhds_unique_of_eventuallyEq (x u) (x v) (Eventually.of_forall fun i=>(h i).seated _ _ w)
 intro t u
 exact tendsto_nhds_unique_of_eventuallyEq (x _) (x _) (Eventually.of_forall fun i=>(h i).hue t _)

-- covering envelope
structure Furled(o:Cover)(b:ℕ)(t d L:ℝ)(f:LinksC→ℂ):Prop extends Enroll (Band o b) L f where
 sleepy(x):¬landingC b o t x→f x=0
 tight {x y}:landingC b o t x→landingC b o t y→
    dist (f x) (f y)≤L*(((nubs (Band o b)).card * dist (inlet (Band o b) x) (inlet (Band o b) y))/|d|)

variable {o:Cover}{b:ℕ}{t d L:ℝ}{p:BudgetPoint}
local notation "SΩ"=>Band o b

lemma Vinyl.readIn {N:Side}{k:ℕ}{f:Pane N→ℂ}
    (v: Vinyl p (wrap _ o) k d L f)(hb:p.B=b)(ht:p.threshold=t)
    (w:k≤b)(e:AtEase SΩ N):
   Furled o b t d L (f∘craft SΩ N):=by
 subst b t
 let c:=craft (Band o p.B) N
 have H(x): c x∈setAwning p (wrap _ o)↔landingC p.B o p.threshold x:= craft_tick e p.threshold x
 refine ⟨⟨v.meas.comp craft_cont.measurable,fun x=>v.small _,fun x y h=> v.localV _ _ (craft_support e h),fun t x=> (v.localV _ _ (craft_hue e t x)).trans (v.hue _ _)⟩,
     fun x h=> v.fence _ (mt (H x).mp h), ?_⟩
 intro x y u z
 rw[dist_eq_norm];apply le_trans (v.polish ((H _).mpr u) ((H _).mpr z))
 exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (fare_inlet (w.trans (Nat.le_add_left ..)) e x y) (abs_nonneg _)) v.nonneg

lemma Furled.zone {F:ℕ→LinksC→ℂ}{f:LinksC→ℂ}
    (h:∀i,Furled o b t d L (F i))(H:TendstoUniformly F f atTop):
    Furled o b t d L f:=by
 refine ⟨Enroll.zone (fun i=>(h i).toEnroll) H,?_,?_⟩

 · intro x v
   exact tendsto_nhds_unique_of_eventuallyEq (H.tendsto_at x) tendsto_const_nhds (Eventually.of_forall fun i=>(h i).sleepy _ v)
 intro x y a e
 exact le_of_tendsto ((H.tendsto_at x).dist (H.tendsto_at y)) (Eventually.of_forall fun i=>(h i).tight a e)

lemma furleds {F:ℕ→LinksC→ℂ}
    (h:∀i,Furled o b t d L (F i)):
   ∃φ:ℕ→ℕ,StrictMono φ∧∃f,TendstoUniformly (F∘φ) f atTop∧Furled o b t d L f:=by
 have u:0≤L:=(norm_nonneg _).trans ((h 0).flat 1)
 have := Fleet.launch (shipFleet (D:=setOf (landingC b o t)) (inlet SΩ) (inlet_bounds _) F
     ⟨L,fun i=>(h i).flat⟩
     ⟨L*(nubs SΩ).card / |d|+1,by positivity,fun x a y z i=>le_trans ((h i).tight a z) (by
         rw[←mul_div_assoc,←mul_assoc, mul_div_right_comm]
         exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)⟩
     (fun i=>(h i).sleepy))
 obtain ⟨φ,U,g,H⟩:=this
 exact ⟨φ,U,g,H,Furled.zone (fun i=>h _) H⟩
end YM.CF.Bay.D
