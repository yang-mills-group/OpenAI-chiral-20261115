import Velour.Lustre.Meander
import YM.SU5.Aria.Gathering
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
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



private lemma gleams_table {I:Type*}(L:List I){H:Hilbert}
 (f:I→ℕ→H.Op)(g:I→H.Op)
 (h:∀i∈L,Gleams H (f i) (g i)):
 Gleams H (fun n=> (L.map fun i=>f i n).prod) (L.map g).prod:=by
 induction L with
 | nil=>exact Gleams.const _
 | cons i L ih=>
   simp only [List.map_cons,List.prod_cons]
   exact Gleams.mul (h i List.mem_cons_self) (ih fun a p=>h a (List.mem_cons_of_mem _ p))


open Boundary Probe
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "𝓗"=> P.ManyF j ξ
local notation "σ"=> P.seasons j ξ

local notation "E"=> (σ).E
local notation "W"=> P.cartage j ξ
local notation "Ω"=> P.heaven j ξ

/-- Latent point presentation under strict positive walls l,r. -/
def fleck (u:P.Latent x)(p:Vantage)(l r:ℝ): (𝓗).Op:=
 W p * (σ).insulate (P.twink x j u) (p j-l).toNNReal (r-p j).toNNReal * W (-p)


lemma cart_season (p:Vantage)(d:ℝ≥0): Commute (W p) (E d):=by
 rw [P.uses_cart]
 exact ((σ).independent ..).symm

lemma pill_knock (D:P.Apron)(p:Vantage)(l r:ℝ):
 W p * (D.knock P j ξ (p j-l) (r-p j))*W (-p)=
 P.pillar j ξ D l r p :=by
 let t:=D.realWidth P j
 let Y:= P.tableau j ξ 0 (D.engine P j ξ)
 have a:P.tableau j ξ p (D.engine P j ξ)=W p * Y * W (-p):=by
   ext1 z
   rw [mul_apply_eq_comp,mul_apply_eq_comp]
   dsimp only [Y]
   rw [P.lyre];rfl
 rw [Apron.knock, Apron.dye,P.lyre_pad,pad_val,pillar,a,
   Apron.time_panel,Apron.time_edge,sub_right_comm (p j) _ l,←sub_sub]
 let v:=E (p j - l - t).toNNReal
 let w:=E (r - p j - t).toNNReal
 change W p * (v*Y*w)*W (-p)=v* (W p*Y*W (-p)*w)

 conv_lhs=>lhs; rw [←mul_assoc,←mul_assoc,(P.cart_season x j p _).eq]
 conv_rhs=>rhs;rw [mul_assoc,(P.cart_season x j (-p) _).eq]
 simp only [mul_assoc,v,w]

lemma flecks (u:P.Latent x)(p:Vantage)(l r:ℝ)
 (a:l<p j)(b:p j<r):
 Gleams 𝓗 (fun i=>P.pillar j ξ (u.val i) l r p) (P.fleck x j u p l r):=by
 have v: Gleams 𝓗 (fun i=>(u.val i).knock P j ξ (p j-l) (r-p j))
     ((σ).insulate (P.twink x j u) (p j-l).toNNReal (r-p j).toNNReal):=
    (P.behold x j u).ribbon.squeeze
      (Real.toNNReal_pos.mpr (sub_pos.mpr a))
      (Real.toNNReal_pos.mpr (sub_pos.mpr b))
      (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr a.le)];exact tendsto_const_nhds)
      (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr b.le)];exact tendsto_const_nhds)
 exact (((Gleams.const _).mul v).mul (Gleams.const _)).agree
   (Eventually.of_forall fun i=>P.pill_knock ..)

variable {I:Type*} (u:I→P.Latent x)(p:I→Vantage)(L:List I)
def sunPrint (l r:I→ℝ):ℂ:=
 inner ℂ Ω ((L.map fun i=>P.fleck x j (u i) (p i) (l i) (r i)).prod Ω)
def silhouette (i:I)(n:ℕ): P.Apron:=(u i).val n
local notation "A"=> fun n i=> (u i).val n
def constell (n:ℕ): ℂ:= P.memorial j ξ (fun i=> (u i).val n) L p
local notation "δ"=> fun i=>p i j
lemma entrances {i:I} {a b:ℝ} (t:a<p i j)(g:p i j<b):
 ∀ᶠ n:ℕ in atTop, a < P.porchY j ((A) n) p i ∧ P.resignY j ((A) n) p i < b:=by
 have h:Tendsto (fun n=> ((u i).val n).realWidth P j) atTop (𝓝 0):=(P.behold x j (u i)).thin j
 filter_upwards [h.eventually (gt_mem_nhds (sub_pos.mpr t)),h.eventually (gt_mem_nhds (sub_pos.mpr g))] with n h g
 change ((u i).val n).realWidth P j<_ at h
 change ((u i).val n).realWidth P j<_ at g
 change a< p i j - ((u i).val n).realWidth P j ∧ p i j + ((u i).val n).realWidth P j < b
 constructor <;> linarith


def Ascends (j:Axis)(p:I→Vantage)(L:List I):Prop:= L.Pairwise fun i k=> p i j < p k j

lemma ascendance (g:Ascends j p L):
 ∀ᶠ n:ℕ in atTop,P.Turnstile j ((A) n) L p:=by
 induction L with
 | nil=> exact Eventually.of_forall fun _=>List.Pairwise.nil
 | cons i L ih=>
    obtain ⟨y,z⟩:=List.pairwise_cons.mp g
    have r:∀ᶠ n:ℕ in atTop,∀ k ∈ L.toFinset, P.resignY j ((A) n) p i<P.porchY j ((A) n) p k:=by
       refine L.toFinset.eventually_all.mpr fun k h=>?_
       obtain ⟨d,r,t⟩:=exists_between (y k (List.mem_toFinset.mp h))
       exact ((P.entrances x j u p (show p i j-1<p i j by linarith) r).and
          (P.entrances x j u p t (show p k j< p k j+1 by linarith))).mono fun _ h=>h.1.2.trans h.2.1
    filter_upwards [r,ih z] with n e f
    exact List.pairwise_cons.mpr ⟨fun k v=>e k (List.mem_toFinset.mpr v),f⟩

lemma sunPrinted (w:Curtains (δ) (δ) L):
 Tendsto (P.constell x j u p L) atTop (𝓝 (P.sunPrint x j u p L w.first w.last)):=by
 let B:= fun i n=>P.pillar j ξ ((A) n i) (w.first i) (w.last i) (p i)
 have h:= gleams_table L B (fun i=>P.fleck x j (u i) (p i) (w.first i) (w.last i))
    fun i y=> P.flecks x j (u i) (p i) _ _ (w.inside _ y) (w.outside _ y)
 refine (tendsto_const_nhds.inner (h.gaze Ω)).congr' ?_
 have y:∀ᶠ n:ℕ in atTop,∀i∈L.toFinset,
     w.first i < P.porchY j ((A) n) p i ∧ P.resignY j ((A) n) p i < w.last i:=
    L.toFinset.eventually_all.mpr fun i g=>P.entrances x j u p
      (w.inside _ (List.mem_toFinset.mp g)) (w.outside _ (List.mem_toFinset.mp g))
 exact y.mono fun n g=>(P.pill_memorial j ξ ((A) n) L p w.first w.last
     (fun i v=>g i (List.mem_toFinset.mpr v)) w.joins).symm

/-- Eu point correspondence over the latent family across axes on
strict chronologies on both sides. -/
theorem star_draped (w:Curtains (δ) (δ) L)
    {L':List I}{b:Axis}
    (w':Curtains (fun i=> p i b) (fun i=>p i b) L')
    (e:L.Perm L')(R:P.Ellis 3 x)(y:Ascends j p L)(z:Ascends b p L')


    : P.sunPrint x j u p L w.first w.last=P.sunPrint x b u p L' w'.first w'.last:=by
 refine tendsto_nhds_unique_of_eventuallyEq (P.sunPrinted x j u p L w) (P.sunPrinted x b u p L' w') ?_
 filter_upwards [P.ascendance x j u p L y,P.ascendance x b u p L' z] with n s t
 exact P.unanimous 3 x _ _ p j b L' s t e R

lemma Ascends.curtain (g:Ascends j p L): Nonempty (Curtains (δ) (δ) L):=
by
 have s: L.Nodup:=List.Pairwise.imp (fun {a b} (h:p a j<p b j)=>show a≠b by intro y; subst b; exact lt_irrefl _ h) g
 exact choose_curtains _ _ _ s (weaves_sorted _ _ _ g)

#print axioms star_draped

