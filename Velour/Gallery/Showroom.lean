import Velour.Gallery.Sleeves
import Velour.Wadding.Tapes

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



local notation "W" a:max => Apron.realWidth P a j
variable (F:SampleDose)(l r:ℝ)
def sleeveEu (A:P.Apron):(𝓗).Op:= P.flounce j x (W A) l r (P.mounted j x A) F
variable {P}
lemma sleeve_wall {a:P.Spectrum0 3}(J:P.Ellis 3 a)(B:P.Apron)
 (u:Corners j l r F (W B)){m:ℕ→ℕ}(q:Tendsto m atTop atTop):
 let x:=P.advocate 3 a j
 P.Spreads j x (fun i=>P.pleat j x l r F (m i) B) (P.sleeveEu j x F l r B):=by
 let d:=W B
 let ξ:=P.advocate 3 a j

 let b:=B.velour P j ξ d
 let e:=B.engine P j ξ
 have be:b=e:=by
   dsimp [b,e,d,Apron.velour,Apron.dye]
   simp only [sub_self,pad_val,Real.toNNReal_zero,eZero]; rfl
 have h:Gleams _ (fun _:ℕ=>b) e:=be ▸
  (show Gleams _ (fun _:ℕ=>b) b from
    ⟨⟨_,Eventually.of_forall (fun _=>le_refl _)⟩,fun _=>tendsto_const_nhds,fun _=>tendsto_const_nhds⟩)
 exact (P.lamina_spreads j d l r F J h q).agree (Eventually.of_forall fun i=>
    P.lam_pleat j ξ l r F (m i) B le_rfl u)

variable (P)
def layout : P.Brocade j x→ℕ→ P.Apron:= Sum.elim Bobbin.spool (fun A _=>A)
def installation(d:ℝ≥0): P.Brocade j x→(𝓗).Op:=
  Sum.elim (P.bobbinEu j x l r F d) (P.sleeveEu j x F l r)
def FitsLayout (d:ℝ≥0): P.Brocade j x→Prop:=
 Sum.elim (fun _=>0<d ∧ Corners j l r F d)
    (fun A=>∀p∈tsupport F.val,l<p j-W A ∧ p j+ W A<r)

lemma assemble {a:P.Spectrum0 3}(J:P.Ellis 3 a)
 (B:P.Brocade j (P.advocate 3 a j)){d:ℝ≥0}
 (u:P.FitsLayout j _ F l r d B){m n:ℕ→ℕ}(q:Tendsto m atTop atTop)(s:Tendsto n atTop atTop):
 let x:=P.advocate 3 a j
 P.Spreads j x (fun i=>P.pleat j x l r F (m i) (P.layout j x B (n i)))
   (P.installation j x F l r d B):=by
 rcases B with B|B
 · change 0<d ∧ Corners j l r F d at u
   exact B.eu_purchase a j J u.1 u.2 s q
 change ∀p∈tsupport F.val,l<p j-W B ∧ p j+W B<r at u
 exact sleeve_wall j F l r J B (fun i p=> by
   obtain ⟨e,h⟩:=u i p
   constructor <;> linarith only [e,h]) q

lemma FitsLayout.pins {P:Spine}{x:P.Spectrum0 j}{A:P.Brocade j x}{d:ℝ≥0}(e:P.FitsLayout j x F l r d A){n:ℕ→ℕ}(w:Tendsto n atTop atTop):
 ∀ᶠ i in atTop,∀y∈tsupport F.val,l<y j-(P.layout j x A (n i)).realWidth P j ∧ y j+ (P.layout j x A (n i)).realWidth P j<r:= by
 rcases A with Z|Z
 · change 0<d ∧ Corners j l r F d at e
   have t:=(Z.thin j).comp w
   filter_upwards [t.eventually (gt_mem_nhds (show (0:ℝ)<d from e.1))] with i v y hy
   change (Z.spool (n i)).realWidth P j< (d:ℝ) at v
   obtain ⟨a,b⟩:=e.2 y hy
   change l<y j-(Z.spool (n i)).realWidth P j ∧ y j+(Z.spool (n i)).realWidth P j<r
   constructor <;>linarith only [a,b,v]
 exact Eventually.of_forall fun _=>e

variable (a:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 a j
local notation "Jω"=> P.heaven j ξ
local notation "B"=> P.Brocade j ξ

lemma install_buttons {I:Type}(L:List I)(l r:I→ℝ)(F:I→SampleDose)
 (Q:I→B)
 (p:EuOrder L l r)
 (J:P.Ellis 3 a)
 (d:I→ℝ≥0)(u:∀i∈L,P.FitsLayout j ξ (F i) (l i) (r i) (d i) (Q i))
 (σ:I→ℕ→ℕ)(m:ℕ→ℕ)(v:Tendsto m atTop atTop)
 (w:∀i∈L,Tendsto (σ i) atTop atTop)
 (g:∀ᶠ n in atTop,∀i∈L,(P.layout j ξ (Q i) (σ i n)).s≤ m n):
 Tendsto (fun n=>P.singleState j (m n) ξ (L.map fun i=>
     P.prepared (m n) (P.layout j ξ (Q i) (σ i n)) (F i)).prod) atTop
    (𝓝 (inner ℂ Jω ((L.map fun i=>P.installation j ξ (F i) (l i) (r i) (d i) (Q i)).prod Jω))):=by
 let f n i:= P.layout j ξ (Q i) (σ i n)
 have c i (s:i∈L):= P.assemble j (F i) (l i) (r i) J (Q i) (u i s) v (w i s)
 have t:=Spreads.prod_runs L c Jω


 rw [← (P.enter j ξ).inner_map_map]
 refine (tendsto_const_nhds.inner t).congr' ?_
 have s:∀ᶠ n in atTop,∀i∈L.toFinset,P.PinsStrict j l r F (f n) i:=by
    classical
    refine L.toFinset.eventually_all.mpr fun i v=>?_
    have b:=List.mem_toFinset.mp v
    exact FitsLayout.pins j _ _ _ (u i b) (w i b)
 filter_upwards [s,g] with i q r'
 exact (P.eu_literal j ξ L l r F (f i) (m i) p
     (fun _ h=>q _ (List.mem_toFinset.mpr h)) r').symm

#print axioms install_buttons
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


