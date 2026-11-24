import YM.SU5.Assay.Base
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 A normal shrinking family has **all** widths shrinking, and acts in
 BSOT with zero threshold on the *given* `(j,x)` space. No hypothesis
 of norm continuity of cartage. Broadening to positive lags is included.
 Distinguish the index of a normal family (`ℕ`) from the engraving height
 (which may for instance equal the index) and from the sampling grid height.
-/
def Fades (D:ℕ→P.Apron): Prop:=∀i:Axis,Tendsto (fun s=> (D s).realWidth P i) atTop (𝓝 0)
structure Normal (D:ℕ→P.Apron)(T:Lag): Prop where
 fades: P.Fades D
 showAt:∀l>0,∀r>0,BSOT (fun i=>P.base j x (D i) l r) atTop (T l r)
variable {P j x}{D C:ℕ→P.Apron}{T L:P.LagOp j x}{l r a b:ℝ}{Y':Vantage}
local notation "β" t:max=> P.base j x (D t)
local notation "σ"=> P.slot j x
local notation "τ" t:max=> (D t).realWidth P j
lemma Fades.all (p:P.Fades D)(h:0<a):∀ᶠ s in atTop,∀i,(D s).realWidth P i <a:=
  eventually_all.mpr fun i=> (p i).eventually (gt_mem_nhds h)
lemma Fades.one (p:P.Fades D)(h:0<l)(j:Axis):∀ᶠ s in atTop,(D s).realWidth P j<l:=(p j).eventually (gt_mem_nhds h)
lemma Fades.kiss (p:P.Fades D)(k:Axis):P.Fades (fun s=>(D s).kiss P k):=p

namespace Normal
variable (p:P.Normal j x D T)
include p
lemma credits : (S).Credits 0 T:=Credits.earned (p.fades j) (Eventually.of_forall (fun s=> P.base_credits j x (D s))) p.showAt
lemma unique (u:P.Normal j x D L)(h:0<l)(t:0<r):T l r=L l r:= (p.showAt l h r t).unique (u.showAt l h r t)
lemma showOn {f g:ℕ→ℝ}(h:0<l)(t:0<r)(q:Tendsto f atTop (𝓝 l))(v:Tendsto g atTop (𝓝 r)):
 BSOT (fun s=> (β s) (f s) (g s)) atTop (T l r):=
 Credits.slide_in (p.fades j) (Eventually.of_forall (fun s=> P.base_credits j x (D s))) p.showAt h t q v
lemma flownOn {f g:ℕ→ℝ}{y:ℕ→Vantage}(h:0<l)(t:0<r)(q:Tendsto f atTop (𝓝 l))(v:Tendsto g atTop (𝓝 r))(w:Tendsto y atTop (𝓝 Y')):
 BSOT (fun s=> P.flown j x (β s) (f s) (g s) (y s)) atTop (P.flown j x T l r Y'):=
 P.locate_limit j x w (p.showOn h t q v)
lemma posed {f g:ℕ→ℝ}{y:ℕ→Vantage}(h:0< Y' j-a)(t:0<b-Y' j)(q:Tendsto f atTop (𝓝 a))(v:Tendsto g atTop (𝓝 b))
 (w:Tendsto y atTop (𝓝 Y')):
 BSOT (fun s=>σ (β s) (f s) (g s) (y s)) atTop (σ T a b Y'):=by
 have u:Tendsto (fun s=> y s j) atTop (𝓝 (Y' j)):= ((continuous_apply j).tendsto _).comp w
 exact p.flownOn h t (u.sub q) (v.sub u) w
lemma budget (h:0<a):∃ C:ℝ,0≤ C ∧ (∀l≥a,∀r≥a,‖T l r‖≤C) ∧
 ∀ᶠ s in atTop, τ s<a∧∀l≥a,∀r≥a, ‖(β s) l r‖≤C:=by
 have u:=p.showAt a h a h; obtain ⟨C,v,y⟩:=u.ceiling
 refine ⟨C,v,fun l t r k=> (Credits.pay₂ p.credits h t k).trans (u.consult v y),?_⟩
 filter_upwards [y,p.fades.one h j] with s t a'; exact ⟨a',fun l r k u=> (Credits.pay₂ (P.base_credits j x (D s)) a' r u).trans t⟩
lemma kiss :P.Normal j x (fun s=>(D s).kiss P j) (P.otherLag j x T):=by
 refine ⟨p.fades.kiss j,?_⟩
 intro l h r u
 refine (p.showAt r u l h).dagger.congr' (Eventually.of_forall fun i=>?_)
 dsimp only; rw [P.base_kiss];rfl
lemma viaDiff (u:P.Fades C){d:ℕ→ℝ}(t:Tendsto d atTop (𝓝 0))
 (v:∀l>0,∀r>0,∀ᶠ s in atTop,‖P.base j x (C s) l r- (β s) l r‖≤d s):P.Normal j x C T:=
 ⟨u,fun _ h _ v'=> (p.showAt _ h _ v').squeeze' t (v _ h _ v')⟩
-- limits used only at positive lags
lemma agrees (w:∀l>0,∀r>0,L l r=T l r):P.Normal j x D L:=by
 refine ⟨p.fades,?_⟩
 intro l h r t; rw [w l h r t]; exact p.showAt _ h _ t
end Normal
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
