import Lucent.Net
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

universe v0
variable {I:Type}[Fintype I]
variable {β:ℕ→ℝ}{R:ℕ→ℝ}{r:ℕ→ℕ}
variable {W:ℕ→I→Staff} {S:Stencil I} {m a:ℕ}{b:ℕ→ℕ}{d:FieldPlan I}
local notation:max "gong" => soundOf P β R W b S m a
local notation "mu" => P.pillars 3

open Preparation.Yoke.Lucent.Arity
namespace Banner
variable {P}
variable (h:Banner I P)(z: Window.Family)

variable (y:P.Spectrum0 3)(β)
abbrev dGap (s:ℕ)(z:Window.Family):ℂ:=
   P.singleState 3 s y (h.pairC β s*h.axialC β z s) -
   P.singleState 3 s y (h.pairC β s)*P.singleState 3 s y (h.axialC β z s)
abbrev gGap (s:ℕ):ℂ:=
   P.singleState 3 s y (h.shearC β s*h.pairC β s) -
   P.singleState 3 s y (h.shearC β s)*P.singleState 3 s y (h.pairC β s)
abbrev PaidGap (β:ℕ→ℝ)(h:Banner I P)(y:P.Spectrum0 3)(s:ℕ)(ε:ℝ):Prop:=(ε <‖h.gGap β y s‖ ∧ ∀ z, ε<‖h.dGap β y s z‖)
def Bought (β:ℕ→ℝ)(h:Banner I P)(y:P.Spectrum0 3)(t:ℕ→ℕ):Prop:=∀e,Tendsto (fun n=>P.singleState 3 (t n) y (h.casting β e (t n))) atTop (𝓝 (h.lyricC e))
def advG := ‖h.lyricC (.inl (.some true)) - h.lyricC (.inl (.some false))*h.lyricC (.inl none)‖
def advD (z:Window.Family):= ‖h.lyricC (.inr (true,z)) - h.lyricC (.inl none)*h.lyricC (.inr (false,z))‖

lemma paid (ε:ℝ)(e:ε<h.advG)(k:∀z,ε<h.advD z)(t:ℕ→ℕ)(p:h.Bought β y t):
   ∀ᶠ n in atTop,h.PaidGap β y (t n) ε :=by
 apply Eventually.and
 · let T:= p (.inl (some true)); let U:= p (.inl (some false)); let L:= p (.inl none)
   exact (T.sub (U.mul L)).norm.eventually (lt_mem_nhds e)
 apply Filter.eventually_all.mpr; intro z
 let T:=p (.inr (true,z)); let U:=p (.inl none); let L:=p (.inr (false,z))
 exact (T.sub (U.mul L)).norm.eventually (lt_mem_nhds (k z))
lemma advantage: ∃ ε:ℝ, 0< ε ∧ ε<h.advG ∧ ∀z,ε<h.advD z:=by
 let F(z:Window.Family):= min h.advG (h.advD z)
 have ht(z:Window.Family):0<F z:=by
    obtain ⟨l,y⟩:=priceless _ _ _ _ _ _ h.money z
    exact lt_min (norm_pos_iff.mpr y) (norm_pos_iff.mpr l)
 obtain ⟨x,_,p⟩:= exists_min_image Finset.univ F univ_nonempty
 refine ⟨F x/2,half_pos (ht x), (half_lt_self (ht x)).trans_le (min_le_left ..), fun z=> (half_lt_self (ht x)).trans_le ((p z (mem_univ _)).trans (min_le_right ..)) ⟩
#check @Filter.eventually_all
#check @PencilLease
#check @Port.wick
#check @HoldRead
#check @QualifiedWakeReadout
#check @JointTuple

end Banner

section
variable {X J:Type}[Countable X][Countable J]
variable {P}
def Purchased (P:Spine)(K:P.Register)(A:ℝ)(a b:Stationary.Gaia)(D T:ℕ→ Cover)(β:ℕ→ℝ)(H:X→Banner I P)(N:J→ℕ→P.Test)(Z:J→ℂ) (f:ℕ→ℕ)(x:P.Spectrum0 3):Prop:=
  JointTuple.{v0} P K x ∧ HoldRead P A f x a b D T ∧
  (∀ e, (H e).Bought β x f) ∧
  (∀ i,Tendsto (fun s=>P.singleState 3 (f s) x (N i (f s))) atTop (𝓝 (Z i)))
variable {K:P.Register}{M A:ℝ}{Mc:ℕ}{g:ℕ→ℕ}{p q:Stationary.Gaia}{a b':ℕ→ Cover}
variable (V:Port.{v0} P K M Mc g β)
include V
theorem clearanceBook (H:X→Banner I P)(N:J→ℕ→P.Test)(Z:J→ℂ)(u:∀ i, WakePoll P (N i) (Z i))(w:0<A)(L:P.PencilLease A p q a b')
   {f:ℕ→ℕ}(e:StrictMono f) :
   ∃ c:ℕ→ℕ, StrictMono c ∧ ∀ U:P.Spectrum0 3→Prop, (∀ᵐ x ∂P.pillars 3,U x) →
    ∃ x: P.Spectrum0 3, U x ∧ P.Purchased.{v0} K A p q a b' β H N Z (f ∘ c) x:=by
 let Y:Type:=(X×Banner.CardI)⊕J
 let F:Y→ℕ→P.Test:=Sum.elim (fun x:X×_=> (H x.1).casting β x.2) N

 let E:Y→ℂ:=Sum.elim (fun x:X×_=> (H x.1).lyricC x.2) Z
 obtain ⟨c,t,y⟩:=V.readout A w p q a b' Y f e L F E (fun y=>by
    cases y with
    | inl z=>exact (H z.1).castingRev β V.wick z.2
    | inr i=>exact u i)
 refine ⟨c,t,fun U h=>?_⟩
 obtain ⟨x,hx,l,r,v⟩:=y U h
 exact ⟨x,hx,l,r,fun i d=>v (.inl (i,d)),fun j=>v (.inr j)⟩
end
#print axioms clearanceBook
