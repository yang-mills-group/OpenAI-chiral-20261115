import YM.SU5.Six.PressSmear
import YM.SU5.Assay.Normal
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
variable (F:SampleDose)
/-! Walled is strict purchase of lags beyond threshold across *topological*
 support. Usually w ≥ 0 (and a < b), but use across all parameters, including
 vacuous purchase on empty support.
-/
def Walled (a b w:ℝ) : Prop:=∀i∈tsupport F.val,w< i j-a ∧ w<b-i j
variable {j F P}{G:SampleDose}{a b d e w:ℝ}
lemma Walled.outer (h:Walled j F a b w)(p:d≤a)(q:b≤e):Walled j F d e w:=by
 intro i t; obtain ⟨u,v⟩:=h i t; constructor <;> linarith
lemma Walled.currency (h:Walled j F a b w)(p:d≤w):Walled j F a b d:=fun i t=>⟨lt_of_le_of_lt p (h i t).1,lt_of_le_of_lt p (h i t).2⟩
lemma Walled.subs (h:Walled j F a b w)(p:tsupport G.val⊆tsupport F.val):Walled j G a b w:=fun i t=>h i (p t)
lemma Walled.more (h:Walled j F a b w):∃u>w,Walled j F a b u:=by
 rcases (tsupport F.val).eq_empty_or_nonempty with v|v
 · exact ⟨_,lt_add_one w,by unfold Walled;rw [v];simp⟩
 let f(i:Vantage):=min (i j-a) (b-i j)
 have t:Continuous f:= ((continuous_apply j).sub continuous_const).min (continuous_const.sub (continuous_apply j))
 have hb:IsCompact (tsupport F.val):= F.budget
 obtain ⟨i,g,p⟩:= hb.exists_isMinOn v t.continuousOn
 obtain ⟨u,v,y⟩:=exists_between (show w<f i from lt_min (h i g).1 (h i g).2)
 exact ⟨u,v,fun k q=> lt_min_iff.mp (y.trans_le (p q))⟩
lemma Walled.flip (h:Walled j F a b w):Walled j (flipDose F j) (-b) (-a) w:=by
 intro i t; rw [flipBudget] at t
 obtain ⟨p,q⟩:=h ((poseMirror j) i) t
 rw [show poseMirror j i j= -i j from if_pos rfl] at p q
 -- wait! p is w < -i j -a, target first w<i j - -b = q; second w< -a-i j =p. ok
 constructor <;> linarith only [p,q]

variable {D N:P.Apron}
lemma Walled.used (h:Walled j F a b w)(P:Spine){t:ℕ}{k:Cover}(p:k∈P.usedGrid t F):
 w<P.meshPose t k j-a∧w<b-P.meshPose t k j:=h _ ((P.usedPose t F k).1 p)
lemma Walled.aperture (h:Walled j F a b (D.realWidth P j)){k:Vantage}(p:k∈P.spacePrice D F):
 a < k j ∧ k j < b:=by
 obtain ⟨i,v,u⟩:= Set.mem_iUnion₂.mp p
 obtain ⟨v,t⟩:=h i v; obtain ⟨u,y⟩:=abs_le.mp (u j); constructor <;> linarith
lemma Walled.apart (h:Walled j F a b (D.realWidth P j))(t:Walled j G b e (N.realWidth P j)):
 Disjoint (P.spacePrice D F) (P.spacePrice N G):=
 Set.disjoint_left.mpr fun _ i y=> (h.aperture i).2.not_ge (t.aperture y).1.le
lemma Walled.WallAfter (h:Walled 3 F a b (D.realWidth P 3)): P.WallAfter D F a:=fun i t=>by linarith only [(h i t).1]
lemma Walled.WallBefore (h:Walled 3 F a b (D.realWidth P 3)): P.WallBefore D F b:=fun i t=>by linarith only [(h i t).2]

variable {Q:ℕ→P.Apron}
lemma Fades.room (p:P.Fades Q)(h:Walled j F a b 0):∀ᶠ s in atTop,Walled j F a b ((Q s).realWidth P j):=by
 obtain ⟨u,v,t⟩:=h.more;exact (p.one v j).mono fun _ z=> Walled.currency t z.le
lemma Fades.stamp (p:P.Fades Q)(F:SampleDose)(h:0<e):
 ∀ᶠ s in atTop,P.spacePrice (Q s) F⊆ {y|∃i∈tsupport F.val,∀k, |y k-i k|<e}:=by
 filter_upwards [p.all h] with s t; intro y u
 obtain ⟨i,g,p⟩:=Set.mem_iUnion₂.mp u; exact ⟨i,g,fun k=>lt_of_le_of_lt (p k) (t k)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
