import Mathlib.Analysis.InnerProductSpace.GramMatrix
import YM.SU5.Aria.Silhouette
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "ν"=> P.seasons j x
local notation "ψ"=> P.physicalEnergy j x
local notation "Ω"=> P.heaven j x
local notation "E"=> (P.seasons j x).E
local notation "W"=> P.cartage j x
local notation "V"=> P.tableau j x
local notation "ρ"=> P.wealth j x
local notation "κ"=> P.enter j x
abbrev Model0 := P.Apron × Vantage
local notation "A"=>P.Model0
local notation "Σ₀"=> Prod.fst (α:=P.Apron) (β:=Vantage)
local notation "Σ₁"=> Prod.snd (α:=P.Apron) (β:=Vantage)
def rayFare := P.porchY j (Σ₀) Σ₁
def rayExit := P.resignY j (Σ₀) Σ₁
local notation "u"=>P.rayFare j
local notation "v"=>P.rayExit j
def turnModel (a:P.Model0): P.Model0:= (a.1.kiss P j, mirrorΩ j a.2)
local notation "T"=>P.turnModel j
local notation "σ"=>P.commuteTight j x Σ₀ Σ₁
lemma turnModels (a:P.Model0): u (T a) = - v a∧ v (T a)= - u a:=⟨congrFun (P.worldPose j Σ₀ Σ₁).1 a, congrFun (P.worldPose j Σ₀ Σ₁).2 a⟩
lemma turn_model_paid (a:P.Model0): σ (T a)=star (σ a):=(P.lives_twin ..).symm
local notation "Ξ"=> List (P.Model0)
def Crest0 := {l: List (P.Model0)|∀ i∈l,0<P.rayFare j i}
def roll0 := {l:List (P.Model0)|P.Turnstile j Σ₀ l Σ₁}
def eWord (y: P.Model0):=y -- spacing syntax
lemma crest_paid {l:Ξ}(c:l∈P.Crest0 j)(v':l∈P.roll0 j): Sheet u v l 0:=by
 obtain ⟨b,p⟩:=weaves_sorted _ _ l (show l.Pairwise _ from v'); cases l with
 | nil=>trivial
 | cons i l=> exact ⟨c _ (List.Mem.head ..),(show _ ∧ _ from p).2⟩
lemma turn_tide {l:Ξ}(t:l∈P.roll0 j): (l.reverse.map (P.turnModel j))∈ P.roll0 j:=by
 change List.Pairwise (fun i k => v i < u k) _; rw [List.pairwise_map, List.pairwise_reverse]; apply List.Pairwise.imp _ t; intro i k h; change v (T k)<u (T i); rw [(P.turnModels j k).2,(P.turnModels j i).1]; exact neg_lt_neg h
abbrev joinHeight (U Z: List P.Model0):= U.reverse.map (P.turnModel j) ++ Z
lemma concat_toRank {l B}(t:l∈P.roll0 j)(p:l∈P.Crest0 j)(r:B∈P.roll0 j)(x:B∈P.Crest0 j): P.joinHeight j l B∈P.roll0 j:= List.pairwise_append.mpr ⟨P.turn_tide j t,r,fun i y k w=>by
 obtain ⟨i,z,rfl⟩:= List.mem_map.mp y; change v (T i)<u k; rw [(P.turnModels ..).2]; exact (neg_neg_of_pos (p i (List.mem_reverse.mp z))).trans (x _ w)⟩
section manip
variable {I B:Type*}{H:Hilbert}(S:OS.Semigroup H j)(X':I→H.Op)(f g:I→ℝ)(p:B→I)(l:List B)
private lemma chat_map (b c:ℝ): Chat f g (l.map p) b c↔ Chat (f ∘ p) (g ∘ p) l b c:=by induction l generalizing b with
 | nil=> rfl
 | cons i l h=> change (_∧ Chat f g (l.map p) _ c)↔ _; rw [h]; rfl
private lemma pinch_map (b c:ℝ): Aria.pinch S f g X' (l.map p) b c= Aria.pinch S (f ∘ p) (g ∘ p) (X'∘ p) l b c:=by induction l generalizing b with
 | nil=> rfl
 | cons i l h=> rw [List.map_cons, Aria.pinch,h]; rfl
end manip
variable (L B:List (P.Model0)) (h:L∈P.roll0 j)(g:B∈P.roll0 j)(c:L∈P.Crest0 j)(d:B∈P.Crest0 j)
def parses := rector (ν) (P.commuteTight j x Σ₀ Σ₁) (P.rayFare j) (P.rayExit j) L 0 Ω
local notation "ν✩" L:max b:max c:max=> pinch (ν) u v σ L b c
lemma joinedMajor (c:ℝ)(h':Chat (P.rayFare j) (P.rayExit j) L 0 c):
    Chat u v (L.reverse.map T) (-c) 0 ∧ (ν✩ (L.reverse.map T) (-c) 0)=star (ν✩ L 0 c):=by
 obtain ⟨t,b⟩:=card_flip (ν) u v σ L 0 c h'; rw [neg_zero] at t b; have hx:u ∘ T= -v:=funext fun i=> (P.turnModels ..).1; have ht:v ∘ T= -u:= funext fun i=>(P.turnModels ..).2
 rw [chat_map, pinch_map,hx,ht,show σ ∘ T=(fun i=> star (σ i)) from funext (fun i=> P.turn_model_paid ..)]
 exact ⟨t,b⟩
include h c g d
lemma common_self : inner ℂ (P.parses j x L) (P.parses j x B)= P.memorial j x Σ₀ (P.joinHeight j L B) Σ₁:=by
 obtain ⟨w,t⟩:=slim_pinch _ _ _ _ (P.crest_paid j c h); obtain ⟨y,a⟩:= slim_pinch _ _ _ _ (P.crest_paid j d g)
 let S:= ν✩ L 0 w; let m:= ν✩ B 0 y
 have he:(ν✩ (P.joinHeight j L B) (-w) y)=(star S).comp m:= (pin_board (ν) u v σ _ _ (P.joinedMajor j x L w t).1 a).2.trans (congrArg (fun x:(P.ManyF j x).Op=>x.comp m) (P.joinedMajor j x L w t).2)
 refine (Eq.trans ?_ (paid (ν) u v σ Ω (P.heaven_hot j x) (P.joinHeight j L B) (-w) y)); rw [he, ContinuousLinearMap.comp_apply]
 have hS: S Ω=P.parses j x L:= pays (ν) u v σ (P.heaven_hot j x) L 0 w; have hm: m Ω=P.parses j x B:= pays (ν) u v σ (P.heaven_hot j x) B 0 y
 rw [←hS,←hm]; exact (ContinuousLinearMap.adjoint_inner_right S Ω (m Ω)).symm
omit h c g d
/-- reflection PSD on arbitrary arranged words in positive slabs (needn't be uniformly at the same fixed volume/shape).
    We deliberately test `commonWell` (multi-axis system) here. -/
abbrev Posy := ↥(P.Crest0 j∩P.roll0 j)
variable (k:Axis)
def duo (x':P.Posy k)(y:P.Posy k):ℂ := P.commonWell j x Σ₀ Σ₁ (P.joinHeight k x'.val y.val)
lemma duo_positive (J:P.Ellis j x){I:Type*}[Fintype I](b:I→P.Posy k):
    Matrix.PosSemidef (Matrix.of fun i y=> P.duo j x k (b i) (b y)) := by
 let Z:= P.ManyF k (P.advocate j x k); let B (i:I): Z:= P.parses k (P.advocate j x k) (b i).val; refine Eq.mp ?_ (Matrix.posSemidef_gram ℂ B) -- ? approach ↔ no
 refine congrArg Matrix.PosSemidef ?_; ext1 i y; exact (P.common_self k (P.advocate j x k) _ _ (b i).property.2 (b y).property.2 (b i).property.1 (b y).property.1).trans (P.common_cult j x _ _ _ J (List.Perm.refl _) (P.concat_toRank k (b i).property.2 (b i).property.1 (b y).property.2 (b y).property.1)).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.duo_positive
