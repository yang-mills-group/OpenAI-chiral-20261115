import YM.SU5.Reconstruction.Quartz.Beadle
import YM.SU5.Reconstruction.Quartz.Echo
import YM.SU5.Reconstruction.Quartz.Moire
import YM.SU5.Reconstruction.Crease.Rounds
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
open YM.Quartz YM.Quartz.Waltz YM.Quartz.Ship
local notation "Qv"=> Picket.quarter j z
local notation "Lvl" i:max=>floor Y H V G C a χ i
local notation "Uj" i:max=>Picket.trans (S₀ i)
local notation "Oh" i:max=>parcelUp (S₀ i)
local notation "Wj"=> Wedge j z
local notation "Wz"=> Counter z j
local notation "M₁"=> (Lvl j) Wj
local notation "M₂"=> (Lvl z) Wz
local notation "ι"=> Z.look.conjStarAlgEquiv
local notation "Cj" i:max k:max bj:max=> Creased Y H V G C a χ F i k bj
/-- Our across-criterion asks for projection of B$' script ANY region within that translated wedge (may touch irrelevant time/space outside the fixed footprint), ability to charge in ordinary Script budgets. Not claiming it here. -/
noncomputable def hikeWorld (W:Set E4) (x:E4):Set E4:= (fun y=>y+x) '' W
include F
theorem ascentW (i:Axis)(A:(G₀ i).Op)(x:E4)(U':Set E4)(h:A∈ (Lvl i) (hikeWorld U' x)):∃ B∈ (Lvl i) U',A=(Oh i) x B:=by
 let B:=(Oh i) (-x) A; have hx:A= (Oh i) x B:=parcel_inv .. |>.symm
 exact ⟨B,(translation_cov Y H V G C a χ F i U' x B).2 (show _ from hx ▸ h),hx⟩ -- include F
omit F
-- negative contact charge geometry for script
noncomputable def ticketCrew (t:E4):Net (G₀ z):= (Lvl z) (hikeWorld Wz t)
variable (t₁ t₂:ℝ) (u v:Axis→ marks (timeMesh Λ))
structure Engages (A:(G₀ j).Op):Prop where
  positive : 0< (u z:ℝ)
  joint : ∃ (Y':(G₀ z).Op)(r:ℝ)(c:ℝ≥0), Duet Y H V G C a χ j z u v A Y'∧ Voices (S₀ z) (M:= (ticketCrew Y H V G C a χ j z (r • basis j):Set (G₀ z).Op)) Y' (( (u z:ℝ)+(v z:ℝ)).toNNReal) c
local notation "E₁"=> Engages Y H V G C a χ j z
-- main coupling properties for Rank
noncomputable def volunteer :Set (G₀ j).Op:= {x|∃ (u v:Axis→Gt),E₁ u v x}
noncomputable def CrewCost :Prop:= Dense (Submodule.span ℂ { t:(G₀ j)|∃ x∈ (volunteer Y H V G C a χ j z), ∃ q:E4,t=(Uj j) q (x (Ω₀ j))} :Set (G₀ j))
-- first obtained equivalences
local notation "Xx"=> volunteer Y H V G C a χ j z
include p
lemma movedInto (x:E4) : (ι) ((Uj j) x) = (Uj z) (Qv x):=by
 ext1 v; obtain ⟨v,rfl⟩:=Z.look.surjective v; rw[LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact DFunLike.congr_fun (p.both x) v
lemma carries_shift (x:E4)(A:(G₀ j).Op): (Oh z) (Qv x) ((ι) A)=(ι) ((Oh j) x A):=by
 unfold parcelUp; rw [map_mul,map_mul,movedInto Y H V G C a χ j z b Z p,movedInto Y H V G C a χ j z b Z p,show Qv (-x)= -Qv x from ?_];
 ext1 i; rw [PiLp.neg_apply]; have hv:=Picket.quarter_gear b.symm; by_cases hz:i=j
 · subst i; rw[(hv x).2.1,(hv _).2.1,PiLp.neg_apply]
 by_cases H :i=z
 · subst i; rw[(hv x).1,(hv _).1,PiLp.neg_apply]
 rw[(hv x).2.2 i hz H,(hv _).2.2 i hz H, PiLp.neg_apply]
lemma quarterCare (r:ℝ): Picket.quarter j z (r • basis z)= -(r • basis j):=by
 let x:=r • basis z; have h:= Picket.quarter_gear b.symm x;
 change Qv x= _; ext1 i; by_cases q:i=z; · subst i; rw[h.1]; simp [x,b,b.symm]
 by_cases t:i=j; · subst i; rw[h.2.1]; simp[x]
 rw[h.2.2 i t q]; simp [x,t,q]
include F
lemma awake_cl (x:(G₀ j).Op)(v:x∈ volunteer Y H V G C a χ j z): x∈ M₁:=by
 obtain ⟨u,vv,h⟩:=v; obtain ⟨Y',-,ω,hx,s⟩:= h.joint; obtain ⟨x',h1,Q',T,a',r,e'⟩:= hx.uses; exact point_awake Y H V G C a χ F j z b _ (⟨u,vv,x,hx.pose, (⟨hx.posv,h1,x',Q',a',r,e'.1⟩), Or.inl rfl⟩)
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
