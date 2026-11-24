import YM.SU5.Aria.Impresario
import YM.SU5.Aria.Euphony
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
variable (k:Trans j) (D:P.Apron)
local notation "B"=> P.fansM j x k
local notation "k✩"=> D.kiss P k.val
local notation "κ"=> P.enter j x
local notation "ρ"=> P.wealth j x
local notation "W"=> P.cartage j x
local notation "V" p:max=> P.tableau j x p (D.engine P j x)
lemma cart_reverses (p:Vantage): ContinuousLinearMap.adjoint (W p)=W (-p):=by
 let U:= W p; let V':= W (-p); let U₀:= (show (Χ).space→ₗᵢ[ℂ] (Χ).space from {U.toLinearMap with norm_map':= P.cart_norm j x p})
 ext1 v; apply ext_inner_right ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_left]; have ht:U₀ (V' v)=v:=by change W p (W (-p) v)=v; rw [←ContinuousLinearMap.comp_apply, ←P.cart_paves,add_neg_cancel,P.cart_zero]; rfl
 exact (congrArg (fun u=>inner ℂ u (U y)) ht.symm).trans (U₀.inner_map_map ..)
lemma cart_mirror (p:Vantage): W (mirrorΩ j p)= W p:= by
 apply congrArg ((P.voyageF j x).aviation (daylight (timeMesh P.par)) (look j)); funext i
 exact if_neg i.property
lemma bank_star : (ρ).adjoint=(κ).toContinuousLinearMap:=by
 have h:(ρ)=(P.Viewers j x).orthogonalProjectionOnto:=by ext1 i; apply Subtype.ext; exact DFunLike.congr_fun (P.visitors_op j x) i
 rw [h]; exact Submodule.adjoint_orthogonalProjectionOnto (P.Viewers j x) -- tune
private lemma stardom {G H:Hilbert}(b:G→L[ℂ]H)(u:H→L[ℂ] G)(t:u.adjoint=b) : b.adjoint=u:=by rw [←t,ContinuousLinearMap.adjoint_adjoint]
lemma boards_star (p : Vantage)(A:(X).Op): ContinuousLinearMap.adjoint (P.tableau j x p A)=P.tableau j x p A.adjoint:=by
 let K':=(κ).toContinuousLinearMap; let U:=W p; let U':=W (-p); unfold tableau; simp only [ContinuousLinearMap.adjoint_comp,P.cart_reverses,P.bank_star,stardom (κ).toContinuousLinearMap (ρ) (P.bank_star j x),neg_neg]; rfl
lemma lives_twin (p:Vantage): star (P.tableau j x p (D.engine P j x))= P.tableau j x (mirrorΩ j p) ((D.kiss P j).engine P j x):=by
 rw [← D.peer P j x]; change ContinuousLinearMap.adjoint (V p)=_; rw [P.boards_star]; unfold tableau; simp only [← mirrorΩ_neg,P.cart_mirror]; rfl
lemma fan_comfort (u v:Χ): inner ℂ (B u) (B v) = star (inner ℂ u v):= P.blade_angle j x k _ _

section stories
variable {I:Type*}(A:I→P.Apron)(p:I→ Vantage)(L:List I)
def resizeMirror (j:Axis)(p:I→Vantage):I→Vantage:=fun i=>mirrorΩ j (p i)
def veilMirror (j:Axis) : I→P.Apron:=fun i=>(A i).kiss P j
local notation "A✩" y:max=> P.veilMirror A y
local notation "p✩" y:max=> resizeMirror y p
local notation "u✩" A:max p:max=>P.porchY j A p
local notation "v✩" A:max p:max=>P.resignY j A p
local notation "u₀"=> u✩ A p
local notation "v₀"=> v✩ A p
local notation "L₀" p:max q:max=> P.commuteTight j x p q
local notation "λ'"=>L₀ A p
lemma worldPose : u✩ (A✩ j) (p✩ j)= -v₀ ∧ v✩ (A✩ j) (p✩ j)= -u₀:=by
 have he(i:I):(p✩ j) i j= -(p i j) :=if_pos rfl; constructor <;> funext i
 · change (p✩ j) i j- (A i).realWidth P j= -v₀ i; rw [he]; unfold resignY Apron.time_edge; abel
 change (p✩ j) i j+(A i).realWidth P j=-u₀ i; rw [he]; unfold porchY Apron.time_panel; abel
lemma wingPose : u✩ (A✩ k.val) (p✩ k.val)=u₀ ∧ v✩ (A✩ k.val) (p✩ k.val)=v₀:= by
 have he(i:I): mirrorΩ k.val (p i) j=p i j:= if_neg (Ne.symm k.property)
 constructor <;> funext i
 · change mirrorΩ k.val (p i) j-(A i).realWidth P j= _; rw [he]
 change mirrorΩ k.val (p i) j+(A i).realWidth P j=_; rw [he]
lemma wingOrder (t:P.Turnstile j A L p): P.Turnstile j (P.veilMirror A k.val) L (resizeMirror k.val p):=by
 unfold Turnstile; rw [(P.wingPose j k A p).1,(P.wingPose j k A p).2]; exact t
lemma tempestOrder (t:P.Turnstile j A L p): P.Turnstile j (P.veilMirror A j) L.reverse (resizeMirror j p) :=by
 unfold Turnstile; rw [(P.worldPose j A p).1,(P.worldPose j A p).2, List.pairwise_reverse]; exact t.imp fun {_ _} h=>neg_lt_neg h
-- word intertwinement and adjoint; can keep CHAT for cross Gram. chronological ordering semantics needed only for adjoint below. (Non-PSD region not purchased.)
local notation "E" A:max p:max L:max b:max c:max=> Aria.pinch (ν) (u✩ A p) (v✩ A p) (L₀ A p) L b c
lemma corresponding_wing (b c:ℝ)(v:Χ): (E (A✩ k.val) (p✩ k.val) L b c) (B v)= B ((E A p L b c) v):=by
 rw [(P.wingPose j k A p).1,(P.wingPose j k A p).2]; induction L generalizing b with
 | nil=> exact (P.fan_stare ..).symm
 | cons i L ih=>
   rw [Aria.pinch,Aria.pinch]; simp only [ContinuousLinearMap.comp_apply, P.fan_stare,ih]; apply congrArg; exact ((A i).swirl ..).symm
lemma adjourning_wing (b c:ℝ)(h:Chat (u₀) (v₀) L b c) : (E (A✩ j) (p✩ j) L.reverse (-c) (-b))=star (E A p L b c):=by
 let X₀:=fun i=>(λ') i; obtain ⟨f,y⟩:= card_flip (ν) (u₀) (v₀) X₀ L b c h
 rw [(P.worldPose j A p).1, (P.worldPose j A p).2, show (L₀ (A✩ j) (p✩ j))=(fun i=> star (X₀ i)) from funext fun i=> (P.lives_twin ..).symm]; exact y
lemma wing_solution (t:P.Turnstile j A L p): P.memorial j x (P.veilMirror A k.val) L (resizeMirror k.val p)=star (P.memorial j x A L p):=by
 unfold memorial; rw [← paid (ν) _ _ _ Ω (P.heaven_hot j x) L 0 0,← paid (ν) _ _ _ Ω (P.heaven_hot j x) L 0 0]; let U:= E (A✩ k.val) (p✩ k.val) L 0 0 -- syntax numbers as args
 conv_lhs => rw [← P.fan_empty j x k]; -- simp changed both
 rw [P.corresponding_wing, P.fan_comfort]
lemma tempest_solution (t:P.Turnstile j A L p): P.memorial j x (P.veilMirror A j) L.reverse (resizeMirror j p)=star (P.memorial j x A L p):=by
 obtain ⟨b,h⟩:=weaves_sorted _ _ L t; obtain ⟨c,h⟩:=slim_pinch _ _ _ _ h; unfold memorial; rw [← paid (ν) _ _ _ Ω (P.heaven_hot j x) L.reverse (-c) (-b), ← paid (ν) _ _ _ Ω (P.heaven_hot j x) L b c, P.adjourning_wing j x A p L b c h]; let v:= E A p L b c
 change inner ℂ Ω (v.adjoint Ω)=_; rw [ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm ..).symm -- direction tune
end stories
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.tempest_solution
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.wing_solution
