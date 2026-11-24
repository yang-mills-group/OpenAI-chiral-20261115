import SatinFixedContrastNovember4
import YM.SU5.Thin.Compound

set_option autoImplicit false
set_option maxHeartbeats 190000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
/-!
# layout prices from convergent operators in the hierarchy

Grid refinement and intrinsic-width removal strictly two-stage here. Don't allow
sum costs on not-time-ordered combinations. But on all these, get the strong
operator-product prices as well on the elected `H` for every input vector, with
same widths and costs. No use of cost bound on an unelected spectrum (until using
the norm of its `BoxOp`), no factor hypothesis on the Satin vacuum, and not using
products priced some other way. (No license for contact values.)
-/
open DoseBill Sifter VoucherOp
namespace Theatre
variable {I:Type*}
private lemma together (X Y:Hilbert)(F:X→ₗᵢ[ℂ]Y)(S:ℕ→ I→ Y.Op)(T:I→ X.Op) (L:List I)(x:X)
    (t:∀ i∈L,∀ z:X,Tendsto (fun k=> S k i (F z)) atTop (𝓝 (F (T i z))))
    (f:∀ i∈L,∃ p:ℝ,∀ᶠ v:ℕ in atTop,‖S v i‖≤ p):
    Tendsto (fun t:ℕ=> word (S t) L (F x)) atTop (𝓝 (F (word T L x))):=by
  induction L with
  | nil=> exact tendsto_const_nhds
  | cons i l ih=>
     obtain ⟨r,p⟩:= f i List.mem_cons_self
     have hu:= ih (fun j v=>t j (List.mem_cons_of_mem _ v)) (fun j v=> f j (List.mem_cons_of_mem _ v))
     obtain ⟨n,h⟩:= p.exists; exact firmly (fun n=> S n i) ((norm_nonneg _).trans h) p (t i List.mem_cons_self (word T l x)) hu
private lemma quote_book (X Y:Hilbert)(ω:X)(F:X→ₗᵢ[ℂ]Y)(v:ℕ→ Y.Op)(u:X.Op)(L:ℕ→ℂ)
    (g:Tendsto (fun i=>v i (F ω)) atTop (𝓝 (F (u ω)))) (e:∀ᶠ i in atTop,L i=markVoice Y (F ω) (v i)): Tendsto L atTop (𝓝 (markVoice X ω u)):=by
  let S(i):=inner ℂ (F ω) (v i (F ω)); have ht:Tendsto S atTop (𝓝 (inner ℂ (F ω) (F (u ω)))):= (tendsto_const_nhds (x:=F ω)).inner g; rw [F.inner_map_map] at ht; exact ht.congr' (e.mono fun _ w=>w.symm)
variable {P:Spine}(x:P.Spectrum0 3){J:P.Ellis 3 x}{b:ℕ→ℕ}{n:ℕ}
variable (Z:I→Lead.Clan)(D:∀ i:I,P.VoucherOp x (Z i) n b)(w:I→Bool)(s:I→ℕ)(f:I→ SampleDose)(lo hi:I→ℝ)(L:List I)(e:Ordered L lo hi)
local notation "ξ"=> P.advocate 3 x 3
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ν"=> P.heaven 3 ξ
local notation "κ"=> P.enter 3 ξ
local notation "Ψ" p:max k:max i:max=> (D i).mixedGrid (w i) (p i) k (f i) (lo i) (hi i)
local notation "Ω" p:max i:max=> (D i).workingOp (w i) (p i) (f i) (lo i) (hi i)
local notation "ζ" i:max=> (D i).thinOp (w i) (f i) (lo i) (hi i)
local notation "Ṗ" p:max l:max=> measuredPrice x Z D w p f l
local notation "C" i:max=> (D i).bound
local notation "T" i:max k:max=> (D i).cost (s i)

abbrev finished0 :(P.ManyF 3 ξ).Op:= word (fun i=> Ω s i) L
abbrev poseGrid (t:ℕ) :(P.ColorHil 3 ξ).Op := word (fun i=> Ψ s t i) L
abbrev finished :(P.ManyF 3 ξ).Op:= word (fun i=> ζ i) L
abbrev answer := markVoice H ν (finished x Z D w f lo hi L)
abbrev tentativePrice := markVoice H ν (finished0 x Z D w s f lo hi L)
local notation "𝓔" p:max=> tentativePrice x Z D w p f lo hi L
local notation "𝓦"=> answer x Z D w f lo hi L
variable (J)
include J
lemma authority (u:SureFoot x Z D w s f lo hi L)(y:P.ManyF 3 ξ) : Tendsto (fun t:ℕ=> poseGrid x Z D w s f lo hi L t (κ y)) atTop (𝓝 (κ (finished0 x Z D w s f lo hi L y))):=by
  apply together H H' κ (fun t i=>Ψ s t i) (fun i=>Ω s i) L y (fun i _ x=>(D i).working_grid J (w i) (s i) (f i) (lo i) (hi i) x)
  intro i _
  refine ⟨(along (f i)+1)* C i, ((P.totalVariation_dose (f i)).eventually (ge_mem_nhds (show along (f i)< along (f i)+1 from lt_add_one _))).mono ?_⟩
  intro t v; exact ((D i).mixedCap (w i) (s i) t (f i) (lo i) (hi i)).trans (mul_le_mul_of_nonneg_right v ((norm_nonneg _).trans ((D i).uniformOp 0)))
include e
theorem gridInvest (u:SureFoot x Z D w s f lo hi L) : Tendsto (Ṗ s L) atTop (𝓝 (𝓔 s)) := quote_book H H' ν κ _ _ _
     (authority x J Z D w s f lo hi L u ν) ((apricot x Z D s L).mono fun i t=> live x Z D w s f lo hi L e i t u)
omit J e
variable (v:ℕ→I→ℕ)(t:∀ i∈L, Tendsto (fun n=>v n i) atTop atTop)(p:∀ i∈ L, ReadyThin (f i) (lo i) (hi i))
include t p
lemma safetyPlan : ∀ᶠ i in atTop,SureFoot x Z D w (v i) f lo hi L:=by
  classical
  filter_upwards [ (Filter.eventually_all_finset L.toFinset).2 fun i t₁ => (t i (List.mem_toFinset.mp t₁)).eventually ((D i).readyCosts (w i) (f i) (lo i) (hi i) (p i (List.mem_toFinset.mp t₁))) ] with i h
  exact fun b p k _=> h _ (List.mem_toFinset.mpr p) k
lemma widthInvest (y:P.ManyF 3 ξ) : Tendsto (fun i=> finished0 x Z D w (v i) f lo hi L y) atTop (𝓝 (finished x Z D w f lo hi L y)) :=
  let a: (H)→ₗᵢ[ℂ]H:=LinearIsometry.id
  together H H a (fun t i=>Ω (v t) i) (fun i=>ζ i) L y
       (fun i u x=> ((D i).field_pass (w i) (f i) (lo i) (hi i) (p i u) x).comp (t i u))
       (fun i _=> ⟨_,Eventually.of_forall fun n=> (D i).workingBound (w i) (v n i) (f i) (lo i) (hi i)⟩)
theorem atFinal : Tendsto (fun t=> tentativePrice x Z D w (v t) f lo hi L) atTop (𝓝 (𝓦)) :=
  (tendsto_const_nhds (x:=ν)).inner (widthInvest x Z D w f lo hi L v t p ν) -- inner linear
end Theatre
#print axioms Theatre.gridInvest
#print axioms Theatre.atFinal
#print axioms Theatre.safetyPlan
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
