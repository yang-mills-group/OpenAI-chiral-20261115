import YM.SU5.ThinInteraction.Resolution
/-!
The `deploy` quadrature for reflected cross products. A useful alternative porting route
for this restriction of our answer tests. See also `Six/FineRays`, `PressSmear`; parts below
import/adapt (e.g. proof of `P.birthSum` and of `intoGrid`).
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 220000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
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
open YM.SatinThin
namespace Thinning
open Set Aria Six Casting
open scoped BigOperators
variable (P:Spine) (x:P.Spectrum0 3) (s n t:ℕ) (Z:Lead.Clan)
local notation "S" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "W" => ShopP P s n
local notation "T" => timeMesh P.par
local notation "d" r:max => offset false r
local notation "τ" => P.probeWidth s n 3
local notation "M" => P.singleState 3 t x
local notation "A" => P.FTest Z s n
local notation "Y" => P.RTest Z s n
section
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "E" => (P.physicalEnergy 3 ξ).E
local notation "H₀" => P.ColorHil 3 ξ
local notation "H" => P.ManyF 3 ξ
local notation "u" => P.truck 3 ξ
local notation "f₀" => P.filterVector x s n Z
local notation "v₀" => alk s n x Z false
local notation "ι" => P.enter 3 ξ
local notation "ϑ" => P.wealth 3 ξ
local notation "θ" => P.macroStep t
-- avoid rich simp on stitched terms
variable {P x s n Z}{a:ℝ} (p:Portfolio x s n a Z)(c:ShopP P s n →₀ℝ) (F:SampleDose) (J:P.Ellis 3 x)

private lemma sumTraces {V V' : Type} [AddCommMonoid V] [AddCommMonoid V']
    (R : V → V' → Prop) (p : R 0 0) (h : ∀ a b t u', R a t → R b u' → R (a+b) (t+u'))
    {d₀: Type}(J:Finset d₀)(f:d₀→V)(g:d₀→V') (e:∀ i∈J, R (f i) (g i)):
    R (∑ i∈J,f i) (∑ i∈J,g i):=by
  induction J using Finset.induction_on with
  | empty=> rwa [Finset.sum_empty,Finset.sum_empty]
  | @insert x L v ih=> rw [sum_insert v,sum_insert v]; exact h _ _ _ _ (e x (mem_insert_self ..)) (ih (fun i k=> e i (mem_insert_of_mem k)))
private lemma originSum {d₀:Type} (J:Finset d₀) (f:d₀→ P.Test)(g:d₀→ H₀)
    (e:∀ i∈J,∃ h:P.birthF 3 t (f i), P.viewF 3 ξ t h = g i): ∃ h:P.birthF 3 t (∑ i∈J,f i), P.viewF 3 ξ t h=∑i∈J,g i:=by
  refine sumTraces (fun f g=> ∃ h:P.birthF 3 t f, P.viewF 3 ξ t h=g) ?_ ?_ J f g e
  · let t':=P.faceUnit 3 t
    let h':= P.birthScale t 0 t'
    have h:P.birthF 3 t 0:= Eq.mp (congrArg (P.birthF 3 t) (zero_smul ℂ (1:P.Test))) h'
    exact ⟨h, (P.identical_F 3 ξ t h h' (zero_smul ..).symm).trans ((P.sixWard_view_scale ξ t 0 t').trans (zero_smul ..))⟩
  rintro a b v w ⟨h,l⟩ ⟨g,k⟩; exact ⟨P.birthAdd t h g,(P.view_plus ξ t h g).trans (congrArg₂ (·+·) l k)⟩

private lemma paysConstant {f:P.Test}{q:H₀} (w:ℂ)(e:∃ h:P.birthF 3 t f,P.viewF 3 ξ t h=q): ∃ h': P.birthF 3 t (w • f), P.viewF 3 ξ t h'= w • q:=by
  obtain ⟨h,y⟩:= e
  exact ⟨P.birthScale t w h,(P.sixWard_view_scale ξ t w h).trans (congrArg (fun x:H₀=> w • x) y)⟩

def momentGap (r:ShopP P s n)(i:Vantage):ℝ≥0:=(i 3+offset false r).toNNReal
def beforePay (i:Vantage): H₀ := pp p i • ∑ r∈ c.support, ((c r:ℝ):ℂ) • E (momentGap r i) f₀
def docket : H₀:= ∑ i∈P.usedGrid t F, P.activation t F i • P.truck 3 ξ (P.vtile t i) (beforePay p c (P.meshPose t i))
private lemma shifted_ray (i:Cover)(r:W)(v:invests t r) :
    P.hotRead t x Z s n 0 (putCharge t r i) = u (P.vtile t i) (E (momentGap r (P.meshPose t i)) f₀):=by
  have h': (P.meshPose t (putCharge t r i) 3-0).toNNReal=momentGap r (P.meshPose t i):= congrArg Real.toNNReal ((sub_zero _).trans (markHeight t r i v))
  exact congrArg₂ (fun (U:(H₀).Op) (b:ℝ≥0)=> U (E b f₀)) (markTruck t r i ξ) h'
private lemma in_direction (i:Cover)(e:2*τ < P.meshPose t i 3)(v:s≤t)(r:W)(x':invests t r)(a:ℂ) :
    let k:=putCharge t r i; let q:=momentGap r (P.meshPose t i); ∃ h:P.birthF 3 t (a • P.issuing t A k), P.viewF 3 ξ t h=u (P.vtile t i) (a • E q f₀):= by
  let e₁:=P.manifestRead t x Z s n (putCharge t r i) (width_paid t r i e x') v
  let y:= u (P.vtile t i); let w:=E (momentGap r (P.meshPose t i)) f₀
  have ht:=P.sixWard_view_scale ξ t a e₁.choose
  exact ⟨P.birthScale t a e₁.choose,ht.trans ((congrArg (fun x':H₀=> a • x') (e₁.choose_spec.trans (shifted_ray (x:=x) (Z:=Z) t i r x'))).trans (map_smul y a w).symm)⟩
private lemma one_center (i:Cover)(e:2*P.probeWidth s n 3 < P.meshPose t i 3)(v:covered t c):
    ∃ h:P.birthF 3 t (chargePlus t p c i),P.viewF 3 ξ t h= u (P.vtile t i) (beforePay p c (P.meshPose t i)):=by
  let s':=P.meshPose t i; let a₀:= pp p s'; let M':=u (P.vtile t i); let V (r:W):= E (momentGap r s') f₀; let z (r:W):= V r
  let g (r:W):= P.issuing t A (putCharge t r i); let w (r:W):= V r; let U (r:W):ℂ:= (c r:ℝ)
  let f:=∑ r∈ c.support, U r • g r; let v' := ∑ r ∈ c.support, M' (U r • z r)
  have ht (r:W)(x':r∈c.support) : ∃ h:P.birthF 3 t (U r • g r),P.viewF 3 ξ t h=M' (U r • z r):=
    in_direction (x:=x) (Z:=Z) t i e v.1 r (v.2 r x') _
  have hz : M' (beforePay p c s') = a₀ • v' := (map_smul M' a₀ (∑ r∈c.support,U r • z r)).trans (congrArg (fun x:H₀=> a₀ • x) (map_sum M' _ _))
  have e₁:= (show ∃ h:P.birthF 3 t f, P.viewF 3 ξ t h=v' from originSum t _ _ _ ht)
  exact ⟨P.birthScale t a₀ e₁.choose,(P.sixWard_view_scale ξ t a₀ e₁.choose).trans ((congrArg (fun x:H₀=> a₀ • x) e₁.choose_spec).trans hz.symm)⟩
lemma worldly (e:roofed P s n F) (v:covered t c):
    ∃ h:P.birthF 3 t (deploy t F p c),P.viewF 3 ξ t h= docket t p c F:= by
 let Y':= P.usedGrid t F
 let η(i:Cover):=P.activation t F i; let k(i:Cover):= u (P.vtile t i) (beforePay p c (P.meshPose t i))
 exact originSum t (x:=x) Y' (fun i=>η i • chargePlus t p c i) (fun i=> η i • k i) (fun i a=> paysConstant t _ (one_center t p c i (e _ ((P.usedPose t F i).1 a)) v))
lemma onPair (e:roofed P s n F) (v:covered t c) {b:ℝ}{g:Lead.Clan}
    (p':Portfolio x s n b g) (c':ShopP P s n→₀ℝ) (G:SampleDose)(m:roofed P s n G) (d':covered t c'):
    M (P.reflectTest 3 (deploy t F p c) * deploy t G p' c')= inner ℂ (docket t p c F) (docket t p' c' G):=by
  let h := worldly t p c F e v; let v':= worldly t p' c' G m d'
  exact ((P.single_agrees 3 3 x t _).symm.trans (P.released_gram 3 ξ t h.choose v'.choose).symm).trans (congrArg₂ (inner ℂ) h.choose_spec v'.choose_spec)
-- `docket` gives elected continuum price after refining.
open MacroGrid
private lemma intoGrid (P:Spine)(X:Hilbert)(f:Vantage→X)(R:Cover → X.Op):
 poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) R (P.macroStep t) =∑ i∈ P.usedGrid t F, P.activation t F i • R i (f (P.meshPose t i)):=by
 let g:=fun i:Cover=> R i ((F.val (P.meshPose t i):ℂ) • f (P.meshPose t i))
 have he(i:Cover)(x:i∉P.usedGrid t F): g i=0:= by
    have hu : F.val (P.meshPose t i)=0:=by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
 refine (room_price (P.macroStep t) (P.macroStep_pos t) g (P.usedGrid t F) he).2.trans ?_
 rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h; unfold g; rw [map_smul,show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((P.macroStep t)^4), smul_smul]; push_cast [activation]; rfl

def paid : H:= ∫ z:Vantage, P.cartage 3 ξ z (P.wealth 3 ξ ((F.val z:ℂ) • beforePay p c z))
lemma cont_before : Continuous (beforePay p c) := by
  apply (pp_cont p).smul; refine continuous_finsetSum _ (fun i _=> show Continuous _ from Continuous.const_smul ?_ ((c i:ℝ):ℂ))
  exact ((P.physicalEnergy 3 ξ).continuousE f₀).comp (by unfold momentGap; fun_prop)
include J
lemma till_paid : Tendsto (fun t=> docket t p c F) atTop (𝓝 (ι (paid p c F))) := by
  let f:= beforePay p c; let g x:=(F.val x:ℂ) • f x
  have h : HasCompactSupport g := F.budget.mono (fun i k t=>k ((congrArg (fun b:ℝ=> (b:ℂ) • f i) (show F.val i=0 from t)).trans (zero_smul ..)))
  have he:Continuous g := (Complex.continuous_ofReal.comp F.smooth.continuous).smul (cont_before p c)
  exact (P.macroRiemann x 3 J g h he).congr fun i=> intoGrid i F P H₀ f _
omit J
end
#print axioms onPair
#print axioms till_paid
end Thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
