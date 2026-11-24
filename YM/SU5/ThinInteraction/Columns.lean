import YM.SU5.ThinInteraction.Sampling
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
local notation "H'" => P.ColorHil 3 ξ
local notation "L" => P.ManyF 3 ξ
local notation "E" => (S).E
local notation "E'" => (P.physicalEnergy 3 ξ).E
local notation "Π'" => P.wealth 3 ξ
local notation "U" y:max => P.cartage 3 ξ y
local notation "φ" => P.filterVector x s n Z
local notation "ω" => P.sixWard_macroVector x s n Z
local notation "h" => 2*τ

variable {P x s n Z}{a:ℝ}(p:Portfolio x s n a Z)(F:SampleDose)(c:ShopP P s n →₀ℝ)

def transit (P:Spine)(s n:ℕ)(i:Vantage):ℝ≥0:=(i (3:Axis)-2*P.probeWidth s n 3).toNNReal
local notation "w" => (τ).toNNReal
private lemma time_shift {i : Vantage}(r:ShopP P s n)(hi:h < i (3:Axis)):
    momentGap r i = transit P s n i+ (whenFocus false r + (τ).toNNReal) := by
  ext
  rw [momentGap,Real.coe_toNNReal, NNReal.coe_add, NNReal.coe_add, timing, Real.coe_toNNReal _ (P.width_here s n 3).le]
  · rw [transit, Real.coe_toNNReal _ (sub_nonneg.mpr hi.le)]; ring
  exact (P.width_here s n 3).le.trans (width_paid' r hi).le -- arguments?
private lemma three_heats (X:Hilbert)(v:OS.Semigroup X (3:Axis))(x:X) {q a b c:ℝ≥0}(e:c=a+(b+q)): v.E c x=v.E a (v.E b (v.E q x)) := by rw [e,v.time,v.time]; rfl
lemma projection_move (r:ShopP P s n)(i:Vantage)(hi:h < i (3:Axis)) :
    Π' (E' (momentGap r i) φ) = E (transit P s n i) (E (whenFocus false r) (alk s n x Z false)) := by
   let Q:= E (transit P s n i); let f:= E (whenFocus false r)
   exact (P.bankHeat 3 ξ (momentGap r i) φ).trans ((three_heats L S ω (time_shift r hi)).trans (congrArg (fun y:L=>Q (f y)) (P.centerEntry x s n Z).symm))
private lemma budget_sum {V:Type} (X : Hilbert)(R:Finset V) (f:V→ X.Op)(c:V→ℂ)(y:X) :
    (∑ i∈R, c i • f i) y= ∑ i∈R,c i • f i y:= by rw [_root_.sum_apply]; exact Finset.sum_congr rfl fun i _=> by simp only [_root_.smul_apply]
private lemma offset_balance (i:Vantage) (hi:h < i (3:Axis)) :
    Π' (∑ r∈ c.support, ((c r:ℝ):ℂ) • E' (momentGap r i) φ) = E (transit P s n i) (focusing S false c (alk s n x Z false)):= by
  let K (r:W):= E' (momentGap r i); let J (r:W):= E (whenFocus false r); let x':= alk s n x Z false
  let q:= E (transit P s n i); let B:=c.support; let d₁ (r:W):ℂ:= ↑(c r:ℝ); let f(r:W):= (d₁ r • K r φ); let g(r:W):= d₁ r • J r x'
  have ht: (focusing S false c) x'=∑ r∈ B,g r:= budget_sum L B J d₁ x'
  have hp (r:W): Π' (f r)=q (g r) := (map_smul Π' (d₁ r) _).trans ((congrArg (fun v:L=> d₁ r • v) (projection_move (Z:=Z) (x:=x) r i hi)).trans (map_smul q _ _).symm)
  exact ((map_sum Π' f B).trans ((Finset.sum_congr rfl (fun r _=> hp r)).trans (map_sum q g B).symm)).trans (congrArg (fun v:L=> q v) ht.symm)

def aspect (i:Vantage) (v:L): L:= pp p i • (U i) (E (transit P s n i) v)
-- same array integral as in TeX, strictly future roof when paying the reconstruction
-- allow generic vector v to show estimates later; actual price uses focusing.
def column (v:L): L:= ∫ i:Vantage,(F.val i:ℂ) • aspect p i v
lemma column_price (e:roofed P s n F) : paid p c F= column p F (focusing S false c (alk s n x Z false)) := by
  let X:= alk s n x Z false; let Y':= focusing S false c X; let q(i):=E (transit P s n i)
  refine integral_congr_ae (Eventually.of_forall fun i=>?_)
  have hp : (U i) (Π' ((F.val i:ℂ) • beforePay p c i))=(F.val i:ℂ) • (U i) (Π' (beforePay p c i)):=by
    exact (congrArg (fun x:L => (U i) x) (map_smul (Π') (F.val i:ℂ) (beforePay p c i))).trans (map_smul (U i) (F.val i:ℂ) _)
  refine hp.trans ?_; by_cases hv:i∈ tsupport F.val
  · apply congrArg (fun x:L=> (F.val i:ℂ) • x) -- danger
    let a' := pp p i; let t:=(U i); let f(r:W):= (E' (momentGap r i)) φ
    have hx: Π' (beforePay p c i) = a' • q i Y':= (map_smul (Π') a' (∑ r∈ c.support, ((c r:ℝ):ℂ) • f r)).trans (congrArg (fun x:L => a' • x) (offset_balance (Z:=Z) (x:=x) c i (e i hv)))
    exact (congrArg (fun x:L => t x) hx).trans (map_smul t a' _)
  have hx:(F.val i:ℂ)=0:= Complex.ofReal_eq_zero.mpr (show F.val i=0 from image_eq_zero_of_notMem_tsupport hv)
  simp only [hx,zero_smul]
variable (J:P.Ellis 3 x)
include J
/-- Actual refined answer in terms of the focused vector. -/
lemma pair_column (e:roofed P s n F) {b:ℝ}{v:Lead.Clan} (p':Portfolio x s n b v) (F':SampleDose)
    (c':ShopP P s n→₀ℝ) (g:roofed P s n F'):
    Tendsto (fun t=> P.singleState 3 t x (P.reflectTest 3 (deploy t F p c) * deploy t F' p' c')) atTop
      (𝓝 (inner ℂ (column p F (focusing S false c (alk s n x Z false)))
        (column p' F' (focusing S false c' (alk s n x v false))))) := by
  let K:=P.enter 3 ξ; let x':= paid p c F; let y:= paid p' c' F'; let G(t):= inner ℂ (docket t p c F) (docket t p' c' F')
  have hp:Tendsto G atTop (𝓝 (inner ℂ (K x') (K y))):= (till_paid p c F J).inner (till_paid p' c' F' J)
  have hz:= (K.inner_map_map x' y).trans (congrArg₂ (inner ℂ) (column_price p F c e) (column_price p' F' c' g))
  exact ((Eq.mp (congrArg (fun z:ℂ=> Tendsto G atTop (𝓝 z)) hz) hp)).congr' (((coverable c).and (coverable c')).mono (fun t u=>(onPair t p c F e u.1 p' c' F' g u.2).symm))
omit J
end
#print axioms pair_column
end Thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
