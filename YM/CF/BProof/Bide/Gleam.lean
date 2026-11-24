import YM.CF.BProof.Bide.Keep
import YM.CF.BProof.Temple.Summit
import YM.CF.BProof.Solar.Fit
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}
-- Bough spine geometry keeps Hue, lifts genuine fields. h rt fixed at hq; no size when comparing l0 theta step. Spans Estimate. Need access S.ρ uniforms.
open Bake PushA Episode Salt
variable {m:Side}{hx N0 n:ℕ}{T': Month x a order power N0 V W}
-- suffix scheduling.These at all n meeting.Buyer settlement.
open Chaff Gloss Maize Tye RP RP.Str
open Brace
-- auxiliary sunrise: Hoist input as existing. variant all n.
variable {F0:(m:Side)→Scroll m B (Brace.northZ m B)}
variable {J:Robes N V W}{η:ℝ}{b k Lm:ℕ} {A:FareFit R η}
open FareFit
namespace Patrol
variable (D:ForestDay V q h a order power N0 b Lm J F0 A T')
local notation "νγ"=>hat R.L x
local notation "Xκ"=> cell m B R.L
open Realm Realm.Shell Tide
variable {Z:Cape m B R.L}
variable (hp:flock Z J q)(hq:T'.q≤ m.val)(hM:61≤ m.val)
namespace Vista
variable (P: Vista D Z n)
open Realm Shell Journey
open Window.Unfit BProof Mint
variable {δ:∀ i:ℕ,Wheels (cell m B R.L i) Lm R}{j:ℕ}


include D hp
namespace Pitcher
variable (Aγ: Pitcher D P δ k)
include Aγ
local notation "Sκ"=> (P.P.astr j (Aγ.port j))
open BProof BProof.Bide
local notation "Δs" i:max=> (P.P.astr i (Aγ.port i))
local notation "G0"=>P.P.A j
open BProof BProof.Bide
variable (ωM:∀ i, Bide.Mask.Grants (δ i).val)(ψ:∀ i:ℕ,BProof.Vogue.Cream J.k J.n (Z i)){r:ℕ}(X:Bide.Half.ClockD R Lm J.n (Peaks.TripD.units R.L r))
namespace Estate
local notation "Yη" i:max=> (denZ (Δs i) U (Z i))
variable (i:Axis)(yR: Peaks.TripD.SetK K.j R.L r)
open Rue Bide.Gale Bide.Leg
include D hp P Aγ
variable {z₁ z₂ z₃:ℝ}(z: ScaleK z₁ z₂ (F0 (mesh m R.L n)))(u:Budget B d z₃)
local notation "Nτ" j:max=> (cell m B R.L j)
open scoped ComplexOrder
include X ωM ψ yR
open BProof.Bide.Half
lemma pe(b:Gale.Body (Nτ j))(g:Gale.Soul i X b)(w:j≤n) : ∃ P, Gale.Soul i (N:=Nτ n) X P∧ Gale.Soul.cup (Yη j) (Z j) (sqR i b)=Gale.Soul.cup (Yη n) (Z n) (sqR i P):=by
 let T (j:ℕ)(L:Gale.Body (Nτ j)):= Soul.cup (Yη j) (Z j) (sqR i L); have he(k i':ℕ)(f:Gale.Body (Nτ i'))(v:Soul i X f)(q:k+i'=n):∃ F,Soul i X F∧ T i' f=T n F:=by -- let naming T syntax
    induction k generalizing i' with
    |zero=>have hk:i'=n:=(Nat.zero_add _).symm.trans q; subst i'; exact ⟨_,v,rfl⟩ -- dependent
    |succ k ih=> obtain ⟨F,h,Z⟩:=stepW D hp P Aγ ωM ψ X i yR f v (by omega); obtain ⟨K,H,p⟩:= ih _ F h (by omega); exact ⟨_,H,Z.trans p⟩
 exact he (n-j) j b g (by omega)
omit ωM yR
include z u
attribute [local instance] Bide.Wager.measureVal Bide.Wager.billVal
private lemma beadX (b:Gale.Body (Nτ n))(p:Gale.Soul i X b):0 ≤Gale.Soul.cup (Yη n) (Z n) (sqR i b):=by
 obtain ⟨k,P'⟩:= ψ n; let Q:= P'.some; let B':=shield D hp n; let U':=Frost.heal (Z n) b
 exact (Soul.harvest i X B' Q p (hull D hp P Aγ (Nat.le_refl n)) (D.tint n (More _)) (fun V h T v t=> fresco D P Aγ V h v t T)).symm ▸ north D hp P Aγ i z u U' (Soul.avgSoulR i X B' Q p (upField ..) (Bide.Half.north i (Nτ n) _)) -- tune θ notation
include ωM yR
lemma topPos (w:j ≤ n)(T:Obs (Nτ j))(h:Allowed (shade (Nτ j) i true X.uF) T): 0 ≤ Fixed.numerator U (Δs j) (Z j) (Fixed.reflectTest i false T * T) :=by
 let S:=shade (Nτ j) i true X.uF; have hf: Disjoint S (regionD (Fixed.reflectSweep _ i) S):= by unfold S; rw [shade_carry]; exact splits i true (by have :=X.born; have :=X.pos; have :=X.duty; omega)
 obtain ⟨N,p,v,Z'⟩:=Leg.distill i h hf; let f:Gale.Body (Nτ j):= N ∘ Prod.fst; have hh:Soul i X f:=Soul.entry N p v; obtain ⟨G,g,e⟩:= pe D hp P Aγ ωM ψ X i yR f hh w
 have hZ:Fixed.numerator U (Δs j) (Z j) (Fixed.reflectTest i false T * T)=Soul.cup (Yη j) (Z j) (sqR i f):=by
    apply Eq.trans (Z' (Yη j)); unfold Fixed.functional Chalk.un; apply integral_congr_ae; apply Eventually.of_forall; intro u; dsimp only; rw [Pi.mul_apply,Chalk.mirror₀]; rfl -- expand kernel?
 rw [hZ,e]; exact beadX D hp P Aγ ψ X i z u G g -- param order
end Estate
end Pitcher
end Vista
end Patrol
end Cupboard
end YM.CF.Py
#print axioms YM.CF.Py.Cupboard.Patrol.Vista.Pitcher.Estate.topPos
