import YM.SU5.FiniteGaugeData.Tapestry.Motif
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)
/-!
# All-History mixed polynomial transport. Locality and cost.

At the upper observing level of an actual FINITE history, the tested mixed polynomial
reads a single supported Ward test obtained by ascent. Without period limit step.
Supports in shield of the Cover certify all participating levels/horizons. For
norm estimates `Piece` projected into support Swatch requires a qualified area.
We first prove support on *all* true paid periods even without that qualification.
Cost bounds in following modules.
-/
set_option quotPrecheck false
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (i k n:ℕ)(S:BillOfWork)(x:Employee S)
local notation "σ" n:max=> side Y i n
local notation "K"=> tent Y H
local notation "F" i:max=> frameBudget S Λ l i
local notation "U" i:max=> Swatch (frameBudget S Λ l i)
local notation "Sx"=> employ (tent Y H) S x
lemma wearSupport (q:Pay Y n i k) : AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire ((tidalDressing Y H i k).finish n (employ K S x))):=by
  induction n with
  | zero=> exact presented Y H 0 i (S 0) _
  | succ t ih=>
    let a:= (tidalDressing Y H i k).finish t (Sx)
    have e:= ascendSupport Y t i k (F t) q (ih ⟨q.1,Nat.le_of_lt q.2⟩)
    change AtSupport false _ (attire (music Y t i k a * roving Y H (t+1) i (Sx (t+1))))
    rw [attire_mul,music,flowing];
    have ht: AtSupport false (region (F (t+1)) (σ (t+1))) (ascender Y t i k (attire a)):= e.mono (image_subset_image subset_union_left)
    have he:= (presented Y H (t+1) i (S (t+1)) (x (t+1))).mono (show region (S (t+1)) (σ (t+1)) ⊆ region (F (t+1)) (σ (t+1)) from image_subset_image subset_union_right)
    exact ht.mulM he
lemma wearH (q:Pay Y n i k)(p:Clocked («K»:=tent Y H) S n x): AtSupport false (region (frameBudget S Λ l n) (side Y i n)) (attire (breathing Y H n i k (motif K S x))):=by unfold motif; rw [breathing_pure _ _ _ _ _ _ p]; exact wearSupport Y H i k n S x q
noncomputable def palp : QuiltLinks S Λ l:= fun j => (extendLeft K S j Λ l).comp (coupon Y H (frameBudget S Λ l j) j i k) -- extends Swatch to the frame
noncomputable def motionPay {B:Clay Λ l}: QuiltLinks S Λ l:= fun j=> (extendLeft K S j Λ l).comp (B (frameBudget S Λ l j) j)
noncomputable abbrev costumeAt := Tapestry.powers K S Λ l (palp Y H i k S) n x
noncomputable abbrev outfitView (B:Clay Λ l) := Tapestry.powers K S Λ l (motionPay Y H S (B:=B)) n x
section
variable (p:∀ j:ℕ,j<n → Spanned Y (frameBudget S Λ l j) j i k)
include p
lemma comparedOutfit : (tidalDressing Y H i k).finish n (employ K S x) = wearStep Y H (frameBudget S Λ l n) n i (costumeAt Y H i k n S x):=by
 induction n with
 | zero=>exact attireL_inj rfl
 | succ t ih=>
   let V:Swatch (F t):= costumeAt Y H i k t S x; let V':= coupon Y H (F t) t i k V; let u:=tidalDressing Y H i k
   have w : V' = V' := rfl -- notation V conflict?
   have h: u.finish t (Sx)= wearStep Y H (F t) t i V:=ih fun i v=> p i (by omega)
   rw [Decking.finish,h]; -- RHS uses fill
   change music Y t i k (wearStep Y H (F t) t i V)* roving Y H (t+1) i (badge K (S (t+1)) (x _))= _
   let B':= followBox (Λ:=Λ) (l:=l) (frameBudget S Λ l t)
   rw [← ContinuousLinearMap.comp_apply,← compatibility_boutique Y H (F t) t i k (p _ (by omega)),ContinuousLinearMap.comp_apply,rovingBadge]
   -- now equality on Ward via `present`
   apply attireL_inj; rw [attire_mul,attire_wear,attire_wear,attire_wear]; unfold costumeAt; rw [powers_succ,material_eq]; unfold palp extendRight extendLeft; rw [present_brocade, ContinuousLinearMap.comp_apply,present_broad,present_broad]; rfl -- tune
omit p
namespace Exhibition
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
lemma comparedVista : (D.vistaDressing Y H).finish n (employ K S x) = badge K (frameBudget S Λ l n) (outfitView Y H n S x B):=by
 induction n with
 | zero=> exact Eq.symm (began K S Λ l x)
 | succ n ih=>
   rw [Decking.finish,ih]; change (liftD Y H n D _)*badge K (S (n+1)) (x (n+1))= _; rw [fromLocal]; unfold outfitView; rw [powers_succ,material_eq, badge_brocade]; simp_rw [extendRight,motionPay,extendLeft,ContinuousLinearMap.comp_apply,widenBadge]
end Exhibition
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.comparedOutfit
#print axioms YM.CF.Buffered.Afterglow.Tapestry.wearSupport
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.comparedVista
