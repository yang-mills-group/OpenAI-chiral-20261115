import YM.CF.Py.Wall
import YM.CF.Py.Balance
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U} {M C:Side}
variable (q:Chi)(J:Robes M V W)(γ w h:ℝ)
variable (i0 v':ℕ)
-- epoch stage invoice x artifacts; output F has sizeK.R.L. aperture h≥min both.Every scales.
-- transit law independent of Station.clock binder. prove at all Scope with h.Set. need align species α_j
structure BillStep (f g F' G':ℝ→ℝ)(x h:ℝ)(p i M₀:ℕ):Prop where
 ride : ∀{N P:Side}{S:StepData (Domain N B) (Domain P B)}(T:Tube SU.group S){G:Ratio (mid N B) (mid P B)}(A:Scree.Loom (mid N B))(E:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B)){a γ:ℝ}, StatV V G T U W X Y a γ w x p i → M₀*radiusB x ≤ (Domain N B).val → RocketV V N P U W J A G q → Roof _ J.k J.roomX J.n E→ LotR Y h (f (x+billX R.L)) (g (x+billX R.L)) →StepR V X Y U A E G S q J.d h (F' x) (G' x)
lemma folio {f g:ℝ→ℝ}(hf:sizeK R.L 1 f)(hg:sizeK R.L 1 g)(𝒯:Warm V U W n J.n k m q J.k J.d J.roomX w h): ∃ F' G':ℝ→ℝ,sizeK R.L 1 F'∧ sizeK R.L 1 G'∧∀ᶠ x in atTop,BillStep V q J w f g F' G' x h m k n:=by
 obtain ⟨F₀,G,x1,x2,X⟩:= 𝒯.stage (shiftC f (billX R.L)) (shiftC g (billX R.L)) (sweepK _ _ (Vale.pitch _) f hf) (sweepK _ _ (Vale.pitch _) g hg)
 refine ⟨F₀,G,x1,x2,X.mono ?_⟩; intro z v; refine ⟨fun {N P S} T {G} A E X Y {a γ} b w r g t=>?_⟩
 have h:Girt.Ward Y:= ward_m (show Y.path.Bounds Y.funds _ _ _ from by rw [b.coinY,b.move]; exact b.hunt.up) t -- tune p param
 obtain ⟨D⟩:= rig V U W J q r E g Y b.sound b.hunt.bill h
 exact v _ _ T A E X Y r.paid g r.pose D b w t
variable (M₀ k₀:ℕ)
structure Valley(G:Warm V U W M₀ J.n k k₀ q J.k J.d J.roomX w h)(v:ℕ)(f g:ℕ→ℝ→ℝ):Prop where
 size :∀ i,i≤v→sizeK R.L 1 (f i)∧ sizeK R.L 1 (g i)
 top:f v=0
 knot:g v=0
 use:∀ᶠ x in atTop,∀ i,i<v→ BillStep V q J w (f (i+1)) (g (i+1)) (f i) (g i) (hat R.L x i) h k₀ k M₀
-- right-to-left.fill for all i.Bound.Vol Π color unified
variable (D:Warm V U W M₀ J.n k k₀ q J.k J.d J.roomX w h)(Bδ:ℕ)
include D
private lemma economy(m:ℕ)(g:m≤ Bδ): ∃ f g:ℕ→ℝ→ℝ,(∀ i,i≤ Bδ→sizeK R.L 1 (f i)∧ sizeK R.L 1 (g i))∧ f Bδ=0 ∧ g Bδ=0 ∧∀ᶠ x in atTop,∀ i,i<Bδ→ Bδ ≤ i+m→ BillStep V q J w (f (i+1)) (g (i+1)) (f i) (g i) (hat R.L x i) h k₀ k M₀:=by
 induction m with
 | zero=>
    have he:sizeK R.L 1 0:= by change sizeK _ _ (fun _=>0); simpa only [zero_mul] using (sizeK.main R.L).scale 0
    exact ⟨0,0,fun i _=>⟨he,he⟩,rfl,rfl,Eventually.of_forall fun i j v t=>by omega⟩
 | succ m ih=>
    let i:=Bδ-(m+1); have hi:i < Bδ ∧ i+(m+1)=Bδ:=⟨by omega,by omega⟩
    obtain ⟨f,y,l,p',u,h'⟩:= ih (by omega); obtain ⟨x1,x2⟩:= l (i+1) (by omega)
    obtain ⟨F,G,x3,x4,t⟩:= folio V q J w h x1 x2 D -- order h
    refine ⟨Function.update f i F,Function.update y i G,fun j t=>?_,by simpa [Function.update_of_ne (show Bδ≠i by omega)] using p',by simpa [Function.update_of_ne (show Bδ≠i by omega)] using u,?_⟩
    · by_cases e:j=i; subst j; rw [Function.update_self,Function.update_self]; exact ⟨x3,x4⟩
      rw [Function.update_of_ne e,Function.update_of_ne e]; exact l j t
    have hx: Tendsto (fun x=> hat R.L x i) atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_id
    filter_upwards [hx.eventually t,h'] with x p q j t u; by_cases z:j=i; subst j; simp only [Function.update_self, Function.update_of_ne (show i+1≠i by omega)]; exact p
    have hK:j+1 ≠ i:=(by omega); simp only [Function.update_of_ne hK,Function.update_of_ne z]; exact q j t (by omega)
lemma niceV : ∃ f g:ℕ→ℝ→ℝ, Valley V q J w h M₀ k₀ D Bδ f g:=by
 obtain ⟨a,b,c,e,f,t⟩:= economy V q J w h M₀ k₀ D Bδ Bδ le_rfl; exact ⟨a,b,c,e,f,t.mono fun i p j v=>p j v (by omega)⟩
end YM.CF.Py
