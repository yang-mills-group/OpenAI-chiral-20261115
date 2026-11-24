import Knotwise.Kale
import Knotwise.Gesture
import WinterX.Camera
import Compass.Pavilion
import Knotwise.Gesture
import WinterX.Instrument
import WinterX.Pantry
import YM.CF.Fans.Cause
import Thin.CapsEarn
import YM.CF.Fans.Elm

/- Adapted from YM/CF/Fans/Elm.lean for the NoSlip, capped ScaledV use below. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
variable {d e η t z gg A B':ℝ} {j k k' m n l:ℕ}
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
open Trees Footprint Iva Eire
open Jade
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open Neon Mew Vow Tap Rive Bake Larch Salt Ione Sour Moto
open scoped Mew
open Both
-- Feynman transfer interface. γΓ is κPass. Key submission at fine Y $f/g/r. inputs.Xo offset. exact stage backend same for all. capacities flexible via callers. Expose Stage$ device per submission as existential with commitments obeying simultaneous comparison through same equivalence; can `Classical.choose` based solely on inputs, no future Pledge.
variable {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q:Chi}
local notation "Nk"=> mid N B
local notation "Pk"=> mid P B
variable (Wξ:Op SU.Slot)(v1 kF Wκ Δ_ f0 g0 g1 g2 Q₁ Q₂ Q₃ cΦ Zμ:ℝ)
variable (price_R:ℝ→ℝ)(θc:ℝ)(gK:ℕ)
variable {J:Type}[LinearOrder J][Fintype J]{h Kv Zv:ℝ}(ζP:J→Site (mid N B))(E' S':Key J → RegBudget (mid P B))(Yf:Key J→ ForceBudget (mid P B))(A_:J→ ArcΦ)(Dϕ:J→ℝ)
local notation "σ_p" => (Cube.node ∘ Hove.heel G ∘ ζP)
-- returns oracle.Binder ABI. Fintype & LOrder for LabelΩ need avoid instance paths.
open Compass Both
variable {Wξ v1 kF Wκ Δ_ f0 g0 g1 g2 Q₁ Q₂ Q₃ cΦ Zμ gK θc}
variable {AΦ:Cusp (mid N B)→ Cusp (mid N B)}{Kc:Cusp (mid N B)}{γt:ℝ}
open Lattice.PlaqAxes AnalyticBridge.VerifiedReset
variable {Clock:∀ (J:Type)[LinearOrder J][Fintype J],(J→Site (mid N B))→capture J (mid P B)→capture J (mid P B)→attach J (mid P B)→(J→ArcΦ)→(J→ℝ)→Key J→Cusp (mid N B)}
variable {hh:ℝ}
variable (Bq: Hourly V U X Y S G G₀ G₁ Wξ q kL hh v1 kF Wκ Δ_ f0 g0 g1 g2 Zμ Q₁ Q₂ Q₃ cΦ θc gK AΦ Kc γt Clock)(he:1≤hh)
variable {I I':Type}[LinearOrder I][Fintype I][LinearOrder I'][Fintype I'](σ:I→Site (mid N B))(E Eo:capture I (mid P B))(Y₀:attach I (mid P B))(F:I→ArcΦ)(U₁:I→ℝ)(qt:MissionH Y hh R.L G σ E Eo Y₀ F U₁ Q₁ Q₂ Q₃ cΦ)
    (σ':I'→Site (mid N B))(M Mo:capture I' (mid P B))(F':attach I' (mid P B))(Z':I'→ArcΦ)(W₀:I'→ℝ)(t':MissionH Y hh R.L G σ' M Mo F' Z' W₀ Q₁ Q₂ Q₃ cΦ)
open Classical
-- Key singleton perturbation marker. relation same kind on signs.$B_clock.

variable (y:staff (mid N B))(j:I)(j':I')
local notation "F₁"=> Clock I σ E Eo Y₀ F U₁
local notation "F₂"=> Clock I' σ' M Mo F' Z' W₀
local notation "nX"=> mid N B
local notation "zA" r:max=>singletonK j r
local notation "zB" r:max=> singletonK j' r
local notation "a"=> taxK y -- collides variable a ℝ non-$use
variable (hs : ∀ u:ℝ, ‖u‖≤1 →
    sees (reSweep (G:Ratio (mid N B) (mid P B)) (↑y)) E Eo Y₀ (singletonK j u) M Mo F' (singletonK j' (taxK y*u))) -- notation args may inaccessible. sees only P B implicit problem.
-- scalar axis input relation, may weaken to germ. comparison of Cusp.Phase etc then Cold.E
variable {N_:Side} (s:staff N_)
abbrev TipLinear(v:Sweep N_): Cipher N_→L[ℝ]Cipher N_:=(suit_Y v).toLinearMap.toContinuousLinearMap
-- using linear holomorphic restriction for ℝ price.Complex modules port. Local Classical Finset $j
local notation "Yκ"=> reSweep G (↑y)
local notation "uL"=> (Yκ).charge
private lemma freeze_tip (v:staff N_)(Q:Key I→ Cipher N_)(Q':Key I'→ Cipher N_)(hL: River Q)(hR:River Q')(p:∀ u:ℝ, ‖u‖≤1→ Q' (singletonK j' (taxK v*u))= suit_Y v.val (Q (zA u))) : tipI Q' [j']= taxK v • suit_Y v.val (tipI Q [j]):= by
 have he:=Compass.turnG Q hL j Q' hR j' (TipLinear v.val) _ (prop1 v).2 p; exact he
include V Bq qt t' he hs
local notation "R1"=> restoring X.p AΦ (F₁)
local notation "R2"=> restoring X.p AΦ (F₂)
lemma tilt_o (W:Orbit nX)(b:Aura nX):
 Mew.tipI (fun z:Key I'=> (R2 z) (moldA (↑y) b) (yellA (↑y) W)) [j']= a • suit_Y (↑y) (tipI (fun z:Key I=>R1 z b W) [j]):=by
 have ht1:= Bq.hand I σ E Eo Y₀ F U₁ qt; have ht2:=Bq.hand I' σ' M Mo F' Z' W₀ t'
 unfold Soloing at ht1 ht2; refine freeze_tip j j' y _ _ (ht1.2.1 _ _) (ht2.2.1 _ _) (fun u hx=>?_)
 exact (costKin V Bq he σ E Eo Y₀ F U₁ qt σ' M Mo F' Z' W₀ t' y j j' hs u hx Kc Kc (fun z e=>Bq.zeal _ z e)).1 W b
-- wrapped.Cold.P constraints
lemma freezeA: pecs y (icedCusp X.p AΦ (F₂) j')= a • icedCusp X.p AΦ (F₁) j:=by
 funext T; change suit_Y ((↑y:Sweep _)⁻¹) (coldE X.p (τι (R2) [j']) (yellA (↑y) T))= a • coldE X.p (τι (R1) [j]) T
 
 rw [show coldE X.p (τι (R2) [j']) (yellA (y: Sweep nX) T)= a • suit_Y (↑y) (coldE X.p (τι (R1) [j]) T) from ?_, map_smul,moon_Y,mul_inv_cancel,toon_Q]
 unfold coldE; rw [map_sum, Finset.smul_sum]; symm; refine Finset.sum_equiv (moldA (↑y)) (fun i=> by simp only [mem_filter,mem_univ,true_and]; exact (glowA ..).symm) ?_; intro i _ ; exact (tilt_o V Bq he σ E Eo Y₀ F U₁ qt σ' M Mo F' Z' W₀ t' y j j' hs T i).symm
-- ∅ K source version. need PotZ at Kc+stack by Kc.zeal. taxK y with cuspan.
lemma θZero : PotZ (↑y) Kc Kc:= fun T p=> Bq.zeal _ _ p
omit V Bq qt t' he hs
lemma stack_T {Q:I→Cusp nX}(u:ℝ): Φstack Q (zA u) = u • Q j:=by
 unfold Φstack; rw [sum_eq_single j]; swap
 · intro b _ p; rw [singletonK, update_of_ne p,Pi.zero_apply,zero_smul]
 swap; · simp
 rw [singletonK, update_self, C_amount]
variable (K1:I→Cusp (mid N B))(K2:I'→ Cusp (mid N B))
lemma stackSeal (u:ℝ)(p:cuspan y (K2 j')= a • K1 j): PotZ y.val (Φstack K1 (zA u)) (Φstack K2 (zB (a*u))):=by
 rw [stack_T j u, stack_T j' (a*u)]
 intro T pv l D d v
 have hf:= congrFun (congrFun (congrFun p l) D) T; change suit_Y ((↑y:Sweep nX)⁻¹) (K2 j' (moldA y.val l) (actY y.val D) (yellA y.val T))= a • K1 j l D T at hf
 apply (show Function.Injective (suit_Y ((↑y:Sweep nX)⁻¹)) from by intro x z e; have ht:=congrArg (fun T=>suit_Y (↑y) (T:Cipher nX)) e; rwa [moon_Y,moon_Y,inv_mul_cancel,toon_Q,toon_Q] at ht)
 change suit_Y ((↑y:Sweep nX)⁻¹) ((a*u) • _) = _
 rw [map_smul,hf,moon_Y,mul_inv_cancel,toon_Q,smul_smul,mul_right_comm,(prop1 y).2,one_mul]; rfl
include V Bq qt he t' hs
lemma freezeForce (p:cuspan y (K2 j')= a • K1 j)(ux:∀ z:Force nX,∀ v:Orbit nX,River fun i:Key I=> restoreF X.p AΦ Kc (F₁) K1 i z v)(uh:∀ z:Force nX,∀ v:Orbit nX,River fun k:Key I'=>restoreF X.p AΦ Kc (F₂) K2 k z v):
   ForceR y.val (fun z v=> tipI (fun i=>restoreF X.p AΦ Kc (F₁) K1 i z v) [j]) (fun z v=>a • tipI (fun i=>restoreF X.p AΦ Kc (F₂) K2 i z v) [j']):=by
 intro T v z; change a • _=_
 rw [show tipI _ [j']=_ from freeze_tip j j' y _ _ (ux z T) (uh _ (yellA (↑y) T)) ?_,smul_smul,(prop1 y).2,one_smul]
 intro x g
 exact (costKin V Bq he σ E Eo Y₀ F U₁ qt σ' M Mo F' Z' W₀ t' y j j' hs x g (Kc+Φstack K1 (zA x)) (Kc+Φstack K2 (zB (a*x))) (fun T v i D d t=> (congrArg₂ (·+·) (Bq.zeal _ T v i D d t) (stackSeal y j j' K1 K2 x p T v i D d t)).trans (map_add ..).symm)).2 T v z
#check tilt_o
#check costKin
end YM.CF.Py
end
