import Anomaly.Weigh
import Anomaly.Sell
import YM.SU5.FiniteGaugeData.Tapestry.Junction
import YM.SU5.Interaction.Source
/-!
Unconditional on our appointed Vantages (cpX here). A real tilted-root
reading at this one K/data set. Uses actual denominator & flags, proves
the Q*t^(-2) nudge can use (129)'s multiplier in the single-root linear
currency. (Higher pin approximation not stated here.)
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
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
open YM.CF.BPress (PL NPL)
variable {F G:ℝ→ℝ}
open Vow Sour Swell Ione
namespace Rate
namespace LocalLimit
open Jet
namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
open Buffered Afterglow Tapestry Vow.TreasuryFog
variable {P:Preparation}{t:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus t))
local notation "Θ" s:max=> (hat P.R.L P.x s)
local notation "κA" i:max s:max=> ((Y.voyage i).CapeT s)
local notation "bm" i:max k:max s:max=> RootBook Y i k s
local notation "Ω" i:max s:max=> P.Ctor (Y.ir i) s

variable {i k s m:ℕ}(o:Site (P.Ctor (Y.ir i) s))
variable {a b f d:ℝ}{J T : Axis→SOp (P.Ctor (Y.ir i) s)}{X Z : SOp (P.Ctor (Y.ir i) s)}
variable (C: CartPins Y i k s m a b f d J T X Z)

def purchaseY (F : SOp (P.Ctor (Y.ir i) s))(D : Axis→ SOp (P.Ctor (Y.ir i) s)) (k m:ℕ) : Mark (Ω i s):=
    ((pinpr P.R.L (Θ s)/(temp (Θ s))^2: ℝ):ℂ) •
      jointMark (bm i k s).p (κA i s) o m (co_Ψ o 0 F) (fun j=> co_Ψ o 0 (D j))

def tested (F : SOp (P.Ctor (Y.ir i) s))(D : Axis→ SOp (P.Ctor (Y.ir i) s)) (k m:ℕ) : Mark (Ω i s) :=
    (stemS (Θ s):ℂ) • (purchaseY Y o F D k m)

lemma tested_eq (X : SOp (P.Ctor (Y.ir i) s))(J : Axis→ SOp (P.Ctor (Y.ir i) s)) (k m:ℕ) :
    tested Y o X J k m= (hueW P.R.L (Θ s):ℂ) • jointMark (bm i k s).p (κA i s) o m (co_Ψ o 0 X) (fun j=> co_Ψ o 0 (J j)):= by
  rw [tested,purchaseY,smul_smul,mul_comm]; simp only [hueW,Complex.ofReal_mul]

def chargeY {A B:Side}{j:ℕ}{L:Side}{ho:Odd L.val}{Y :Pricing j L ho (Thread j)} {e:ℝ}
    (U:Grasp Y B e)(R:GramM (mid A B))(K:Scree.Loom (mid A B))(F:Sour.Bag (mid A B))
    (H:∀ x:Orbit (mid A B),IsStarProjection (spar j R.J.M (K x)))(x:Orbit (mid A B)) : ℂ:=
  beamZ _ (pilotH U R K x (H x) (acts (∑ i:Vow.Aura _, F i x) (acts (fueled R.p R.K x).val (vacuum (Dwell _)))))

lemma basePilot {A B:Side}{j:ℕ}{L:Side}{ho:Odd L.val}{Y :Pricing j L ho (Thread j)} {e:ℝ}
    (U:Grasp Y B e)(R:GramM (mid A B))(K:Scree.Loom (mid A B))
    (x:Orbit (mid A B))(H:IsStarProjection (spar j R.J.M (K x))) :
    pilotH U R K x H (acts (fueled R.p R.K x).val (vacuum (Dwell _)))=denZ R U K x:=by
  have he:=showUp (R:=R) U K x H 0 R.K; rw [show exponentL (n:=mid A B) R.p 0 x.1=0 from (by simp [exponentL,numbE]),exp_zero,one_mul,add_zero] at he; exact he.symm

include C
lemma CartPins.window :
    let W:=tested Y o X J k m
    let R:=bm i k s
    let J':=fun j:Axis=>co_Ψ o 0 (J j)
    let V:=((hueW P.R.L (Θ s):ℂ) • puffLine (κA i s) R.p o J' (co_Ψ o 0 X) m)
    let S:= R.p.B+12+2*m
    WindowTag W o S (‖(hueW P.R.L (Θ s):ℂ)‖ * framePay (Tenant.quota^2*b)) ∧
    Contact (κA i s) (offsetMask S o) W V:= by
  intro W R J' V S
  have ht:= C.ropes.tubes; let Q:=ht.transfers C.staffing P.dpos o
  have hz:=C.pulse; unfold W; rw [tested_eq]; exact ⟨(jointWindow o hz.roof P.dpos Q.capX hz.reach C.capR hz.hint.le Q.hatJ m).scale _,(jointContact o hz.roof P.dpos hz.reach C.capR hz.hint.le Q.capX Q.hatJ C.curtain).scale _⟩

lemma CartPins.linked (x:Fields (Ω i s)) :
    let Q:= hueW P.R.L (Θ s)
    let t:= translatedFields (o-0) x
    twist (quantU (γS (taxiPlus (o-0)))) ((tested Y o X J k m) x) = (↑Q:ℂ) • (jointMark (bm i k s).p (κA i s) 0 m X J t) := by
  intro _ _; rw [tested_eq,Pi.smul_apply,twist_scalar]
  let T:= C.ropes.tubes; let V:=T.transfers C.staffing P.dpos o
  let h:=C.pulse
  exact congrArg ((hueW P.R.L (Θ s):ℂ) • ·) (joint_taxi 0 o h.roof P.dpos T.capX V.capX h.reach C.capR (fun _=>rfl) T.hatJ V.hatJ (fun _ _=>rfl) m x)

-- single-root opening incl normalizing denominator. planting key rank not certified yet.
theorem CartPins.firstPrice (h:(Y.voyage i).kick≤k)(v:s<Y.uv k) :
    let J':=fun j:Axis=>co_Ψ o 0 (J j); let X':=co_Ψ o 0 X
    let R:=bm i k s; let b:=R.p; let q:=Rill.cipherK P.J.n; let K:=κA i s
    let D:=partitionZ R P.U K
    let H:=fun x:Orbit (P.Ctor (Y.ir i) s)=> (projects_here Y i k s x).1
    let W:=tested Y o X J k m; let Y':=((hueW P.R.L (Θ s):ℂ) • puffLine K b o J' X' m)
    D ≠ 0 ∧ ∃ F:Sour.Bag (Ω i s),
     Nest P.U R K P.J.n 24 (node o) P.h (rScale b) Y' F f (d*pinpr P.R.L (Θ s)) ∧
      Integrable (chargeY P.U R K F H) (city _) ∧
      (∀ x:Orbit (Ω i s), letterRead (W (x.1,K x)) (denZ R P.U K x) = chargeY P.U R K F H x) ∧
      Journey.compass Y i k s W=(∫ x, chargeY P.U R K F H x ∂city _)/D ∧
       ∃ A B:Vow.Aura (P.Ctor (Y.ir i) s)→ℝ, voyageB A b.B (rScale b) ≤ f ∧ voyageB B b.B (rScale b) ≤ d*pinpr P.R.L (Θ s)∧
         (∀ X:Vow.Aura (P.Ctor (Y.ir i) s),¬grooveB 24 b (node o)⊆X.val → A X=0∧ B X=0) ∧
          ∃ m:∀ X,Title b P.h q (F X) X (A X), (∀ X,BirthRight b P.h (F X) X (B X)) ∧ Stax.WickL b P.h q (Title.powerQ F A m).payX A B (fun i Y=>F Y i) (grooveB 24 b (node o)) := by
  intro J' X' R b q K D H W Y'
  obtain ⟨F,hK⟩:= C.for_all o
  let t:= CartPins.window Y o C
  have he(x:Orbit (Ω i s)) : letterRead (W (x.1,K x)) (denZ R P.U K x) = chargeY P.U R K F H x := by
    unfold chargeY
    rw [hK.science x (H x),basePilot _ R K x _]
    exact t.2.money x _
  obtain ⟨sQ,u,v⟩:= Tapestry.funds Y s i k (f:=W) t.1.ticket.env h v.le
  have he₁ : (fun x:Orbit (Ω i s)=> inner ℂ (mateK _) (acts (W (x.1,K x)) (denZ R P.U K x)))=chargeY P.U R K F H:=funext he
  refine ⟨u,F,hK,he₁ ▸ sQ,he,v.trans ?_,hK.pouch.currency C.pulse.most (zero_le_one.trans P.height)⟩
  exact congrArg (fun f:Orbit (Ω i s)→ℂ=> (∫ x:Orbit (Ω i s),f x∂city _)/D) he₁
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
