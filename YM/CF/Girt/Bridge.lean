import YM.CF.Girt.Quay
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{sN:ℕ}{d' w' a' b' c' V:ℝ}
structure BaseL (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ) where
 pearl : Pearl P
 wear : Stamped j L ho Y
 power : G.count=L
 pe : 0<e
 jpos : 1 ≤ j
 size : P.roundZ≤(mid M B).val
 wick : ∃ (s:ℕ)(a w d:ℝ), Tax L (ticketT (Thread j) true) false true a w s d ∧ s≤(mid M B).val ∧ e≤d
 lift : ∃ a b c d:ℝ,R.J.P.toll a b c d
 cap : ∃ b:ℝ, ∃ r t:ℕ,Roof _ b e r F₁∧Roof _ b e t F₂
 legal : 0<u ∧ 2*u<Next.SectorChange.firstRadius SU.group
 trial (F:Forest (ratio G)) (W: Pane (mid C B))(U:Orbit (mid M B)) : JointB G (seine G F q u W (F₁ U), F₁ U) e
 grant : Ward R
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
abbrev YF(F:Forest (ratio G))(X:Orbit (mid M B))(V:Orbit (mid C B)): Bkg (More (mid C B)) × Bkg (More (mid M B)) := (seine G F q u (F₂ V) (F₁ X),F₁ X)
def waveV(F:Forest (ratio G))(X:Orbit (mid M B))(V:Orbit (mid C B)): Phys (mid M B):= fire (Thread j) G R.J.M (unionP (YF G F₁ F₂ q u F X V)) (cartsL (switchG G).symm (denZ R P F₂ V))
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)
include X
lemma enter_p : RG.Envelope (denZ R P F₂):=by
 obtain ⟨b,v,w,p,l⟩:= X.cap; exact sailW _ X.grant X.pearl X.wear X.pe X.jpos _ F₂ l (P.clock_fine G X.size)
lemma entersL(F:Forest (ratio G)): RG.Envelope (uncurry (waveV P G R F₁ F₂ q u F)):=by
 obtain ⟨b,v,w,p,l⟩:= X.cap; obtain ⟨s,a,h,d,H,u',g⟩:= X.wick
 let L(Z: Orbit (mid M B) × Orbit (mid C B)):=YF G F₁ F₂ q u F Z.1 Z.2
 have hf:Measurable (fun i:Orbit (mid M B)×Orbit (mid C B)=>F₁ i.1) := p.bill.comp measurable_fst
 have he:Measurable L:= (((brake G q u F X.legal.1 X.legal.2).measurable.comp ((l.bill.comp measurable_snd).prodMk hf)).prodMk hf)
 let A(Z: Orbit (mid M B)× Orbit (mid C B)):= denZ R P F₂ Z.2; have ht : RG.Envelope A:= snap (enter_p X) measurable_snd; exact heat_k X.power _ H u' g X.pe X.size L A (fun z=>X.trial ..) he ht
lemma hut_k(F:Forest (ratio G))(V:Orbit (mid M B))(g: Seat (mid C B)→E)(H:∀ i:Seat (mid M B),g ((ratio G).embed i)=1)(U:Orbit (mid C B)): waveV P G R F₁ F₂ q u F V (gird g U) =waveV P G R F₁ F₂ q u F V U:=by
 obtain ⟨b,s,t,p,l⟩:= X.cap; obtain ⟨n,a,w,d,h,hp,L⟩:= X.wick; obtain ⟨_,_,_,_,T⟩:= X.lift
 let Q:= YF G F₁ F₂ q u F; have he: Q V (gird g U)=july G g (Q V U):=by
    unfold july; have hx:gauge (scaleG G g) (F₁ V)=F₁ V:=by funext; simp only [Lattice.gauge,scaleG,comp_apply]; simp [H]
    have hp:Odd G.count.val:= X.power ▸ ho
    refine Prod.ext ?_ hx.symm
    change seine _ _ _ _ (F₂ (gird g U)) _= _; rw [← brake_g G q u F hp (F₂ U) (F₁ V) g,hx]; exact congrArg (fun x=>seine G F q u x (F₁ V)) (l.rev _ _ _)
 have ht:denZ R P F₂ (gird g U)= effectK (tradew _ g).val (denZ R P F₂ U):= sweep R X.grant T F₂ t l U g X.pearl X.wear (P.clock_fine G X.size) X.jpos
 unfold waveV; unfold Q at he; rw [ht,he]
 exact score_m G R.J.M (Q V U) n h X.power hp (ambient _ _ X.pe L (X.trial ..)) g H _
end YM.CF.Girt
