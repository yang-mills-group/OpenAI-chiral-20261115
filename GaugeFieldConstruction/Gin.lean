import GaugeFieldConstruction.Gong
import GaugeFieldConstruction.Gander
import YM.CF.Prism.Pang
import YM.CF.Feu.Rill
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 95000
noncomputable section
namespace YM.CF.TableF.Axon
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Next.Foundations Taxi
local notation "GS"=> SU.group
open MultiNext.SignedSource PhysicalNext.JointLoad Analysis Siete Banjo
variable {n d:Side}{P E: BudgetPoint}{o: Skye.Seat d}{D:Set (tangD d)}{X:Scree.Hub n}{x:tangD n}{Y:tangD d→ tangD n}{u r s b a K:ℝ}
open Haro
lemma LocalBuild (u:Proofs P X.val.2 X.val.1 Y 0 (fun v=> v∈ D) 6 s b) (v:∀ i ≤ 6,∀ Z:Fin i→ tangD d,(∀ j, Z j ∈ D)→ StrongE P X K b (iteratedFDeriv ℝ i Y 0 Z)): LocalCurve P X Y D K b :=by
 refine ⟨u.flow,⟨u.mark,u.sails⟩,?_,fun i h Z t=> (StrongE.tap (v i h Z t))⟩
 have hh:= StrongE.tap (v 0 (by omega) Fin.elim0 (fun i=> Fin.elim0 i)); simpa using hh
abbrev prey (s:ℝ):ℝ:= DevelopCost*xHoch 6*(4*s)^6
lemma prey_r (v:0 ≤ s):0≤ prey s:=by have ht:0≤ DevelopCost:= Finset.sum_nonneg (fun i _=>by positivity); have wp:0 ≤ xHoch 6:=zero_le_one.trans (multip 6).choose_spec.1; unfold prey; positivity
lemma focusS (z:X=X)(hv:LocalCurve P X Y {i | E.dirBound o i} s b) (t:1 ≤ s)(p:0 ≤ b)(w:b≤1) (k:E.order=6) (F:Pane n→ℂ)(h:X=X)(u:∀ x y,Agrees X.val.2 x y → F x= F y)(c:ℝ)(hF:∀ U, pingS P.threshold X.val.2 U → Signs P X.val.1 (F∘ increment U) c): Signs E o (F∘ increment 1∘Y) (prey s*c):=by
 let x:=Y 0; have he:pingS P.threshold X.val.2 (increment 1 x):=by simpa using hv.home.2 1 (by simp)
 have hb: ContDiffAt ℝ (6:ℕ∞ω) (F∘ increment 1) x:= (stirring (1:Pane n) (Y 0) u c (hF _ he)).of_le (Nat.cast_le.mpr P.order_ge)
 have hp:0≤ c:= (hF _ he).grade; let Q:= xHoch 6*(4*s)^6*c; have hh:0≤ Q:= mul_nonneg (mul_nonneg (zero_le_one.trans (multip 6).choose_spec.1) (by positivity)) hp
 refine ⟨mul_nonneg (prey_r (zero_le_one.trans t)) hp, by rw [k]; exact hb.comp 0 hv.smooth,fun m l y e=>?_⟩; rw [k] at l
 change ‖iteratedFDeriv ℝ m ((F∘increment 1)∘ Y) 0 y‖≤ _
 apply (advances 6 _ _ _ hb hv.smooth (h:=Footmark P X s b) (C:=Q) ?_ (E.dirBound o) (fun i _ p v ht=> hv.releases _ p _ ht) m l y e).trans
 · unfold prey; exact (mul_le_mul_of_nonneg_right (show _≤DevelopCost from single_le_sum (f:=fun i=> (↑(Fintype.card (OrderedFinpartition i)):ℝ)) (fun _ _=>by positivity) (mem_range.mpr (show m<7 from by omega))) hh).trans_eq (by unfold Q; ring)
 intro m t' v g; refine ((multip 6).choose_spec.2 n X.val.2 1 P X.val.1 x F u c (hF _ he) hv.home.1 m t' (t'.trans P.order_ge) v (fun _=>4*s*b) (fun i=>payφ _ p w t (g i))).trans ?_
 rw [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (by linarith) w) m).trans (pow_le_pow_right₀ (by linarith) t')) (zero_le_one.trans (multip 6).choose_spec.1)) hp
lemma slot_credit {F:InkD n} (u:LocalCurve P X Y {i | E.dirBound o i} s b) (w:F=F) (g:Finset (Dwell n)→ℝ)(r1:PressB P X F r K)(h:∀ U,BedP P U F X g)(hz:∀ i,0≤ g i)(t:1 ≤ s)(p:0 ≤ b)(w₁:b≤1)(k:E.order=6)(i j:Prism.Rock n)(l m:SU.Slot): Signs E o (fun x=> CharM F i j (increment 1 (Y x)) l m) (prey s*Prism.crack g i j):=
 focusS (Eq.refl X) u t p w₁ k (Prism.crib F i j l m) rfl (fun _ _ p=> congrArg (fun x:Cipher n=>Prism.mileT i j true false x l m) (r1.term _ _ p)) _ (fun U v=>Prism.sent _ _ _ _ (h U) v hz _ _)
open Phase Jet Cube Nor Feu Extra.Iteration Extra.Iteration.Scales
variable {U:tangD d→ℂ}
open Pressure
lemma peseta (u:Signs E o U a) (x:ℝ)(K:Support (More d))(hp:E.threshold=temp x)(h:o∈K)(b:ℕ): Allows E.order (fun i=>U (temp x • lineP E o K b i)) 0 a:=by
 obtain ⟨I,h,e⟩:= peg_z E o K b h hp; simp_rw [e]; let F':= U ∘ Prism.trunk E o; have hx:Allows E.order F' 0 a:= Prism.skin u
 change Allows E.order (F'∘ I) 0 a; refine ⟨(show ContDiffAt ℝ (E.order:ℕ∞ω) F' (I 0) from I.map_zero.symm ▸ hx.smooth).comp 0 I.contDiff.contDiffAt,fun j p=>?_⟩
 rw [Next.Foundations.jets_linear I (hx.smooth.of_le (Nat.cast_le.mpr p))]; exact ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (by simp only [prod_const,card_univ,Fintype.card_fin]; exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h)).trans (hx.norm_le j p)))
end YM.CF.TableF.Axon
end
