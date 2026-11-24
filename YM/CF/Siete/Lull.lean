import YM.CF.Siete.Zoom
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Skye Scree Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n j l:ℕ}{K M' H C Q b v a ε r u R x t:ℝ}{c f:Side}{L:Side}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{P B:BudgetPoint}{X X':Support (More f)}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]
local notation "G"=>SU.group
section P
structure Mails (V:Pane c)(U:Pane c→Pane f)(o y:Seat c)(i: Bond (More f))(v: tangD c→SU.group.Color)(P:BudgetPoint)(n:ℕ)(C:ℝ):Prop where
 ch:ContDiffAt ℝ (n:ℕ∞ω) v 0
 pre: ∀ᶠ x in 𝓝 (0:tangD c), U (increment V x) i= SU.group.lieExp (v x)*(U V i)
 grade:v 0=0
 holds (j:ℕ)(h:j ≤ n)(p:Fin j → tangD c)(q:∀ i,P.dirBound y (p i)): ‖iteratedFDeriv ℝ j v 0 p‖ ≤ C
variable (M:Museum F x A X' Y I) (T:Tube G S) (V:Pane c)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(N:Pane f)(Z:LogArray G (Active A x F))(g:Seat c→SU.E)(e:Bond (More f))
local notation "o'" => S.ratio.parent e.1
local notation "s"=> loom P (Heir.reach x) b
local notation "Z'"=> hail M T V β k q d l N Z g e
local notation "uQ"=> reply T F x k g e
local notation "g_"=> atoms T M β k q d l N Z g ∘ increment V
abbrev fleece (n l:ℕ)(X:Support (More f))(B:BudgetPoint)(Q b:ℝ):ℝ:= Q*(b*2)+2*(1+(coverNumber B.B X:ℝ))^(B.power*n)
lemma pac (hQ:1 ≤ Q)(hb:1 ≤ b):1 ≤ fleece n j X B Q b:=le_trans (one_le_mul_of_one_le_of_one_le hQ (one_le_mul_of_one_le_of_one_le hb (by norm_num))) (le_add_of_nonneg_right (by positivity))
lemma ships {α:ℝ}{G':Teller G} (o:Seat f)(h:Mom.needed X' e)(ho:o∈X)(hb:e.1∈ inspected X)(J:Guide _ (P.dirBound o') 0 g_ n α)(p:Nut P V o' (Heir.reach x) n a b r g)(W: Folio.Bulletin x G' T)(hT:Act T F x k n t Q)(hv:Matins T F B.power u M')(hk:P.power=B.power)(hQ:1 ≤ Q)(hm:1 ≤ M')(hl:α ≤ s)(hu:s<t)(h₁:s≤1)(hj:P.threshold ≤2*B.threshold)(ht:P.threshold=temp x)(hyt:2 ≤ n)(hB:B.B ≤ 2*radiusB x)(hi:1000 ≤ radiusB x)(he:(M'*s^2+clinicFee n Q*s^2+α) ≤ 2*B.threshold/feeI x l (P.power*n)) : Mails V (recent T β k q d l N Z) o' (S.ratio.parent o) e (uQ ∘ Z') P n (fleece n l X B M' b * Lyre.width B o e):=by
 have h' : ContDiffAt ℝ (n:ℕ∞ω) (uQ ∘ Z') 0:=by
    have hx:= fires M T V β k q d l N Z g e J p hl; let H: tangD f →L[ℝ] SU.group.Color:= (SU.group.adjoint ((g o')⁻¹)).toContinuousLinearMap.comp (ContinuousLinearMap.proj e)
    change ContDiffAt ℝ _ (H ∘ (echo T F x k ∘ Z')) _; exact H.contDiff.contDiffAt.comp _ ((hT.calibrated.uniform _ (hx.size.trans hu.le)).smooth.comp (f:=Z') 0 hx.1)
 have hg: (uQ ∘ Z') 0=0:= reply_self ..; have hx:= fires M T V β k q d l N Z g e J p hl
 refine ⟨h',contacts M T V β k q d l N Z g e hT W h p.toCanvas hx.1.continuousAt (hx.size.trans_lt hu),hg,fun i v w z=> ?_⟩
 by_cases g':i=0; · subst i; rw [iteratedFDeriv_zero_apply,hg,norm_zero]; exact mul_nonneg (zero_le_one.trans (pac hm (p.hC.trans p.hQ))) (Lyre.width_pos ..).le
 let D:=(1+(coverNumber B.B X:ℝ))^(B.power*n); let z':=sphereQ V o' (Heir.reach x) g
 have hw := priceZ T V g e o ho hb hv p (Nat.pos_of_ne_zero g') v hk hj hm h₁ w z
 have hy:0<feeI x l (P.power*n):=by unfold feeI; positivity
 have hy':=B.threshold_pos; apply (loud M T V β k q d l N Z g e o ho hb (B:=B) J hT hQ p hl hu.le h₁ ht hyt (Nat.pos_of_ne_zero g') v w z).trans -- note hy shadow
 refine (add_le_add_left hw _).trans ?_
 unfold fleece; rw [add_mul (M'*(b*2)),add_assoc]; apply add_le_add_right; rw [←add_mul,←add_assoc];
 calc
   _ ≤ 2*B.threshold/feeI x l (P.power*n) * (feeI x l (P.power*n)*D) := mul_le_mul he (by unfold D; rw [←hk]; exact foal hB hi l) (zero_le_one.trans (heft_one ..)) (by positivity) -- tune
   _ = 2*D*B.threshold:=by field_simp
   _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hy'.le (spine_one ..)) (by unfold D; positivity)
end P
end YM.CF.Siete
