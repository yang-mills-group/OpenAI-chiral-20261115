import YM.CF.Siete.Porous
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Skye Scree Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n j l:ℕ}{K M' H C Q b v a ε r u R x:ℝ}{c f:Side}{L:Side}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{P B:BudgetPoint}{X X':Support (More f)}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]
local notation "G"=>SU.group
section P
variable (M:Museum F x A X' Y I) (T:Tube G S) (V:Pane c)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(N:Pane f)(Z:LogArray G (Active A x F))(g:Seat c→SU.E)(e:Bond (More f))
local notation "o'" => S.ratio.parent e.1
local notation "s"=> loom P (Heir.reach x) b
local notation "zQ" => sphereQ V o' (Heir.reach x) g
local notation "δ"=>sonic T M β k q d l N Z g e.1 V
local notation "V'"=> hail M T V β k q d l N Z g e
local notation "z"=> reply T F x k g e
local notation "g_"=> atoms T M β k q d l N Z g ∘ increment V
variable {α t:ℝ}
lemma fires (J:Guide _ (P.dirBound o') 0 g_ n α) (p:Nut P V o' (Heir.reach x) n a b r g)(hp: α ≤ s): Guide _ (P.dirBound o') 0 V' n s:=by
 have he: Guide _ (P.dirBound o') 0 δ n s:=(step_guide p).duo (J.rise hp)
 refine he.duo (g:=fun _=>δ 0) ⟨contDiffAt_const,fun j y w hv=>?_⟩
 by_cases h:j=0
 · subst j; rw [iteratedFDeriv_zero_apply]; exact he.size
 rw [iteratedFDeriv_const_of_ne h]; change ‖(0:Deck G (More c) (More f))‖ ≤ s; rw [norm_zero]; exact (norm_nonneg _).trans he.size
lemma loud (o:Seat f)(ho:o∈X)(hb:e.1∈inspected X)(J:Guide _ (P.dirBound o') 0 g_ n α)(hT: Act T F x k n t Q)(hQ:1 ≤ Q)(p: Nut P V o' (Heir.reach x) n a b r g)(hp:α ≤ s)(ha:s ≤ t)(hK:s≤1)(ht:P.threshold=temp x)(hy:2 ≤ n)(hu:0<j)(hv:j≤n)(w:Fin j→tangD c)(he:∀ i,P.dirBound (S.ratio.parent o) (w i)): ‖iteratedFDeriv ℝ j (z ∘ V') 0 w‖≤ ‖woody T F (iteratedFDeriv ℝ j zQ 0 w) e‖ + (clinicFee n Q*s^2+α)*heft n X P B :=by
 let A':= clinicFee n Q*s^2; have hz :=p.hC.trans p.hQ; have hi:= P.threshold_pos
 have hr: temp x ≤ s:=by rw [←ht]; unfold loom; exact le_trans (le_mul_of_one_le_left hi.le hz) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by simp; positivity)))
 have hx:= fires M T V β k q d l N Z g e J p hp
 let L:=realStroke T F; let R:=echo T F x k
 let W:= iteratedFDeriv ℝ j (R ∘ V') 0 w; let ψ:=iteratedFDeriv ℝ j (L ∘ V') 0 w; let z':= iteratedFDeriv ℝ j δ 0 w
 have hh:= (hT.calibrated.uniform _ (hx.size.trans ha)).smooth.comp (f:=V') 0 hx.1
 have hl:ψ= (Heir.mainStroke T F false) z':=by
    unfold ψ; rw [L.iteratedFDeriv_comp_left hx.1 (Nat.cast_le.mpr hv)]
    change (Heir.mainStroke ..) (_-(_:_))=(Heir.mainStroke T F false) _
    have hy: Guide _ (P.dirBound o') 0 δ n s:=(step_guide p).duo (J.rise hp); unfold hail; rw [iteratedFDeriv_prodMk hy.1 (contDiffAt_const (c:=δ 0)) (Nat.cast_le.mpr hv), iteratedFDeriv_const_of_ne (Nat.ne_of_gt hu)] -- tune
    exact congrArg _ (sub_zero z')
 let D:= woody T F (iteratedFDeriv ℝ j zQ 0 w)
 have hsc : ψ=D+iteratedFDeriv ℝ j g_ 0 w:=by rw [hl]; unfold z'; change Heir.mainStroke T F false (iteratedFDeriv ℝ j (fun x=>(zQ x,(g_) x)) 0 w)= _; rw [iteratedFDeriv_prodMk (step_guide p).1 J.1 (Nat.cast_le.mpr hv)]; rfl
 have hga:0≤α:=(norm_nonneg _).trans J.size
 have hg: ‖ψ-D‖ ≤ α*heft n X P B:=by rw [hsc,add_sub_cancel_left]; exact (rise_i j (J.2 _ hv) w he).trans ((mul_le_mul_of_nonneg_right (heft_bounds S ho hb hv) hga).trans_eq (mul_comm ..))
 have hG: ‖W-ψ‖ ≤ A'*heft n X P B:=by
    unfold W ψ; rw [←show iteratedFDeriv ℝ j ((R-⇑L) ∘ V') 0 w= _ - _ from ?q]; swap
    · rw [show (R-⇑L) ∘ V'=R ∘ V' - L ∘ V' from rfl,iteratedFDeriv_sub_apply (hh.of_le (Nat.cast_le.mpr hv)) ((L.contDiff.contDiffAt.comp 0 hx.1).of_le (Nat.cast_le.mpr hv))]; rfl
    have hu: Guide _ (P.dirBound o') 0 ((R-⇑L) ∘ V') n A':= handle hT.calibrated hr (zero_le_one.trans hQ) hK ha hx hy
    exact (rise_i j (hu.2 _ hv) w he).trans ((mul_le_mul_of_nonneg_right (heft_bounds S ho hb hv) ((norm_nonneg _).trans hu.size)).trans_eq (mul_comm ..))
 have he :‖W e‖ ≤ ‖D e‖+(A'+α)*heft n X P B:=by
    have h : ‖W-D‖ ≤ (A'+α)*heft n X P B:=by rw [add_mul]; exact (norm_sub_le_norm_sub_add_norm_sub W ψ D).trans (add_le_add hG hg)
    refine le_trans ?_ (add_le_add_right ((norm_le_pi_norm (W-D) e).trans h) _); simpa using norm_add_le (D e) ((W e) - D e)
 let H: tangD f →L[ℝ] SU.group.Color:= (SU.group.adjoint ((g (S.ratio.parent e.1))⁻¹)).toContinuousLinearMap.comp (ContinuousLinearMap.proj e); rw [show z ∘ V'= H ∘ (R∘ V') from rfl,H.iteratedFDeriv_comp_left hh (Nat.cast_le.mpr hv)]; change ‖SU.group.adjoint _ (W e)‖ ≤ _; rw [SU.group.norm_adjoint]; exact he
end P
end YM.CF.Siete
