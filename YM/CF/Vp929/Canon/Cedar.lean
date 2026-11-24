import YM.CF.Vp929.Canon.Tar
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
variable {U V X:Op (Single n)}
local notation "Et"=> SpaceM
open Cycle929
local notation "wF"=> (potion j M ∘ Haro.heroP)
lemma potsAdd (z:Momentum): wF (X+V) z= wF X z + wF V z:=by
 unfold Function.comp potion; rw [show heroP (X+V) z=heroP X z+heroP V z from ?_, mul_add,add_mul]; apply eq_add_of_sub_eq; rw [←Exa.weights,add_sub_cancel_right]
lemma potsScale (z:Momentum): wF (b • X) z=b • wF X z:=by unfold Function.comp potion; rw [coreF, Matrix.mul_smul, Matrix.smul_mul]
variable (w:1 ≤ j)
include w
local notation "ZD"=> zs j M
private lemma atV (i:Axis)(X:Op (Single n)): DifferentiableAt ℝ (fun t=> wF X (bout i t)) 0:=by
 have hp:DifferentiableAt ℝ (fun t:ℝ=> heroP X (bout i t)) 0:=by unfold heroP; apply DifferentiableAt.fun_sum; intro j _; unfold Laurent.mode Tap.bout; fun_prop
 let h:= (barox j w M i).differentiableAt; exact (((differentiableAt_const 1).sub h).mul hp).mul h
omit w
include w
lemma zd_s (i:Axis) : ZD (X+V) i= ZD X i + ZD V i:=by
 refine Eq.symm (((atV w i X).hasDerivAt.add (atV w i V).hasDerivAt).congr_of_eventuallyEq (Eventually.of_forall (fun x=> (potsAdd (bout i x) (M:=M))))|>.deriv |>.symm)
lemma zd_t (i:Axis): ZD (b • X) i=b • ZD X i:=(((atV w i X).hasDerivAt).const_smul b).congr_of_eventuallyEq (Eventually.of_forall (fun y=>(potsScale (bout i y)))) |>.deriv
omit w
abbrev spaL: Pal→L[ℝ] Op SU.Slot := (show Pal→ₗ[ℝ] Op SU.Slot from ⟨⟨fun x=>spaX x 0,pedal⟩,fun r X=>pedal_r _ _⟩).toContinuousLinearMap
def pickM : Pal→L[ℝ] ((SpaceM):Type) := projectorMind.toContinuousLinearMap.comp spaL
lemma pickM_left {x:Pal}(p:Mind (spaX x 0)): (pickM x).val= spaX x 0:=by
 unfold pickM; change (projectorMind _).val=spaX x 0; unfold projectorMind; rw [Submodule.projectionOnto_apply_of_mem_left _ p]; rfl
def pointW (n:Side)(j:ℕ)(w:1 ≤ j)(M:Male): Op (Single n) →L[ℝ] (SpaceM:Type) :=pickM.comp ((show Op (Single n) →ₗ[ℝ] Pal from ⟨⟨fun x=> zs j M x 0,fun x y=>zd_s w 0⟩, fun r x=> zd_t w 0⟩).toContinuousLinearMap)
def pointC (n:Side)(j:ℕ)(q:ℝ)(M:Male):Op (Single n) →L[ℝ] (SpaceM:Type):= by
 let γ:=fun X:Op (Single n)=> sovX q (potion j M (heroP X)); refine pickM.comp ((show Op (Single n)→ₗ[ℝ] Pal from ⟨⟨γ,fun x y=>?_⟩,fun r x=>?_⟩).toContinuousLinearMap)
 · unfold γ sovX
   have t(z:Momentum): potion j M (heroP (x+y)) z = potion j M (heroP x) z+potion j M (heroP y) z:=potsAdd _
   simp_rw [t,smul_add,sum_add_distrib,smul_add]
 unfold γ sovX; simp_rw [show ∀ z,potion j M (heroP (r • x)) z= r • potion j M (heroP x) z from fun z=>potsScale z]; rw [show RingHom.id ℝ r=r from rfl, smul_comm r]; refine congrArg (fun p:Pal=>(16*q)⁻¹ • p) ?_; rw [smul_sum]; exact sum_congr rfl (fun i _=> smul_comm ..)
lemma pointE : pointC n j q M (StackL F univ)= waveTest q F j M :=rfl
include w in
lemma pointCash (u:AxisP (heroP X)): (pointW n j w M X).val=τ_ j M X:= pickM_left (normalization j w M u).2.1
lemma cw_bear (t:s⊆univ): Logic P a (fun F:RegBudget n=> StackL F s):= Logic.ballot s _ (fun i _=>Logic.comp ((show Cipher n→ₗ[ℝ] Op (Single n) from ⟨⟨ orbitPH, fun x y=>Haro.orbP x y⟩,fun r f=>Fixed.Voltage.orbit_smul _ _⟩).toContinuousLinearMap) (itemQ _ 1))
abbrev aimC (j:ℕ)(w:1 ≤j):= (48*‖pickM‖*ξP + ‖pickM‖*ξP)*fixC j w
include w
lemma fixC_p: 0 ≤ fixC j w:=by
 unfold fixC; have p:0 < pawe j w true:= (pawn_p j 2 w true).choose_spec.1; have hp: 0 < pawe j w false:= (pawn_p j 2 w false).choose_spec.1; positivity
lemma aimC_p: 0 ≤ aimC j w:=mul_nonneg (by unfold ξP; positivity) (fixC_p w)
lemma cake (e:P.supportExponent=1)(v:P.power=2) (g:IncX Utrue F P a b)(y:1 ≤ a) (p:Frequency L n q):‖waveTest q F j M - pointW n j w M (StackL F (treeΘ P L.val))‖≤ aimC j w* (Real.exp (-(mstar L.val:ℝ))*b/a^2):=by
 let T:Finset (Scree.Hub n):= treeΘ P L.val; let X:=StackL F T; let Y:=StackL F Tᶜ; let V:= StackL F univ; let ξ:=Real.exp (-(mstar L.val:ℝ)); let δ:= b/a^2; let C:=fixC j w; let Γ:=‖pickM‖*ξP; have hξ:Real.exp (- (L.val:ℝ)) ≤ ξ:=Real.exp_le_exp.mpr (neg_le_neg (Nat.cast_le.mpr (root_le _)))
 have hm: V=X+Y:=(sum_add_sum_compl T _).symm
 have U1:Scoria j M Y (C*(ξ*δ)):=by
    have hl (i:Scree.Hub n)(t:i∈Tᶜ) : mstar L.val ≤ coverNumber P.B i.val.2:=by
      apply le_of_not_gt; intro h; exact (mem_compl.mp t) (mem_filter.mpr ⟨mem_univ _,(paves L.val _).2 h⟩)
    simpa only [Y,T,C,ξ,δ,e,one_mul,mul_div_assoc] using gem (live_other (plea n P L.val)) g y v w M (mstar L.val) hl
 have U2: Scoria j M V (C*δ):=by
    obtain h:=gem (live_full n) g y v w M 0 (fun i _=> Nat.zero_le _); simpa only [Nat.cast_zero,mul_zero,neg_zero,Real.exp_zero,one_mul] using h
 let A(p):= pointW n j w M p; let B(p):=pointC n j q M p; let G:= 48*‖pickM‖*ξP; have hp: T=treeΘ P L.val:=rfl
 have ht : ‖B V-A V‖ ≤ G * (C * (ξ*δ)):=by
    obtain ⟨h,pΨ,r⟩:= U2.earm; obtain hT:= tier2 p pΨ r (Psy j w M U2.axisP); change ‖pickM (sovX q (potion j M (heroP V))) - pickM (zest j M (WW V) 0)‖ ≤ _; rw [←map_sub]; refine (pickM.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hT (norm_nonneg _)).trans ?_)
    rw [show ‖pickM‖ * (48*ξP * q * (C*δ))=G*C*δ*q by unfold G; ring]; refine (mul_le_mul_of_nonneg_left (p.small.trans hξ) ?_).trans_eq (by ring); unfold δ C G; have hx:0 ≤ b:=Fixed.Voltage.spent_E P _ g y; have hb := fixC_p w; unfold ξP; positivity
 have hv: ‖A Y‖ ≤ Γ* (C*(ξ*δ)):=by
    obtain ⟨h,r,k⟩:=U1.earm; refine (pickM.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ((Haro.burn _ _ k (by decide) r (Psy _ w _ U1.axisP)).2 0) (norm_nonneg _)).trans_eq (by unfold Γ; ring))
 rw [←pointE]; change ‖B V-A X‖ ≤ _; rw [show B V-A X=(B V-A V)+A Y from ?_]; swap; · rw [show A V=A X+A Y from by unfold A; rw [hm,map_add]]; abel
 apply (norm_add_le ..).trans; exact (add_le_add ht hv).trans_eq (by unfold aimC Γ δ G C ξ; ring)
omit w
lemma ovis (P':BudgetPoint){Z:RegBudget n}(g:IncX Utrue F P a b)(z:IncX Utrue Z P' d t)(e:(1-ρX)*StackL F univ*ρX=(1-ρX)*StackL Z univ*ρX)(a':1≤ a)(q':P.power=2)(h:1 ≤ d)(v:P'.power=2)(r:Frequency L n q)(w:1 ≤j): waveTest q F j M=waveTest q Z j M:=
 congrArg (fun x=>pickM x) (sov_back r e (gem (live_full n) g a' q' w M 0 fun _ _=>Nat.zero_le _) (gem (live_full n) z h v w M 0 fun _ _=>Nat.zero_le _))
end TestW
end Test
end YM.CF.Py.Rate
