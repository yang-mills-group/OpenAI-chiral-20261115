import SatinFixedContrastNovember4
import SatinThinQuizLevel
/-!
# Milestone 15.II. Apply to our shrinking probes! Identify the common limit kernels

Use the *same* centered positions and **actual state** on both series, at every
point of positive strict order in the limit (no Plenum needed for the positive-time
`commonWell` limit). Also receive the smearings at **any** positive-wall supports.
Our limiting position kernel coincides with the limit of that very `commonWell`.
It reproduces the price on all these smears. Don't claim at arbitrarily small
central time gap on each stencil itself-- `WallBefore, WallAfter, Turnstile` conditions.
No price asserted at boundary. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 310000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "γ"=> P.cartage 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "λ'"=> P.enter 3 ξ

section general
private lemma thermal_pivot (X:Hilbert) (S':OS.Semigroup X 3)(U:X.Op)(t:ℝ≥0)(u:∀ x:X, S'.E (t/2) (U x)=U (S'.E (t/2) x))(x y:X):
   inner ℂ x (U (S'.E t y))= inner ℂ (S'.E (t/2) x) (U (S'.E (t/2) y)):= by
 rw [S'.swing,u,←ContinuousLinearMap.comp_apply (S'.E (t/2)) (S'.E (t/2)),← S'.time,add_halves]
-- general time gap (no symmetric seam assumption)-- unequal-width formula
lemma at_half_gap (A B:P.Apron)(f:P.birthF 3 A.s A.F)(g:P.birthF 3 B.s B.F)(p q:Vantage)(J:P.Ellis 3 x) (h:p 3 + A.realWidth P 3 < q 3 - B.realWidth P 3):
   P.commonWell 3 x (usher (A.kiss P 3) B) (usher p q) [false,true]=
      inner ℂ (P.cradleG x A f ((q-p) 3 / 2)) (γ (q-p) (P.cradleG x B g ((q-p) 3 / 2))):= by
 let t:ℝ:= (q-p) 3; let d:= t.toNNReal
 have p':0≤ t:= by change 0≤ q 3-p 3; linarith only [h,A.real_width_pos P 3,B.real_width_pos P 3]
 rw [P.thin_kernel x A f B g p q J h]; change inner ℂ _ (γ (q-p) ((Ε).E d (π' (P.thinOrigin x B g))))=_; rw [thermal_pivot G (Ε) (γ _) d (fun z=> P.warm_drive 3 ξ _ _ z)]
 have he:d/2=(t/2).toNNReal := by
    apply NNReal.eq; rw [Real.coe_toNNReal,NNReal.coe_div,NNReal.coe_two,show (d:ℝ)= t from Real.coe_toNNReal t p']; positivity
 change inner ℂ ((Ε).E (d/2) _) (γ _ ((Ε).E (d/2) _))=_; rw [he]
end general

variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "Λ"=> P.profilesZ x V w
local notation "ΛH[" z "]"=> P.profilesH x w z V
local notation "W"=> P.soldTrumpet A c r n w
local notation "ℒ"=> Lead.Clan
variable (T:P.HandleWith x c r A n)
local notation "B[" z "," i "]"=> P.sold_birth x A c r n w z i T
variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x) (μ:ℝ)(a b:Lead.Clan)
variable (F U:SampleDose)
include R
include J in
lemma illuminate_globe {p q:Vantage}(u:p 3<q 3):
   Tendsto (fun i=>P.commonWell 3 x (usher ((W a i).kiss P 3) (W b i)) (usher p q) [false,true]) atTop
      (𝓝 (P.pointPrism x V w (q-p) a b)):= by
 let t:ℝ:= (q-p) 3 / 2; have pt:0<t:= half_pos (sub_pos.mpr u); let v:=γ (q-p)
 refine ((R.heated_points a t pt).2.inner (𝕜:=ℂ) ((v.continuous.tendsto _).comp (R.heated_points b t pt).2)).congr' ?_
 have hz:0<(q-p) 3:=sub_pos.mpr u
 have he:= (R.slender a 3).add (R.slender b 3); rw [zero_add] at he; filter_upwards [he.eventually (gt_mem_nhds hz)] with i t'
 exact (P.at_half_gap x _ _ B[a,i] B[b,i] p q J (show p 3+(W a i).realWidth P 3 <_ from by linarith only [show (W a i).realWidth P 3+(W b i).realWidth P 3< q 3-p 3 from t'])).symm
lemma illuminate_bank (t:ℝ)(p:0<t): π' (ΛH[a] t)= Λ a t :=
 tendsto_nhds_unique ((((π').continuous.tendsto _).comp (R.heated_points a t p).1).congr fun _=> (P.cradle_bank x ..).symm) (R.heated_points a t p).2
omit R
-- Earlier probe uses its **own flip test**. Need not involve later probe.
lemma illuminate_flip:
    P.readProfile x (flipDose F 3) μ (Λ a)= DoseTravel.beam G F (P.earlierProfile x V w μ a):=by
 let f(p:Vantage):=((flipDose F 3).val p:ℂ) • P.laterProfile x V w μ a p
 have he: MeasurePreserving (poseMirror 3).toMeasurableEquiv volume volume:= opposite_money 3
 refine (he.integral_comp' f).symm.trans (integral_congr_ae (Eventually.of_forall fun p:Vantage=>?_))
 let i:= opposeR 3 p
 change ((F.val (opposeR 3 i)):ℂ) • γ i (Λ a (max μ (i 3)))= (F.val p:ℂ) • γ p (Λ a (max μ (-p 3)))
 rw [show opposeR 3 i=p from reflectPose_twice 3 p,P.cart_mirror (x:=ξ),show i 3= -p 3 from if_pos rfl] -- x named? rw unfolds?

def forwardSite (F:SampleDose)(μ:ℝ) : Prop:= ∀ x∈ tsupport F.val,μ≤ x (3:Axis)
def backwardSite (F:SampleDose)(μ:ℝ) : Prop:= ∀ x∈ tsupport F.val, μ≤ -(x (3:Axis))
variable (u:0<μ)(p:backwardSite F μ)(q:forwardSite U μ)
include R J u
local notation "T₀"=> DoseTravel.beam (G) F (P.earlierProfile x V w μ a)
local notation "T₁"=> DoseTravel.beam (G) U (P.laterProfile x V w μ a)
-- fill order estimate even across grids & ANY tests
include q
lemma illuminate_forward :
   Tendsto (fun i=> P.thinKet x (W a i) (B[a,i]) U) atTop (𝓝 T₁) ∧
      ∀ t:ℕ→ℕ,Tendsto t atTop atTop→Tendsto (fun i=> P.thinGridKet x (t i) (W a i) (B[a,i]) U) atTop (𝓝 (λ' T₁)) :=
 ⟨P.dynamic_cont_ket x _ _ _ _ _ _ J (R.energy a).1 u (fun t=> P.illuminate_bank x A c r n w V g h T R a t) q (R.heated_points a μ u).1,
   P.dynamic_grid_ket x _ _ _ _ _ _ J (R.energy a).1 u (fun t=> P.illuminate_bank x A c r n w V g h T R a t) q (R.heated_points a μ u).1⟩
omit q
include p
lemma illuminate_backward :
   Tendsto (fun i=> P.thinKet x (W a i) (B[a,i]) (flipDose F 3)) atTop (𝓝 T₀) ∧
      ∀ t:ℕ→ℕ,Tendsto t atTop atTop→Tendsto (fun i=> P.thinGridKet x (t i) (W a i) (B[a,i]) (flipDose F 3)) atTop (𝓝 (λ' T₀)) :=by
 rw [←P.illuminate_flip x w V μ a F] -- order maybe
 refine P.illuminate_forward x A c r n w V g h T R J μ a (flipDose F 3) u fun x t=>?_
 have he: (poseMirror 3) x ∈ tsupport F.val:= (show x ∈ poseMirror 3 ⁻¹' tsupport F.val from flipBudget .. ▸ t)
 have t':= p ((poseMirror 3) x) he; change μ≤ -((opposeR 3 x) 3) at t'
 rwa [show opposeR 3 x 3= -x 3 from if_pos rfl,neg_neg] at t'
include q
lemma illuminate_seam : ∀ᶠ i in atTop, P.ThinSeam x (W a i) (W b i) B[a,i] B[b,i] F U:=by
 filter_upwards [(R.slender a 3).eventually (gt_mem_nhds u),(R.slender b 3).eventually (gt_mem_nhds u)] with i y z
 refine P.thin_price_seam x _ _ _ _ _ _ (R.sensor a i) (R.sensor b i) (fun v h=> ?_) (fun v h=>(zero_add _).trans_lt ((show _ < _ from z).trans_le (q v h))) J
 linarith only [p v h, show (W a i).realWidth P 3< μ from y]
omit J in
-- integral of limiting position kernel also defined through its limiting profiles.
lemma illuminate_price : P.readPrism x V w μ F U a b=
     ∫ p:Vantage,∫ q:Vantage,(F.val p:ℂ)*(U.val q:ℂ)*P.pointPrism x V w (q-p) a b:=by
 refine (both_integral G (weightedMoney F G _ (P.profile_solid x g h V w μ R.cinema u a).1) (weightedMoney U G _ (P.profile_solid x g h V w μ R.cinema u b).2)).trans ?_
 refine integral_congr_ae (Eventually.of_forall fun i=> integral_congr_ae (Eventually.of_forall fun j=>?_)); by_cases p': F.val i=0; · simp [p']
 by_cases q':U.val j=0; · simp [q']
 dsimp only

 rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal, P.prism_between x g h V w μ R.cinema u i j (p i (subset_closure p')) (q j (subset_closure q')),mul_assoc]; rfl
omit R J u p q
include R in
lemma illuminate_zero (i t:ℕ)(u:c (n i) ≤ t) :
   P.singleState 3 t x (P.prepared t (W a i) F)=0 ∧ P.singleState 3 t x (P.prepared t ((W a i).kiss P 3) F)=0 :=
 ⟨P.Dose_zero t _ _ x (R.vacuum a i) u,P.Dose_zero t _ _ x (((P.common_reading (c (n i)) x (W a i).F 3).2.2.1).trans ((congrArg star (R.vacuum a i)).trans (star_zero _))) u⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_forward
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_backward
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_globe
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_price
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_zero
