import YM.SU5.Hiro.LunchBox
import YM.SU5.Aria.Prima
/-! # concrete late schedule with positive cost. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Hiro Ballad Papal Regis.Head Regis.Head.Brecht Regis.Circuit
open Twah (DirSpin)
open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn
open CF.Pannier.Chancel
namespace Spine
open Stationary (Gaia)
variable (P:Spine)
local notation "K"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "F"=> Prototype.goldF
local notation "δ"=> ruler P.par.block
abbrev platterWidth :ℕ:=P.calibration.ℓ+10
local notation "D"=> P.platterWidth
def rosemary(n:ℕ) : Cover:= fun i=> if i=(3:Axis) then (n:ℕ)+3* (D:ℤ) else 3*(D:ℤ)
def rangeClasp(n:ℕ): Cover:= (ruler P.par.block) • P.rosemary n
local notation "U" n:max=> P.rangeClasp n
lemma rosemary_hi(n:ℕ)(i:Axis):3*(D:ℤ) ≤ P.rosemary n i:=by unfold rosemary; split; omega; rfl
abbrev pianist (P:Spine):ℝ:= ruler P.par.block
local notation "rC"=> P.pianist
lemma holy :0< (rC):= by unfold pianist; exact_mod_cast ruler_gene P.par.block
abbrev pairMood:DirSpin:=(0,0)
def supper := shotR (X:=corner P.pianist) pairMood pairMood* speckleV F F SU.group (corner P.pianist)
lemma service_space : corner P.pianist≠0:=fun v=> (by have he:=congrArg (fun t:Gaia=> t (3:Axis)) v; simp [corner] at he; exact absurd he (ruler_gene _|>.ne'))
lemma supper_money : 0< ‖P.supper‖ := by
 have hj:=P.service_space; have hp:0< ‖corner rC‖:=norm_pos_iff.mpr hj
 have hx: Maxwell.bareCurl 0 1 0 1 (corner rC)=4*Maxwell.normal*(‖corner rC‖^2)⁻¹^2:=by
    rw [Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad hj,Maxwell.Bare.opp_grad hj]; simp only [↓reduceIte,Maxwell.second_Green hj]; norm_num [corner,show (0:Axis)≠3 from by decide,show (1:Axis)≠3 from by decide]; ring -- tune
 have hd:speckleV F F SU.group (corner rC)≠0:=by
    change (Fintype.card SU.group.ColorIndex:ℂ) * (↑(Maxwell.bareCurl 0 1 0 1 (corner rC)):ℂ)≠ 0; rw [hx]; haveI:Nontrivial SU.group.Color:=Thera.yet_one.nontrivial_color; have ht:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
    refine mul_ne_zero ?_ ?_; · change (Fintype.card (Fin SU.group.lieDim):ℂ)≠0; rw [Fintype.card_fin]; exact_mod_cast ht.ne'
    exact_mod_cast (mul_pos (mul_pos (by norm_num : (0:ℝ)<4) Maxwell.normal_pos) (by positivity :0<(‖corner rC‖^2)⁻¹^2)).ne'
 have hw:shotR (X:=corner rC) pairMood pairMood≠0:=by
    unfold shotR; let i:= Window.kernel rC; rw [show shotL _ pairMood pairMood=i from ?_,show shotL (-corner rC) pairMood pairMood= -i from ?_]; have hu:i≠0:=fun v=>by have ht:(0:ℝ)<Complex.re i:=Window.kernel_pos P.holy; rw [v,Complex.zero_re] at ht; linarith
    exact mul_ne_zero (mul_ne_zero (by norm_num) hu) (neg_ne_zero.mpr hu)
    · unfold shotL i; rw [show -corner rC=corner (-rC) from ?_,pencil_time, kernel_neg, if_pos rfl]; exact (PiLp.single_neg ..).symm
    unfold shotL i; simp only [pencil_time,pairMood,ite_true]
 exact norm_pos_iff.mpr (mul_ne_zero hw hd)
-- full blur witness along ALL axes including each spacelike coordinate separated by the given ruler
variable {r c:ℕ→ℕ}(v:Tendsto r atTop atTop)(h:∀ i,0<r i)
include v h
lemma posPilot : Tendsto (fun n=> Onyx.riseX (r n) (P.rangeClasp (r n)-(0:ℕ→ Cover) n)) atTop (𝓝 (corner rC)):=by
 let A:=δ; let f(n):= r n; have hx:= tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp v; let Z:Cover:=A • fun i:Axis=>3*(D:ℤ)
 let g(k:ℕ):= Onyx.riseX (f k) (U (r k)- (0:Cover)); have ht(i:Axis): Tendsto (fun n=>(g n i:ℝ)) atTop (𝓝 (corner rC i)):=by
    let d(k):= (Z i:ℝ)/(r k:ℝ); have hd:Tendsto d atTop (𝓝 0):= tendsto_const_nhds.div_atTop hx; by_cases e:i=3
    · subst i; have he:= hd.const_add (rC); rw [add_zero, ← show corner rC (3:Axis)=_ from (by simp [corner] : corner rC 3 = rC)] at he; refine he.congr fun k=>?_ ; change ↑A+d k= _; have hv:= h k; simp [d,g,Z,Onyx.riseX,Onyx.moor,f,A,rangeClasp,rosemary]; field_simp; try ring
    rw [show (corner rC i:ℝ)=0 from (by simp [corner,e])]; refine hd.congr (fun k=>?_); simp [d,g,rangeClasp,rosemary,e,f,Z,A,Onyx.riseX,Onyx.moor] -- notation rC issue
 exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr ht)
omit v h
-- witness orientation H
abbrev bulk (i:ℕ):ℝ:= rGauge r i
abbrev capsage (r:ℕ→ℕ)(i:ℕ):ℝ:= (rGauge r i)^5
lemma holdingK(i:ℕ)(w:0<r i):0<capsage r i:= by unfold capsage rGauge; positivity
local notation "μ" i:max=> P.costM r c i
noncomputable def fullMark (n:ℕ) := P.jade pairMood (r n) (F) (U (r n)) (holdingK n (h n)) (c n)
noncomputable def offMark (n:ℕ) := P.jade pairMood (r n) (F) (0:Cover) (holdingK n (h n)) (c n)
local notation "φ" i:max=> P.fullMark (c:=c) h i
local notation "χ" i:max=> P.offMark (c:=c) h i
variable (B:ℕ→ P.Test →ₗ[ℂ]ℂ)
def SeasonB:=P.Priceplate pairMood pairMood (F) (F) r c (P.rangeClasp ∘ r) 0 (fun i=> holdingK i (h i)) (tip r) B
include v h
lemma supper_law (a:P.SeasonB (c:=c) h B) : Tendsto (fun i=> μ i*(P.Nuptials (B i) (φ i) (χ i))) atTop (𝓝 (P.supper)):=by
 apply P.ripeness pairMood pairMood _ _ r c (P.rangeClasp ∘ r) 0 (fun i=> holdingK i (h i)) B v h (P.posPilot v h) P.service_space ?_ a -- b? check
 have he:Tendsto (rGauge r) atTop atTop:= (tendsto_natCast_atTop_atTop.comp v).const_mul_atTop (by norm_num : (0:ℝ)<2); apply (tendsto_inv_atTop_zero.comp he).congr; intro i; have hw:0<rGauge r i:=by unfold rGauge; specialize h i; positivity
 change _⁻¹= (rGauge r i)^4/(rGauge r i)^5; field_simp
lemma earned (a:P.SeasonB (c:=c) h B) : Tendsto (fun i=>μ i*(B i ((φ i)*(χ i)))) atTop (𝓝 (P.supper)):=by
 have hp:= P.fundTip r c h (fun i=> B i (φ i)*B i (χ i)) (by filter_upwards [(show Priceplate _ _ _ _ _ _ _ _ _ _ _ _ from a).first,(show Priceplate _ _ _ _ _ _ _ _ _ _ _ _ from a).last] with i p b; rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (b.trans (min_le_left ..))).trans p)
 have he:= (P.supper_law v h B a).add hp; rw [add_zero] at he; refine he.congr fun i=>?_ ; unfold Nuptials; ring
lemma entitlement (a:P.SeasonB (c:=c) h B) :∀ᶠ i in atTop, ‖P.supper‖/2< ‖P.costM r c i*P.Nuptials (B i) (φ i) (χ i)‖ ∧ ‖P.supper‖/2< ‖P.costM r c i*(B i ((φ i)*(χ i)))‖:= by
 have he:=half_lt_self P.supper_money; exact ((P.supper_law v h B a).norm.eventually (lt_mem_nhds he)).and ((P.earned v h B a).norm.eventually (lt_mem_nhds he)) -- lt vs gt
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.supper_law
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.entitlement
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.supper_money
