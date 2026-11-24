import YM.SatinExist.Danish
import YM.SatinExist.Ione
import YM.SatinExist.Luminous
import YM.SatinExist.Twin
/-! # Real fields on these actual labels. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open SatinTails SatinJets Boundary Spectral
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
variable (P:Spine)(x:P.Spectrum0 3)
local notation "X"=>P.ColorHil 3 (P.advocate 3 x 3)
local notation "Y"=>P.ManyF 3 (P.advocate 3 x 3)
local notation "ℰ" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "R"=>P.seasons 3 (P.advocate 3 x 3)
local notation "Λ"=>P.kiosk 3 (P.advocate 3 x 3)
local notation "E"=> (ℰ).E
local notation "U"=> (R).E
local notation "V"=>P.advocate 3 x 3
local notation "Ω" =>P.heaven 3 V
local notation "Pτ" F:max a:max b:max=>P.pillar 3 V F (- (a:ℝ)) (b:ℝ) 0
variable (A:ℕ→P.Apron) (k:ℕ)(L:(P.ManyF 3 (P.advocate 3 x 3)).Op)
variable (p:P.Concerto x A k L)
include p
lemma Concerto.profile(t:ℝ≥0)(h:0<t)(w:∀ i,P.birthF 3 (A i).s (A i).F):Tendsto (fun i=>P.cradleG x (A i) (w i) (t:ℝ)) atTop (𝓝 ((plated (R) L (r:=k) t) (P.heaven 3 (P.advocate 3 x 3)))):=by
 refine (p.purchase t h).brakes (Ω)|>.congr' ?_
 filter_upwards [p.thin.eventually (gt_mem_nhds h)] with i hi
 rw [P.once_in, P.cradle_bank];
 let t':= (t:ℝ)
 have he:(A i).realWidth P 3< t':= (P.bookRig _).symm.trans_lt (NNReal.coe_lt_coe.mpr hi)
 let q:= (A i).realWidth P 3; let v:= P.thinOrigin x (A i) (w i)
 apply congrArg (⇑(P.wealth 3 V));
 change E _ _=E _ _; rw [P.thinRawEntry x _ (w i),←ContinuousLinearMap.comp_apply,←(ℰ).time]
 exact congrArg (fun y:ℝ≥0=>E y v) (by change (t'-q).toNNReal+q.toNNReal= t'.toNNReal; rw [← Real.toNNReal_add (sub_nonneg.mpr he.le) ((A i).real_width_pos P 3).le,sub_add_cancel])
lemma Concerto.kissPrice : P.Concerto x (fun i=> (A i).kiss P 3) k (star L):=by
 refine ⟨p.thin,p.high,fun a u=>?_⟩
 apply (p.purchase a u).starR.sameC _
 · unfold plated; simp_rw [Real.toNNReal_coe,star_mul,(parRev (R) a k u).star_eq]; rw [mul_assoc]
 apply Eventually.of_forall; intro i
 exact (P.reflectsW x A 3 i [] a).symm
omit p
variable (N:P.PowerNames x A)
variable (Z:Lead.Clan)(c r n:ℕ→ℕ)(w:Lead.Clan→Prism)
local notation "Σ"=> N.fields 3
local notation "𝓻"=> N.rate 3
abbrev weightL := demerit Z • ((N.fields 3) [])
abbrev heightPA (Z:Lead.Clan) := ariaM (w Z) (𝓻 [])
abbrev legR := P.ariaL x (w Z) (P.weightL x A N Z)
local notation "X'"=>P.weightL x A N Z
local notation "A'" j:max=>P.stitchApron Z (A j) (c (n j)) (r (n j))
variable (S:P.Snapdragon x c r A n)
include S
lemma rotorPrice (g:P.LargeM c r)(h':StrictMono c):
 P.Concerto x (P.soldTrumpet A c r n w Z) (P.heightPA x A N w Z) (P.legR x A N Z w):=by
 let M:= 𝓻 []
 let f:=Σ []
 have Q:= N.price 3 []
 apply chordConcert P x (w Z) (fun j=> A' j) M (X')
 refine ⟨P.dragon_stamps x c r Z A n g S Q,h'.tendsto_atTop.comp S.allow.fast.tendsto_atTop,fun a u=>?_⟩
 apply (P.snapBrakes x c r Z A n g S Q a u).sameC (Eventually.of_forall fun i=>rfl)
 rw [N.paid _ _ a u]; unfold plated weightL; simp only [Real.toNNReal_coe, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; rfl
omit S
lemma twin_alias : P.Concerto x (P.bareTwin A w Z) (P.heightPA x A N w Z) (P.legR x A N Z w):=by
 let M:= 𝓻 []
 let J(i:ℕ):= P.pricedTwinBase (A i) Z
 have Q:= N.price 3 []
 have hc:Tendsto (fun i=> (A i).realWidth P 3) atTop (𝓝 0):= Q.prices.thin
 have hv(i:ℕ):P.zt (J i)= P.zt (A i):=rfl
 apply chordConcert P x (w Z) J M (X')
 have h:Tendsto (fun i=>P.zt (J i)) atTop (𝓝 0):=by apply NNReal.tendsto_coe.mp; simp_rw [hv,P.bookRig]; exact hc
 refine ⟨h,P.height_of_width A 3 hc,fun a u=>?_⟩
 have ht:= Q.prices.paid a u; simp_rw [one_smul] at ht
 apply (ht.pump (demerit Z)).sameC _
 · rw [N.paid _ _ a u]; unfold plated weightL; simp only [Real.toNNReal_coe, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; rfl
 filter_upwards [h.eventually (ge_mem_nhds u)] with i hi
 change demerit Z • (Pτ (A i) a a)= (Pτ (J i) a a)
 have hp:P.zt (J i) ≤ a:= hi
 have hu':P.zt (A i) ≤ a:=hp
 have he:(J i).engine P 3 V= demerit Z • (A i).engine P 3 V:=by
    let w:=(A i).u 3; let x₀:=add_pos ((A i).pos 3) ((A i).pos 3); let p:= P.shifts 3 (w:ℕ);
    apply P.values_too 3 V (A i).s (w+w) x₀ (P.meterRule0 3 V (J i));
    have hx:=P.prismS_astr 3 V (A i).s (w+w) x₀ (demerit Z) (P.meterRule0 3 V (A i)) (P.prism_null 3 V _ _ x₀)
    rw [add_zero, add_zero, ← map_smul] at hx; exact hx
 rw [P.stampPoint x (A i) _ _ hu' hu', P.stampPoint x (J i) _ _ hp hp, hv,he,P.kiosk_scale,Algebra.mul_smul_comm,Algebra.smul_mul_assoc] -- I direction
-- turns into magnetic response W
variable {v:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
-- unnecessary
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
