import SatinFixedContrastNovember4
import YM.SU5.Assay.Starter
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six
variable (P:Spine)(R:P.Register)(x:P.Spectrum0 3)
local notation "Zs"=>Ballad.Lead.Clan
local notation "κ"=>P.coffee 3 x
local notation "σ"=>P.rawSlot 3 x
local notation "β"=>P.base 3 x
local notation "Ω"=>P.heaven 3 x
local notation "O"=>(P.ManyF 3 x).Op
local notation "⟪" T "⟫"=> inner ℂ Ω ((T:O) Ω)
local notation "L"=>P.LagOp 3 x
variable (A : Lead.Clan → ℕ→P.Apron)(l:Lead.Clan→ℕ→P.Folio)(T:Lead.Clan→P.LagOp 3 x)
variable (B : Lead.Clan → ℕ→P.Apron)(m:Lead.Clan→ℕ→P.Folio)(U:Lead.Clan→P.LagOp 3 x)
/-!
 Cost of repeating the actual stocks: every entry in stock normalization
 with THAT COMPANY'S price; the whole pole is scalar pricing on available
 arms. Thus nonzero discrepancies *without* reproducing the old rank or
 any nontrivial connected price in this test. A first estimate.
-/
variable (M:P.Menagerie)
local notation "λ₀"=>P.electro M
local notation "U₀"=>P.visor x M
local notation "T₀"=>P.starboard x (U₀)
local notation "w"=>(P.seasons 3 x).wax
local notation "ι"=>P.unitLag 3 x
lemma face_fore (Z:Lead.Clan):(T₀) Z=star (λ₀ Z)•ι:=by
 unfold starboard visor; rw [P.otherLag_scale,P.unit_otherLag]
-- symmetric because F,G normalized and real
variable {a b c:ℝ}{F G:SampleDose}
lemma sip (Z:Lead.Clan)(u:Walled 3 F a b 0)(f:F.Normalized):
 κ (U₀ Z) a b F=λ₀ Z• w (b-a) ∧ κ ((T₀) Z) a b F=star (λ₀ Z) • w (b-a):=by
 rw [P.face_fore]; unfold visor;rw [coffee_scale (P.unit_credits 3 x) u,coffee_scale (P.unit_credits 3 x) u,P.unit_coffee _ _ u f];exact ⟨rfl,rfl⟩
private lemma eΩ (t:ℝ)(z:ℂ): (z•w t:O) Ω=z•Ω:=by rw [ContinuousLinearMap.smul_apply];unfold wax;rw [P.heaven_hot]
private lemma oΩ: inner ℂ Ω Ω=1:=by rw [inner_self_eq_norm_sq_to_K,P.stone_norm];norm_num
lemma sip_read (Z:Lead.Clan)(u:Walled 3 F a b 0)(f:F.Normalized): ⟪κ (U₀ Z) a b F⟫=λ₀ Z ∧ ⟪κ ((T₀) Z) a b F⟫=star (λ₀ Z):=by
 obtain ⟨t,y⟩:=P.sip x M Z u f
 rw [t,y,eΩ,eΩ,inner_smul_right,inner_smul_right,P.oΩ,mul_one,mul_one];exact ⟨rfl,rfl⟩

def fee :CrossRead:=Matrix.vecMulVec (fun Z=>star (λ₀ Z)) λ₀
lemma fee_value (u:Walled 3 F a b 0)(v:Walled 3 G b c 0)(f:F.Normalized)(g:G.Normalized):P.seatPair x a b c F G (T₀) (U₀)=P.fee M:=by
 ext1 Z W
 change inner ℂ Ω ((κ ((T₀) Z) _ _ _) ((κ (U₀ W) _ _ _) Ω))=star (λ₀ Z)*λ₀ W
 rw [(P.sip _ _ _ u f).2,(P.sip _ _ _ v g).1,P.eΩ,map_smul,P.eΩ,inner_smul_right,inner_smul_right,P.oΩ]
 ring
lemma fee_denial: (P.fee M).det=0 ∧ (P.fee M).rank≤1:= ⟨Matrix.det_vecMulVec _ _,Matrix.rank_vecMulVec_le _ _⟩

-- Explicit uniform lower comparison, in original stock pricing

def lobby : Set CrossRead:={z|∀ (Z W:Ballad.Lead.Clan), purePrice Z/2*(purePrice W/2)<‖z Z W‖}
lemma lobby_open:IsOpen lobby:=by
 have h (i j:Zs):Continuous (fun z:CrossRead=>‖z i j‖):=((continuous_apply j).comp (continuous_apply i)).norm
 rw [show lobby= ⋂ (i:Zs) (j:Zs), (fun z:CrossRead=>‖z i j‖)⁻¹' Set.Ioi (purePrice i/2*(purePrice j/2)) by ext;simp [lobby]]
 exact isOpen_iInter_of_finite fun i=>isOpen_iInter_of_finite fun j=>isOpen_Ioi.preimage (h i j)
lemma lobby_entry {f:CrossRead}(h:f∈lobby)(Z W:Zs):f Z W ≠0:= norm_ne_zero_iff.mp (lt_trans (mul_pos (half_pos (purePrice_p Z)) (half_pos (purePrice_p W))) (h Z W)).ne'
variable {M P}
lemma Company.fee_entry {n:ℕ} (h:P.Company n M (1/2)):P.fee M∈lobby:=by
 have v(Z:Zs): purePrice Z/2<‖λ₀ Z‖:=by
   have a:= norm_sub_norm_le 1 (M Z).y
   rw [norm_sub_rev,norm_one] at a
   have b:(1:ℝ)/2<‖(M Z).y‖:=by linarith only [a,(h.tariff Z).1]
   rw [electro,norm_mul,Complex.norm_real,Real.norm_of_nonneg (purePrice_p Z).le,show purePrice Z/2= 1/2*purePrice Z by ring]
   exact mul_lt_mul_of_pos_right b (purePrice_p Z)
 intro Z W; change _ < ‖star (λ₀ Z)*λ₀ W‖
 rw [norm_mul,norm_star]
 gcongr ?_ * ?_
 · exact (half_pos (purePrice_p Z)).le
 · exact (half_pos (purePrice_p W)).le
 · exact v Z
 · exact v W
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
