import YM.SU5.Assay.Outward
import YM.SU5.Assay.Punch
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
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
open Ballad Prototype Cordial
/-! Bind to the old expense. Any sufficiently late fixed index yields the
whole company even using the SAME gauge and spin wire as the earlier expense.
This conclusion remains before that index's two smears, orientations, etc.
-/
local notation "𝔏"=>Lead.Clan
local notation "τ"=>P.tock
local notation "μ"=>P.meanBox j
local notation "V"=>P.calibration.ℓ
local notation "b"=>ruler P.par.block
variable (n:ℕ)
def eider : ℕ:=1+ ∑j,P.probeClock n j
lemma eider_paid:P.BFits (P.eider n) (P.flash n).patio:=by
 intro i d v
 obtain ⟨u,w⟩:=P.shelters n i d (Finset.mem_union_left _ v)
 have h:P.probeClock n i ≤ P.eider n :=le_trans (by apply Finset.single_le_sum (f:=P.probeClock n) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left ..)
 have q:b*P.probeClock n i≤b*P.eider n:=by gcongr;exact (ruler_gene _).le
 rw [neg_mul] at u ⊢
 exact ⟨le_trans (by gcongr) u,w.trans q⟩
structure Company (M:P.Menagerie)(a:ℝ):Prop where
  clock:∀Z,(M Z).n=n
  cabin:∀Z,(M Z).width=P.eider n
  tariff:∀ Z,‖(M Z).y-1‖<a ∧ ‖(M Z).y⁻¹-1‖<a
variable {P}{r:P.Register}{w:Supplier}{d e:ℝ}
lemma Plume.company {g:ℕ→𝔏→ℂ}(u:P.Plume g)(h:uniform P r w d e){a:ℝ}(t:0<a):
  ∀ᶠ n in atTop,∃M,P.Company n M a ∧∀Z,(M Z).y=g n Z:=by
 filter_upwards [u.letter h t] with n p
 let M:P.Menagerie:=fun Z=>⟨n,P.eider n,g n Z,p.1,by unfold eider;omega,P.eider_paid _,(p.2 Z).1,u n Z⟩
 exact ⟨M,⟨fun _=>rfl,fun _=>rfl,fun Z=>(p.2 Z).2⟩,fun _=>rfl⟩
lemma funded_company (h:uniform P r w d e)(p:Tasting.Paid P.par){a:ℝ}(t:0<a): ∀ᶠ n in atTop,∃M,P.Company n M a:=by
 obtain ⟨g,q⟩:=p.quill
 filter_upwards [q.company h t] with n v
 obtain ⟨M,w,_⟩:=v; exact ⟨_,w⟩

-- Paired with real electrode `purePrice`. All six use respective y ≠0
-- which need not be real; at the conjugate body star must conjugate it.
-- Thus our calibrated insertion `Medal.bright` carries this scalar
-- removed, our repriced insertion can put it back to retain the literally
-- same front normalization if desired.
variable (P) in
def electro (M:P.Menagerie) (Z:𝔏):ℂ:=(M Z).y * (purePrice Z:ℂ)
lemma electro_alive (M:P.Menagerie)(Z:𝔏):P.electro M Z ≠0:=mul_ne_zero (M Z).nonzero (by exact_mod_cast (purePrice_p Z).ne')
lemma electro_front (M:P.Menagerie)(Z:𝔏):P.electro M Z • (M Z).bright.F=P.frontMat Z (M Z).n:=by
 let y:=(M Z).y; let u:ℂ:=(purePrice Z:ℂ)
 have v:y*u*(y⁻¹*u⁻¹)=1:=by rw [mul_comm y⁻¹,←mul_inv_rev y u]; exact mul_inv_cancel₀ (electro_alive M Z)
 change (y*u) • y⁻¹ • u⁻¹ • _ = _
 rw [smul_smul y⁻¹,smul_smul,v,one_smul,frontMat]
lemma Medal.also {Z:𝔏}(M:P.Medal Z):∃r:P.Reel j Z,r.n=M.n:=by
 obtain ⟨d,a,c,t⟩:=Taste.neum P M.worth (P.defaultBay ..) M.nonzero j
 exact ⟨⟨_,d,a,c,M.gap,t⟩,rfl⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
