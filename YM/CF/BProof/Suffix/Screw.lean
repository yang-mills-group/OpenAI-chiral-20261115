import YM.CF.BProof.Epoch.Use
import YM.CF.Tar.Silt
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
-- generic shooting proof. reuse rank guesses also in true family (dummy rank guesses).
open Episode
variable {a b n d k:ℕ}
variable (A B:ℕ→ℝ)
def ante (n d:ℕ)(A B:ℕ→ℝ)(g:ℝ)(z:StarPS n)(j:ℕ):ℝ:= B j+ (g+ ∑ i∈Finset.Ico d j, guess_Q n A z i)
structure Air (n a:ℕ) where
 W: ℕ→ℝ
 B: ℕ→ℝ
 γ: ℝ
 z: ℕ→ℝ
 hp:∀ i,0< W i
 hv:∀ i,0< z i
namespace Air
variable (P:Air n a)
abbrev pn (j):=P.hv j|>.le -- inferred def.C mortal
abbrev aim:=ante n a P.W P.B P.γ
abbrev θ(i):= θ_guess (l0:=n) P.z P.pn i
lemma aim_s (i:ℕ)(p:a ≤ i)(z): P.aim z (i+1)=P.aim z i+(P.B (i+1)- P.B i)+ guess_Q n P.W z i:=by
 unfold aim ante; rw [sum_Ico_succ_top p]; ring
lemma aim_c(i:ℕ):Continuous (fun z=> P.aim z i):=continuous_const.add (continuous_const.add (continuous_finsetSum _ (fun k _=>real_k n _ k)))
-- reserve terms not outside range.<n
lemma deposit (i)(p:a ≤  i)(v:ℝ)(z)(u:∀ j,a ≤ j→j< i→P.W j≤v): |P.aim z i-P.B i-P.γ|≤ (i-a:ℕ)*v:=by
 unfold aim ante; rw [show ∀ t:ℝ,P.B i+(P.γ+t)-P.B i-P.γ=t from fun v=>by abel]; have h:= (Finset.abs_sum_le_sum_abs (fun j=>guess_Q _ P.W z j) (Finset.Ico a i)); refine h.trans ((sum_le_sum (g:=fun _=>v) fun i k=>(credits_q _ P.W (fun i=>(P.hp i).le) z _).trans (u i (mem_Ico.mp k).1 (mem_Ico.mp k).2)).trans_eq ?_); simp
lemma aim_z(z): P.aim z a=P.B a+P.γ:=by simp [aim,ante]
-- fix tau.S. quant exports Glue.Note rotor fake allowed as K.point.W.
lemma shoot(F:∀ j:ℕ, StarPS n → ΘS (P.z j))(f:ℕ→StarPS n→ℝ)(p:∀ j,Continuous (F j))(hp:∀ j,Continuous (f j))(h:∀ j z,|f j z|≤ P.W j) : ∃ z:StarPS n,∀ j:ℕ,j<n→P.θ j z= F j z ∧ f j z=guess_Q n P.W z j :=by
 let L(i:Fin n)(v:StarPS n):= (f i v / P.W i,(P.z i)⁻¹ • (F i v).val)
 have hx(v:StarPS n):‖(fun i=>L i v)‖≤1:=by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>?_ ; let a:= P.z i; let b:= (F i v).val; have ha:0<a:= P.hv i; have hv:‖b‖≤a:= (F i v).property; change max (‖f i v / P.W i‖) (‖a⁻¹ • b‖) ≤ 1
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs,abs_div,abs_of_pos (P.hp i),div_le_one (P.hp i)]; exact h _ _
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (inv_mul_cancel₀ (ne_of_gt ha))
 let G(z:StarPS n):StarPS n:=⟨fun i=>L i z,hx z⟩
 have hg:Continuous G:= Continuous.subtype_mk (continuous_pi (fun i=> ((hp (i:Fin n)).div_const _).prodMk ((continuous_subtype_val.comp (p i)).const_smul (P.z i)⁻¹))) _
 obtain ⟨z,hK⟩:= Moen.Space.bow zero_lt_one G hg
 have hw(i:Fin n): L i z=z.val i:=congrFun (congrArg Subtype.val hK) i
 refine ⟨z,fun i h=>?_⟩; let j:Fin n:=⟨i,h⟩; unfold θ θ_guess guess_Q; rw [dif_pos h,dif_pos h]; have hα: P.z i≠0:= (P.hv i).ne'
 constructor
 · apply Subtype.ext; change P.z i • (z.val j).2= (F i z).val; rw [←hw j]; exact smul_inv_smul₀ hα ((F i z).val)
 rw [←hw j]; change _= P.W i *(f i z/ P.W i); rw [mul_comm,div_mul_cancel₀ _ (P.hp i).ne']
end Air
end Cupboard
end YM.CF.Py
