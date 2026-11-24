import YM.CF.Feu.Moment
import YM.CF.Muse.Hear
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Haro Feu Feu.Corset Nor
open Levier Haro Feu Feu.Corset Nor
open Jade
-- uniforms. purchase printers.Heights train
abbrev gownI (a C:ℝ)(L:Side)(B:ℕ):ℝ:= (((B+B+1)^4 :ℕ)* (L.val^4:ℕ)*(Fintype.card Axis:ℕ))* C
abbrev goldV (a C:ℝ)(R:Patch)(x:ℝ)(k:ℕ):ℝ:= Real.exp (-a*(luceL R k x)^2)*gownI a C R.L (radiusB x)
lemma morphV(a L:ℝ)(p: S.patch.L=R.L) (k:ℕ) : goldV a L R x k=tentX a (luceL R k x) L S (radiusB x):=by unfold Jade.tentX goldV gownI; rw [p] -- tune
lemma gold_p (a C:ℝ)(h:0<a)(z:0 ≤ C)(m:ℕ):∃ N:ℕ,∀ i:ℕ,N≤ i→ sizeK R.L m fun x=> goldV a C R x i:=by
 obtain ⟨N,H⟩:=Lilt.sting (R:=R) (Lento.sun 1) a h m; have hp:BoreP (fun x=>gownI a C R.L (radiusB x)):=by
    unfold gownI; push_cast; have he:BoreP (fun x=>(radiusB x:ℝ)+radiusB x+1):= (BoreP.radius_c.join BoreP.radius_c).join (BoreP.still 1)
    exact (((he.self _).grip (BoreP.still _)).grip (BoreP.still _)).grip (BoreP.still _)
 refine ⟨N,fun i t=>(by have he:=H i t; unfold goldV; simp_rw [one_mul] at he; exact he.tint (hp.creditK _))⟩ -- tune
lemma slice_b (s d A:ℝ)(k n l:ℕ) : ∃ D:ℝ,1≤D ∧ ∃ N:ℕ,∀ R:Patch,N≤R.L.val→let P:= sliceK R.L (l+90) (k+2) s A ((4:ℝ)^n*d); 0 ≤ P∧P ≤ 1∧P^4 ≤D*gritY R.L.val∧∀ E:Stake.Isle,∀ᶠ H:ℝ in atTop,Coin_ ((4:ℝ)^n*(d*H)) (population*(A*followV [] R.L)) (population*E.r1) s (l+90) (k+2) ≤ P*H:=by
 obtain ⟨C,h,hv⟩:=shareK (l+90) (k+2) s A ((4:ℝ)^n*d); obtain ⟨N,p⟩:=exists_nat_gt C; refine ⟨C,h,N,fun P q=>?_⟩
 intro v; let A':ℝ:= P.L.val
 have ha:0<A':=by unfold A'; positivity
 have hg:1≤ A':=by unfold A'; exact Nat.one_le_cast.mpr P.L.property
 have he: 0≤v:=mul_nonneg (by positivity) (Vpos ..).le
 have hx':v^4=C*A'⁻¹^6:=hv P
 have hx:C ≤ A':= (p.trans_le (Nat.cast_le.mpr q)).le
 have hk:A'⁻¹ ≤ 1:= inv_le_one_of_one_le₀ hg
 have hu:v≤1:= by
    by_contra! e
    have hh:v^4≤1:=by rw [hx', inv_pow,← div_eq_mul_inv]; exact (div_le_one (by positivity)).mpr (hx.trans (le_self_pow₀ hg (by omega)))
    have hz:1^4 < v^4:=pow_lt_pow_left₀ e (by positivity) (by omega); norm_num at hz; exact hz.not_ge hh
 refine ⟨he,hu,(hx'.trans_le ?_),fun i=>?_⟩
 · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (inv_pos.mpr ha).le hk (by omega:(5:ℕ)≤6)) (zero_le_one.trans h)
 have h:= (healthY s ((4:ℝ)^n*d) A (l+90) (k+2) P.L i).2; simp_rw [mul_assoc ((4:ℝ)^n) d] at h -- also slice macro not rewriting inside?
 exact h
end YM.CF.Oath
