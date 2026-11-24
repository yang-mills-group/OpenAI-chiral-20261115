import SatinThinBeacon

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- The HOT lens estimate is affordable even *at* all these final hills. -/
open Fief
variable (C:ℝ)(R:Patch)(v:1≤ C)
local notation "q"=>allotΨ R.L
local notation "b"=>radiusB
local notation "ϑ"=>(1/256:ℝ)
private lemma size_exp : sizeK R.L 6 (fun x:ℝ=> Real.exp (-(1/256:ℝ)*(radiusB x:ℝ))):=by
 let k:= (1/256:ℝ)/3; have he:0<k:=by unfold k; norm_num
 apply ((sizeK.tip R.L k he).square 3).cost_d; filter_upwards with x; rw [abs_of_pos (Real.exp_pos _)]
 refine le_trans ?_ (le_abs_self _); unfold tipPay; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; push_cast; have ht:(↑(radiusB x/60):ℝ) ≤ (radiusB x:ℝ):=by exact_mod_cast (Nat.div_le_self (radiusB x) 60)
 unfold k; linarith
include v
lemma computed_rc:∀ᶠ x:ℝ in atTop,Nice_B (radiusB x) 2 (C*(allotΨ R.L x)⁻¹) (1/8):=by
 let G(x:ℝ):= Real.exp (-ϑ*b x)
 have h:sizeK R.L (4+1) (fun x:ℝ=> (2*C)^2*G x):=((size_exp R).scale ((2*C)^2)).low (by omega)
 have hx:0<C:=zero_lt_one.trans_le v
 obtain ⟨u,w⟩:= eventually_atTop.mp (tear_r (15^4:ℝ) ϑ 8 (by norm_num))
 let p':= Work.E01.radiusB_tendsto
 have hg:= (pill_R _ (k:=4) (d:=1) (by norm_num) h) -- tune order
 filter_upwards [hg,p'.eventually (tear_r (3^4:ℝ) ϑ 12 (by norm_num)),p'.eventually_ge_atTop u,p'.eventually_ge_atTop 1,(pal_U R.L 0 le_rfl)] with x g vK e hz hi m pm
 let B:= b x; have hs:0<q x:=by simpa using hi.1
 let P:= C*(q x)⁻¹; let K:= (2*P)^2; have hK:0 ≤ K:=sq_nonneg _
 have hk:K ≤ Real.exp (ϑ*B):=by
    have hl:G x=(Real.exp (ϑ*B))⁻¹:=by unfold G; rw [neg_mul,Real.exp_neg]
    change _<1*Scales.g SU.group R.L x^4 at g
    have H: (2*C)^2/ Real.exp (ϑ*B) ≤ (q x)^2:=by
       rw [div_eq_mul_inv,←hl]; refine g.le.trans_eq ?_; unfold allotΨ; ring
    unfold K P; rw [←div_eq_mul_inv,←mul_div_assoc, div_pow, div_le_iff₀ (pow_pos hs 2)] -- tune mul_div_assoc orientation
    exact (div_le_iff₀ (Real.exp_pos _)).mp H |>.trans_eq (mul_comm ..)
 let k:=chip_B B m / cape_B B; let T:=pearl (chip_B B m+B); let W:= pearl (cape_B B); have hh:rentP P B m 2=T*K*((W:ℝ)*K)^k:=by
    change (T:ℝ)*(W:ℝ)^k*(2*P)^((k+1)*2)=_; rw [Nat.mul_comm (k+1) 2,pow_mul]; change (T:ℝ)*(W:ℝ)^k*K^(k+1)=_; rw [pow_succ,mul_pow]; ring
 have hp:0<B:=hz
 have ha: (T:ℝ)*K ≤ Real.exp (2*ϑ*m):=by
    have hv':(T:ℝ)≤ (15:ℝ)^4*(m:ℝ)^8:=by exact_mod_cast pearl_m B m hp pm
    rw [show 2*ϑ*(m:ℝ)=ϑ*m+ϑ*m by ring,Real.exp_add]; exact mul_le_mul (hv'.trans (w m (le_trans e pm))) (hk.trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr pm) (by norm_num)))) hK (Real.exp_pos _).le
 have hv: (W:ℝ)*K≤Real.exp (2*ϑ*B):=by
    have h:(W:ℝ) ≤ (3:ℝ)^4*(B:ℝ)^12:=by exact_mod_cast pearl_y B hp
    rw [show 2*ϑ*(B:ℝ)=ϑ*B+ϑ*B by ring,Real.exp_add]; exact mul_le_mul (h.trans vK) hk hK (Real.exp_pos _).le
 have H:= mul_le_mul ha (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hK) hv k) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) _) (Real.exp_pos _).le
 refine hh.trans_le (H.trans ?_); have p: (k:ℝ)* (B:ℝ)≤ 6*(m:ℝ):=by exact_mod_cast sev_B B m hp
 rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_monotone; linarith only [p,Nat.cast_nonneg (α:=ℝ) m]
end YM.CF.QuadClock
