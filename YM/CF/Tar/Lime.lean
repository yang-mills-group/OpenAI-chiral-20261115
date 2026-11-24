import YM.CF.Tar.Duty
import YM.CF.Reed.Trio
import YM.CF.Ridge.Trio
import YM.CF.Ridge.Ply
import YM.CF.Paxos.Heron
import YM.CF.Tar.Run
import YM.CF.Paxos.Luz
import YM.CF.Bloom.Kale
set_option autoImplicit false
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
open Oise
abbrev nu_B(L:Side):ℝ:=ν_PS L/2
local notation "Hκ"=> (hat R.L x)
local notation "ζK"=> (fun v:ℕ=> hat R.L x v)
abbrev buoy(t:ℕ):= t^4
abbrev post_H(t:ℕ):= buoy t+t
abbrev trunkY(t B:ℕ):=post_H t+1+B
-- fixed x proof path estimates
lemma fast_β(L:Side)(x:ℝ)(u i:ℕ)(p:u ≤ i): hat L x u ≤ hat L x i:= add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr p) (pitch L)) x -- add_le_add_right t yields x+…
include V
lemma cap_v (x:ℝ)(t:ℕ) : Tendsto (fun u:ℕ=>hat R.L x (buoy u)) atTop atTop:=by -- need bill positive V. V type implicit argument.Include
 have hp:0< billX R.L:=by have ht:= billx_T V; unfold ν_PS at ht; linarith
 exact tendsto_const_nhds.add_atTop ((tendsto_natCast_atTop_atTop.comp ((tendsto_pow_atTop (by omega : (4:ℕ)≠0)) : Tendsto (fun x:ℕ=>x^4) atTop atTop)).atTop_mul_const hp)
lemma glow_y(t:ℕ)(F:ℝ→ℝ)(hf:sizeK R.L 2 F): ∀ᶠ k:ℕ in atTop,
         ((trunkY k t-buoy k:ℕ):ℝ)*grant_B R.L (hat R.L x (trunkY k t)) ≤ (buoy k:ℝ)* nu_B R.L ∧ (1/2:ℝ)^k * F (hat R.L x (post_H k)) ≤ dleaf R.L (hat R.L x (buoy k)):=by
 let X(k:ℕ):= Hκ (buoy k); let Y(k:ℕ):= Hκ (trunkY k t); let M(k:ℕ):= Hκ (post_H k); let L':=R.L
 have hp:0<nu_B R.L:=half_pos (billx_T V); have hb:0 ≤ Vale.billX R.L:=pitch ..
 have hc(k:ℕ):X k ≤ M k:=fast_β _ _ _ _ (by unfold post_H; omega); have hu(k):M k ≤ Y k:=fast_β _ _ _ _ (by unfold trunkY; omega); have h:=cap_v V x 0
 have hm:Tendsto M atTop atTop:=tendsto_atTop_mono hc h
 let G:=Scales.y SU.group R.L; let A:= Vale.billX R.L
 let C:=|G x|+A*(3+t:ℝ)+2; have hC:1≤ C:=by unfold C A; have hp:0 ≤ Vale.billX R.L*(3+t:ℝ):= mul_nonneg hb (by positivity); linarith [abs_nonneg (G x)]
 have hx(k:ℕ)(p:1 ≤ k): G (Y k) ≤ C*(k:ℝ)^4:=by
    have hp: k ≤ k^4:=by nth_rw 1 [←pow_one k]; exact pow_le_pow_right₀ p (by decide)
    let u:ℝ:=(k:ℝ)^4; have hr: (k:ℝ)≤ u:=by unfold u; exact_mod_cast hp
    have hv:1≤u:=le_trans (show 1 ≤ (k:ℝ) from Nat.one_le_cast.mpr p) hr
    have he: G (Y k) ≤ |G x| *u + ((3+t:ℝ)*u)*A:=by
       have hh: G (Y k)=G x+(trunkY k t:ℝ)*A:=by unfold Y G Scales.y hat betaF A; ring
       rw [hh]; apply add_le_add ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hv)); apply mul_le_mul_of_nonneg_right _ hb; unfold trunkY post_H buoy; push_cast; change u+_+1+(t:ℝ)≤_; nlinarith
    unfold C; change _≤ _*u; linarith only [he,hv]
 let Bψ(x):=grant_B R.L x
 have hp':0 < nu_B R.L:=hp
 obtain ⟨i,hK⟩:= exists_nat_gt (((2+t:ℝ)* C)/(nu_B R.L))
 have hv:Tendsto (fun k:ℕ=> C*((k:ℝ)^4 * (1/2:ℝ)^k)) atTop (𝓝 0):=by simpa only [mul_zero] using (tendsto_pow_const_mul_const_pow_of_lt_one 4 (by norm_num:(0:ℝ)≤ 1/2) (by norm_num:(1/2:ℝ)<1)).const_mul C
 filter_upwards [eventually_ge_atTop (1:ℕ),eventually_ge_atTop i,hm.eventually ((hf.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds zero_lt_one)), hv.eventually (ge_mem_nhds zero_lt_one),h.eventually (show ∀ᶠ i:ℝ in atTop,Scales.g SU.group R.L i ≤ temp i from (by filter_upwards [(clove_p R).spine_a.eventually (ge_mem_nhds zero_lt_one),eventually_gt_atTop (0:ℝ)] with x p u; simpa only [div_le_one (Work.E09.temp_pos u)] using p)), (Scales.year SU.group R.L|>.comp h).eventually_gt_atTop 0] with k g y' tB hv gB qB
 let z:ℝ:=k; let N:= X k; have ht:1 ≤ z:= Nat.one_le_cast.mpr g; have ht':0 ≤ z^4:=by unfold z; positivity
 have heN:0<G N:=qB
 have hM: G N ≤ G (Y k):= add_le_add_left ((hc k).trans (hu k)) _
 have hK': G (Y k) ≤ C*z^4:=hx _ g
 constructor
 · have ht'B: ((trunkY k t-buoy k:ℕ):ℝ) ≤ (2+t:ℝ)*z:=by unfold trunkY post_H; rw [Nat.cast_sub (by omega)]; push_cast; unfold z at *; nlinarith
   have hh: grant_B R.L (Y k) ≤ C*z^2:=by
      unfold grant_B; have hp:0<G (Y k):=heN.trans_le hM; apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩; rw [mul_pow]; calc
         _ ≤ C*z^4:=hK'
         _ ≤ C^2*(z^2)^2:=by rw [← pow_mul]; gcongr; exact le_self_pow₀ hC (by omega)
   have hj := (mul_le_mul ht'B hh (Real.sqrt_nonneg _) (show 0≤(2+t:ℝ)*z by positivity)); unfold buoy at *; push_cast; -- rewrite z. use explicit bound
   have hf:(2+t:ℝ)*C/(nu_B R.L) ≤ z:=hK.le.trans (Nat.cast_le.mpr y'); rw [div_le_iff₀ hp'] at hf; exact hj.trans ((le_of_eq (by ring : (2+t:ℝ)*z*(C*z^2)=(2+t:ℝ)* C*z^3)).trans (le_trans (mul_le_mul_of_nonneg_right hf (show 0≤ z^3 by positivity)) (le_of_eq (by unfold z; ring))))
 let u0:=(Scales.g SU.group R.L N); have htq:G N*u0^2=1:=Scales.yg2 SU.group R.L (x:=N) heN; have hg:0 ≤ u0:=(Scales.gauge SU.group R.L heN).le
 apply le_trans (mul_le_mul_of_nonneg_left tB (pow_nonneg (by norm_num) k))
 rw [mul_one]; apply le_trans (_ : (1/2:ℝ)^k ≤ u0^2) (show u0^2 ≤ u0*temp N from (by rw [sq]; exact mul_le_mul_of_nonneg_left gB hg))
 apply le_of_mul_le_mul_left _ heN; rw [htq]; exact (mul_le_mul_of_nonneg_right (hM.trans hK') (pow_nonneg (by norm_num) _)).trans ((mul_assoc C (z^4) _).trans_le hv)
end YM.CF.Py
