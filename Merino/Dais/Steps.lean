import YM.SU5.Exchange.Force.Band
import Merino.Corolla.Seasons
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
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


open Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
open Pitching Pitching.Focus Fief
variable (R:Patch) (f:ℕ) (x:ℝ)
open Corolla


private lemma paidW {W:ℝ→ℝ} (h:sizeK R.L 3 W):
  ∀ᶠ x in atTop, |W x| ≤ cur R.L f x:=by
 obtain ⟨D,g⟩:=h
 have ht:sizeK R.L 1 (fun x=> W x / pinpr R.L x):=by
    refine ⟨D,?_⟩
    filter_upwards [g,draft_π R.L] with x h v
    rw [abs_div,abs_of_pos (pow_pos v.2.1 2),pow_one]
    exact (div_le_iff₀ (pow_pos v.2.1 2)).mpr (h.trans_eq (by ring))
 have e:=(Chill_v.coin ht f).abs
 rw [abs_zero] at e
 filter_upwards [e.eventually (ge_mem_nhds one_pos),draft_π R.L] with x w b
 let y:=BPress.lscale x; let t:=pinpr R.L x
 have hp:0<y^f:=pow_pos (zero_lt_one.trans_le (BPress.lscale_one x)) _
 have ht:0<t:=pow_pos b.2.1 _
 change |y^f*(W x/t)|≤1 at w
 change |W x| ≤ t/y^f
 rw [←mul_div_assoc,abs_div,abs_mul,abs_of_pos ht,abs_of_pos hp,div_le_iff₀ ht,one_mul] at w
 exact (le_div_iff₀ hp).mpr (by rwa [mul_comm])

private lemma falls {y:ℝ}(g:1≤x)(k:x≤y)(p:0<Scales.y SU.group R.L x):
   0<cur R.L f y ∧ cur R.L f y≤cur R.L f x ∧ cur R.L f x≤pinpr R.L x:=by
 have b:Scales.y SU.group R.L x≤Scales.y SU.group R.L y:=add_le_add_left k _
 have h:radiusB x ≤ radiusB y:=Nat.ceil_mono
   (pow_le_pow_left₀ (Real.log_nonneg g) (Real.log_le_log (zero_lt_one.trans_le g) k) _)
 have l:BPress.lscale x ≤ BPress.lscale y:=add_le_add_right (Nat.cast_le.mpr h) _
 have v:=zero_lt_one.trans_le (BPress.lscale_one x)
 have d:0<pinpr R.L y:=pow_pos (gauge _ _ (p.trans_le b)) _
 have e:pinpr R.L y≤pinpr R.L x:=pow_le_pow_left₀ (gauge _ _ (p.trans_le b)).le
   (inv_anti₀ (Real.sqrt_pos.2 p) (Real.sqrt_le_sqrt b)) _
 refine ⟨div_pos d (pow_pos (v.trans_le l) _),?_,div_le_self (d.le.trans e) (one_le_pow₀ (BPress.lscale_one x))⟩
 exact le_trans (div_le_div_of_nonneg_left d.le (pow_pos v _) (pow_le_pow_left₀ v.le l _))
        (div_le_div_of_nonneg_right e (pow_pos v _).le)


variable (u:ℕ)(Γϕ:ℝ)
local notation "λ'" => colorsPhi
local notation "Q" => cur
local notation "dX" => Vale.billX R.L

structure StairBills (W:ℝ) : Prop where
 height: Capsule R x
 step: 0<Q R.L f (x+dX) ∧ Q R.L f (x+dX) ≤ Q R.L f x
 request: Q R.L f (x+dX) ≤ λ' R.L Γϕ x
 seams: wovenV (Q R.L f (x+dX)) u ≤ λ' R.L Γϕ x
 pastel: |W| ≤ Q R.L f x
 pitch: ∀ (z:ℂ)(h:ℝ), let v:=Q R.L f (x+dX)
                        let t:= (↑R.L.val:ℝ)⁻¹^5*v+W
                        κprobe mintR R.L h v W z 0=t ∧
                        κprobe naxR R.L h v W z 0=t∧
                        κprobe nagR R.L h v W z 0=t∧
                        |t| ≤ 2*Q R.L f x


variable {K:Teller SU.group}{Lr:ChartRatio SU.group}
lemma stairBills (V:Grace K R Lr) (T:ℝ→ℝ)(v:sizeK R.L 3 T):
  ∀ᶠ x in atTop, StairBills R f x u Γϕ (T x):=by
 have s:0 < dX := mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1<R.L.val by have he:=V.tallX; omega)))
 have c:Chill_v (fun _:ℝ=>0):=fun n=>by simp
 let a:ℝ:=2*↑u+1
 filter_upwards [(year SU.group R.L).eventually_gt_atTop 0,paidW R f v,colors_more R Γϕ a,prolong (V:=V) c (Eventually.of_forall fun _=>le_rfl),eventually_ge_atTop (1:ℝ)] with y g h b r z
 obtain ⟨j,k,l⟩:= falls R f y z (le_add_of_nonneg_right s.le) g
 have ha:1≤a:=by unfold a;linarith only [Nat.cast_nonneg (α:=ℝ) u]
 have hp:1≤(↑R.L.val:ℝ):=by exact_mod_cast R.L.property
 have hq:a*Q R.L f (y+dX) ≤ λ' R.L Γϕ y:=(mul_le_mul_of_nonneg_left (k.trans l) (zero_le_one.trans ha)).trans b
 refine ⟨r,⟨j,k⟩,(le_mul_of_one_le_left j.le ha).trans hq,?_,h,?_⟩
 · unfold a at hq; unfold wovenV; linarith only [hq]
 intro e h'; dsimp only; refine ⟨?_,?_,?_,?_⟩
 · simp [κprobe,mintR]
 · simp [κprobe,naxR]
 · simp [κprobe,nagR,naxR]
 let m:ℝ:=(↑R.L.val:ℝ)⁻¹
 have hm:m ≤1:=inv_le_one_of_one_le₀ hp
 have hn: m^5≤1:=pow_le_one₀ (by unfold m; positivity) hm
 apply le_trans (abs_add_le ..)
 change |m^5*Q R.L f (y+Vale.billX R.L)| + _ ≤ _
 rw [abs_of_nonneg (mul_nonneg (show 0 ≤ m^5 from by unfold m; positivity) j.le)]
 exact (add_le_add ((mul_le_of_le_one_left j.le hn).trans k) h).trans_eq (two_mul _).symm

-- shift any N eventually criterion forward
lemma later {P:ℕ→Prop} (h:∀ᶠ s in atTop,P s):∀ᶠ s in atTop,P (s+1):=
  (show Tendsto (fun s:ℕ=>s+1) atTop atTop from
    tendsto_atTop.2 fun t=> (eventually_ge_atTop t).mono fun _ hs=>hs.trans (Nat.le_succ _)).eventually h
end YM.CF.Merino.Dais
