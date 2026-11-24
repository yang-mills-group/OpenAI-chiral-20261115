import YM.SU5.FiniteGaugeData.Steam.Kettle
import YM.SU5.FiniteGaugeData.LocalLimit.Physical
import YM.CF.Continuum.Ramp
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
/-! # AwayFromTheBelt
Scale-independent (tall-s) budgets at Actual branch on normalized reads. Specialization
of Epoch bounds in Continuum Ramp etc. But UNBOUNDED physical sizes on this same
hierarchy. Margin paid remains S-local. -/
open LocalLimit Window Jade.Earn Period
namespace Steam
abbrev Fare (x:ℝ) (n:Side)(k:ℝ):= sites n*(3*strengthLog (soaked x)+k)
lemma port_eq (x k:ℝ){s:Side}(Q:GramM s) : budgetCharge Q (soaked x) k=Fare x s k:= by unfold budgetCharge Fare massMeter sites sizes; rw [Nat.cast_pow]
variable {k wK v delay :ℝ}{C R0 DC :ℝ→ℝ}{P:Prescription R B}{N0 M:ℕ}
include V
-- module dependent estimate
lemma horizons (x:ℝ): Tendsto (hat R.L x) atTop atTop := by
 have he: 0 < billX R.L := mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1<R.L.val by have he:=V.tallX; omega)))
 unfold hat; refine tendsto_atTop.2 (fun b=>?_); filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ((b-x)/(billX R.L))] with i t; have hx' : b-x ≤ (i:ℝ)*billX R.L:=(div_le_iff₀ he).mp t; linarith
open Pitching Focus
local notation "C₀" m:max i:max=> (cell m B R.L i)
local notation "X"=> hat R.L x
local notation "Ω₀"=> Scales.y SU.group R.L
variable {kT:Kettle k J P N0 h q}
variable (H:Service V U W J q h DC C R0 P N0 delay)
include H kT
open Branch in
lemma cosmos : ∀ᶠ i : ℕ in atTop, ∀ {M:ℕ}{m:Side} (A:Branch W m M x N0),∀ {b}, i<M → Bon J q h DC delay A → RealQ A b → Earn.pathFees (More (cell m B R.L i)) (More (cell m B R.L (i+1))) (Scales.y SU.group R.L (hat R.L x i)) k ≤ (A.offset P b i).re-(A.offset P b (i+1)).re:= by
 filter_upwards [(horizons (V:=V) x).eventually kT] with i t
 intro k m A b e B' r
 rw [offset.eq_1 P A b i,dif_pos e]; exact t _ _ (A.toSpine.address i) _ _ (B'.request _ e) _ _ _ (hat_step i ▸ (B'.beta_ok H r _ e).2) (B'.flow (B'.charged H r _ e))
variable (wP :0≤ k) (t:1 ≤ x) (p0:0 ≤ v)
omit H V kT
private lemma same_fare (n:Side): roomSite (More n) = sites n:=by unfold Earn.roomSite sites; rw [site_card,Nat.cast_pow]
include V wP t
private lemma ascent_fee (i:ℕ)(z:ℝ) (hp:0≤z):
  Fare (X (i+1)) (cell m B R.L (i+1)) (-(2*k+z/2)) ≤ Fare (X i) (cell m B R.L i) (-(2*k+z)) + pathFees (More (cell m B R.L i)) (More (cell m B R.L (i+1))) (Ω₀ (X i)) k :=by
 have he:1 ≤ X i:= t.trans (Vale.crown ..); have ha:= show X i ≤ X (i+1) from hat_mono (by omega)
 let U:=soaked (X (i+1)); let P:=soaked (X i); have hU:0<U:= (amplifier _ (zero_lt_one.trans_le (he.trans ha))).2.2.1; have hu:U≤ P:= inv_anti₀ (Real.sqrt_pos.mpr (zero_lt_one.trans_le he)) (Real.sqrt_le_sqrt ha)
 have hs:strengthLog U ≤ strengthLog P:= mul_le_mul_of_nonneg_left (Real.log_le_log hU hu) (Nat.cast_nonneg _)
 let C0:= sites (C₀ m i); let C1:=sites (C₀ m (i+1)); have ht₀:0≤ C0:=zero_le_one.trans (sites_pos _); have hp₁:2*C0≤ C1:=by
    have hb:= full_a V i B m; rw [Period.same_room,Period.same_room,same_fare,same_fare] at hb; exact hb
 unfold pathFees Fare; rw [same_fare,same_fare,heir_s V]
 change C1*(3*strengthLog U + - _) ≤ C0*(3*strengthLog P+ - _)+(3*(C1-C0)*strengthLog U-k*C1)
 nlinarith only [mul_le_mul_of_nonneg_right hs ht₀,mul_le_mul_of_nonneg_right hp₁ wP, mul_le_mul_of_nonneg_right hp₁ hp]
include H kT p0
lemma away : ∀ᶠ j:ℕ in atTop,∀ (m:Side){T:Month x 1 6 2 N0 V W}{f ρ:ℕ→ℝ}{S:Cape m B R.L}{ht:T.q ≤ m.val}{l:ℕ} (A:Parcel J q h DC C R0 T ht S ρ f l), FromShot P delay A → Real.exp (-v * sites (cell m B R.L 0))≤ ‖compensated U (A.gram 0) (S 0)‖ → j ≤ l → Real.exp (Fare (X j) (cell m B R.L j) (-(2*k+1))) ≤ ‖compensated U (A.gram j) (S j)‖ := by
 obtain ⟨a,he⟩:= eventually_atTop.mp (cosmos (x:=x) H (kT:=kT))
 let q':= LocalLimit.expense C R x v a
 let γ:= 3*strengthLog (soaked (X a))
 let z:= |q'+γ|; let f'(j:ℕ):= (1/2:ℝ)^(j-a)*z; have hx(j):0≤ f' j:= by unfold f' z; positivity
 have ht': Tendsto f' atTop (𝓝 0):=by
    have hz:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ)≤1/2 by norm_num) (show (1:ℝ)/2<1 by norm_num)).comp (tendsto_sub_atTop_nat a)).mul_const z; rwa [zero_mul] at hz
 filter_upwards [eventually_ge_atTop a,ht'.eventually (ge_mem_nhds zero_lt_one)] with j p' vT; intro m T f ρ S ht l A pA l' e'
 let K(i):= Fare (X i) (C₀ m i) (-(2*k+f' i))
 let n(i):= ‖compensated U (A.gram i) (S i)‖
 have hu: Real.exp (K j) ≤ n j:= by
    clear vT
    induction j,p' using Nat.le_induction with
    | base =>
       apply le_trans (b:=Real.exp (-q'*sites (C₀ m a))) ?_ (level_secured ht A v p0 l' a e'); apply Real.exp_monotone; have hh:= le_abs_self (q'+γ); have hK:f' a=z:=by simp [f']
       have hξ:= show γ-(2*k+f' a)≤ -q' by rw [hK]; linarith only [hh,wP]
       unfold K Fare; change sites (C₀ m a)*(γ+-_) ≤_; rw [mul_comm (-q')]; exact mul_le_mul_of_nonneg_left hξ (zero_le_one.trans (sites_pos _))
    | succ i hv IH =>
       have b' := IH (by omega); have hk : f' (i+1)= f' i/2:=by unfold f'; rw [show i+1-a=i-a+1 from by omega,pow_succ]; ring
       let E:= pathFees (More (C₀ m i)) (More (C₀ m (i+1))) (Ω₀ (X i)) k; have pF: K (i+1)≤ K i+E:=by unfold K; rw [hk]; exact ascent_fee (m:=m) (V:=V) wP t i (f' i) (hx _)
       obtain ⟨x₀,α,W,D⟩:=pA.issued -- check FromShot fields
       let u:= A.gram i; let u':= A.gram (i+1)
       have hs:E ≤ u.v.re-u'.v.re:= by unfold u u'; rw [W]; exact he i hv _ e' pA.paid α.toRealQ -- tune
       have hA : partitionZ u U (S i)=partitionZ u' U (S (i+1)):= (A.balance i (by omega)).trans (A.balance (i+1) e').symm
       unfold n compensated at b' ⊢; rw [norm_mul,Complex.norm_exp,Complex.neg_re] at b' ⊢; rw [←show partitionZ _ _ _=_ from hA]; apply le_trans (Real.exp_monotone pF); rw [Real.exp_add,mul_comm (Real.exp _) (Real.exp E)]; refine (mul_le_mul_of_nonneg_left b' (Real.exp_pos _).le).trans ?_
       rw [←mul_assoc,←Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by change E+(-u.v.re) ≤ -u'.v.re; linarith only [hs])) (norm_nonneg _)
 apply hu.trans'; refine Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans (sites_pos _))); gcongr -- vT
end Steam
end YM.CF.Py.Rate
