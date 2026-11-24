import YM.SU5.FiniteGaugeData.Steam.Basket
import YM.SU5.FiniteGaugeData.Drachma.Treasure
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
variable {k wK v delay :ℝ}{C R0 DC :ℝ→ℝ}{P:Prescription R B}{N0 M:ℕ}
open Pitching Focus
local notation "C₀" m:max i:max=> (cell m B R.L i)
local notation "X"=> hat R.L x
local notation "Ω₀"=> Scales.y SU.group R.L
variable {kT:KettleΨ J P N0 h q}
variable (H:Service V U W J q h DC C R0 P N0 delay)
include H kT
open Branch YM.SU5.FiniteGaugeData.Drachma.Tokens YM.SU5.FiniteGaugeData.Drachma.Tame CF.Parcel.Tanin
omit H kT
abbrev pressM(n:Side)(g:GramM n)(k:ℕ) (V:Grace K R L):= fameF V k n g.beta g.J.M
-- one-sided steady walk-temperature comparison, using $β move
lemma specwalk (hR:LocalRatio L)(r:ℝ)(p:0<r) (v:ℝ):∀ᶠ α:ℝ in atTop,∀ y z:ℝ, α/2 ≤ z→ 0<y→ y≤z+v→coinV L z≤ coinV L y + r:=by
 let c:ℝ:=Fintype.card SU.group.ColorIndex
 let ε:=r/(1+c); let D:= Real.exp ε; have hc:0≤c:=Nat.cast_nonneg _; have he: 0<ε:=by positivity
 have hD:1<D:=by have g:=Real.add_one_le_exp ε; change _<Real.exp ε; linarith only [g,he] -- tune
 filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (2*v/(D-1))] with x h1 h2
 intro y z h k l; have hz:0<z:= lt_of_lt_of_le (by positivity) h; have hy:Real.log y ≤ Real.log z+ε:=by
    -- direct via $y/z
    have ht:Real.log (y / z) ≤ Real.log D:= Real.log_le_log (div_pos k hz) (by apply (div_le_iff₀ hz).2; rw [div_le_iff₀ (sub_pos.mpr hD)] at h2; nlinarith only [mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hD.le), h2,l])
    rw [Real.log_div k.ne' hz.ne',Real.log_exp] at ht; linarith -- tune
 rw [pocketU hR hz,pocketU hR k]; have hp':(1+c)*ε=r:=by unfold ε; field_simp; -- tune
 nlinarith only [he,(mul_le_mul_of_nonneg_left hy hc),hp']
section
variable {l:ℕ}{T:Branch W m l x N0} {b:Bet l} {δ:ℝ} (B₀: Bon J q h DC delay T)
include H B₀
local notation "φ" i:max=> b.read i
lemma budget1 (r:RealQ T b)(i:ℕ)(e:i≤l): X i / 2 ≤ (φ i).re:= (matched_of_enters (B₀.clocks i) (B₀.beta_ok H r _ e).2).1
private lemma date_pos(r:RealQ T b)(i:ℕ)(e:i≤l): 0< (φ i).re:= (half_pos (zero_lt_one.trans_le (B₀.clocks i).grade)).trans_le (budget1 H B₀ r i e)
lemma moves_fame (e:Solved P T δ b) (i:ℕ)(p:i < l): (φ i).re ≤ (φ (i+1)).re + (K.top.drift-billX R.L + W.C.P + billX R.L /512):=by
 let y:=T.toSpine.address i; let z:=T.fee P i b; have hs : (T.active P b i).beta=(φ i).re:= B₀.paysStep H e i p
 let g:= (T.op P i).posted (φ (i+1)).re (T.chargeLevel P b (i+1)); change (φ (i+1)).re+(V.L.charge y.lag+y.fee)-g= _ at hs; have he:= (B₀.posts H).bound i p _ (B₀.area H e.toRealQ (i+1))
 have hu:g = z.re := by rw [←Complex.ofReal_re g, B₀.fee_eq H e.toRealQ i p] -- tune
 have h:=abs_le.mp ((Complex.abs_re_le_norm z).trans (he.trans (B₀.clocks i).slow))
 have hh: |V.L.charge y.lag+billX R.L|+1 ≤ K.top.drift:= V.L.bound _
 have hl: |y.fee|≤ W.C.P:= ((B₀.request i p).statv _ 0 0 0 (hat_step i ▸ matched_of_enters (B₀.clocks (i+1)) (b:= (φ (i+1)).re) (B₀.beta_ok H e.toRealQ _ p).2)).dose.fiscal
 linarith only [hl,h.1,hs,hh, hu,le_abs_self y.fee, le_abs_self (V.L.charge y.lag+billX R.L)]
omit B₀
include kT
lemma steamstep (K':LocalRatio L)(s:ℝ)(e:0<s): ∀ᶠ i:ℕ in atTop,∀{m:Side} {l:ℕ}{δ:ℝ} (A_:Branch W m l x N0) {b: Bet l}, i<l→ Bon J q h DC delay A_ → Solved P A_ δ b →
 pressM _ (A_.gram P b (i+1)) (l-(i+1)) V -s*sites (cell m B R.L (i+1)) ≤ pressM _ (A_.gram P b i) (l-i) V + ((A_.offset P b i).re-(A_.offset P b (i+1)).re) :=by
 let f:=s/6; let r:=K.top.drift-billX R.L + W.C.P + billX R.L/512; have hp : 0<f:=by positivity
 let U₀:= hat R.L x; have he:Tendsto (fun i=>U₀ (i+1)) atTop atTop:= (horizons (V:=V) x).comp (tendsto_add_atTop_nat 1)
 filter_upwards [he.eventually (specwalk K' f hp r), (horizons (V:=V) x).eventually (kT (s/2) (by positivity))] with i hS hK
 intro m l δ A_ b p P₀ v₀; let b1:= (b.read (i+1)).re; let b0:=(b.read i).re; let H':= P₀.beta_ok H v₀.toRealQ _ p; let A:= A_.toSpine.address i; have ht: rentD V A (s/2) b1 ≤ (A_.offset P b i).re-(A_.offset P b (i+1)).re:=by rw [offset.eq_1 P A_ b i,dif_pos p]; exact hK _ _ _ _ _ (P₀.request i p) _ _ _ (hat_step i ▸ H'.2) (P₀.flow (P₀.charged H v₀.toRealQ _ p)) -- tune
 let y:=C₀ m i; let z:=C₀ m (i+1); have hc: 0≤ sites y:=zero_le_one.trans (sites_pos _); have hh: sites y≤ sites z:=by rw [←ser_pocket,←ser_pocket]; exact Earn.builtLe (A.step V)
 have hy: coinV L b1 ≤ coinV L b0+f:= hS b0 b1 (budget1 H P₀ v₀.toRealQ _ p) (date_pos H P₀ v₀.toRealQ _ (by omega)) (moves_fame H P₀ v₀ _ p)
 let XQ(i):= A_.last.Q i; let F(a:ℝ):= fameF V (l-i) y a (XQ i).M; let G(a:ℝ):= fameF V (l-(i+1)) z a (XQ (i+1)).M
 change fameF V (l-1-i) _ b1 _ - fameF V (l-1-i+1) _ b1 _ - _ ≤ _ at ht; rw [show l-1-i=l-(i+1) by omega, show l-(i+1)+1=l-i by omega] at ht; change G b1-F b1-s/2*sites z ≤_ at ht
 have hv: F b1-F b0=3*sites y*(coinV L b1-coinV L b0):=by unfold F fameF angular; rw [ser_pocket]; ring
 change G b1-s*sites z ≤ F b0+_; unfold f at hy; nlinarith only [mul_le_mul_of_nonneg_left hy hc,ht,hv,mul_le_mul_of_nonneg_left hh e.le]
end

include H -- need? after end/section
lemma glueK (rho:LocalRatio L): ∃ V₀:ℝ,0≤V₀∧∀ {m l x} (T:Branch W m l x N0) (B₀:Bon J q h DC delay T){b}(r:RealQ T b) (i:ℕ), i≤ l → pressM _ (T.gram P b i) (l-i) V ≤ V₀*sites (cell m B R.L i):=by
 let G:=Real.log (min 1 V.W.parcel); let d:= dozer SU.group; let V0:=3*coinV L (1/2)-d/2*(4*G); refine ⟨|V0|,abs_nonneg _,?_⟩
 intro m l x T z b r i hi; let n:=cell m B R.L i; let θ:= (T.gram P b i); let μ:= l-i; let t:= θ.beta; have ht: 1/2 ≤ t:=(div_le_div_of_nonneg_right (z.clocks i).grade (by norm_num : (0:ℝ)≤2)).trans (budget1 H z r _ hi); have hl:0<t:= (by norm_num:(0:ℝ)<1/2).trans_le ht
 have he: coinV L t ≤ coinV L (1/2):=by rw [pocketU rho hl,pocketU rho (by norm_num)]; gcongr
 have hv:= YM.SU5.FiniteGaugeData.Drachma.capering (f:=More n) (V.L.roof μ|>.2.1 _) V.W.reserve; have hp:ser (More n)=sites n:=ser_pocket _; change ser (More n)*(4*G)≤ _ at hv; rw [hp] at hv
 let X':=photo_ψ K.j n θ.J.M; have hh:X' ≤ 0:=(heat_budget (P:=U) θ.J.M W.health (by have hR:=R.order_cut; have hy:= V.L.lobby; omega) (J.gran.trans (z.can.cape i).size)).1
 have hz: 0≤ sites n := zero_le_one.trans (sites_pos _); have hν:0≤d:=Nat.cast_nonneg _
 apply le_trans _ (mul_le_mul_of_nonneg_right (le_abs_self V0) hz); change (angular (More n) L _ t+ X')≤V0*sites n; unfold angular V0; rw [ser_pocket]; unfold d at *; nlinarith only [hh, mul_le_mul_of_nonneg_left hv hν, mul_le_mul_of_nonneg_left he hz]
include kT H
lemma horizonZ (rho:LocalRatio L) (s:ℝ)(hs:0<s) (h0:0≤v): ∀ᶠ j:ℕ in atTop,∀ (m:Side){T:Month x 1 6 2 N0 V W}{f ρ:ℕ→ℝ}{S:Cape m B R.L}{ht:T.q ≤ m.val}{l:ℕ} (A:Parcel J q h DC C R0 T ht S ρ f l), FromShot P delay A → Real.exp (-v * sites (cell m B R.L 0))≤ ‖compensated U (A.gram 0) (S 0)‖ → j ≤ l → Real.exp (pressM (C₀ m j) (A.gram j) (l-j) V -s * sites (C₀ m j)) ≤ ‖compensated U (A.gram j) (S j)‖:=by
 let r:=s/4; have hr:0<r:=by positivity
 obtain ⟨a,he⟩:= eventually_atTop.mp (steamstep (x:=x) (kT:=kT) H rho r hr)
 obtain ⟨V0,hV0,g⟩:=glueK H rho; let q':= LocalLimit.expense C R x v a
 let z:= |q'|+V0; let f'(j:ℕ):= (1/2:ℝ)^(j-a)*z; have hx(j):0≤ f' j:= by unfold f' z; positivity
 have ht': Tendsto f' atTop (𝓝 0):=by
    have hz:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ)≤1/2 by norm_num) (show (1:ℝ)/2<1 by norm_num)).comp (tendsto_sub_atTop_nat a)).mul_const z; rwa [zero_mul] at hz
 filter_upwards [eventually_ge_atTop a,ht'.eventually (ge_mem_nhds hr)] with j p' vT; intro m T f ρ S ht l A pA l' e'
 let K(i):= pressM (C₀ m i) (A.gram i) (l-i) V - (2*r+f' i)*sites (C₀ m i)
 let n(i):= ‖compensated U (A.gram i) (S i)‖; obtain ⟨x₀,α,W,D⟩:=pA.issued
 have hu: Real.exp (K j) ≤ n j:= by
    clear vT
    induction j,p' using Nat.le_induction with
    | base =>
       apply le_trans (b:=Real.exp (-q'*sites (C₀ m a))) ?_ (level_secured ht A v h0 l' a e'); apply Real.exp_monotone; have hp:f' a=z:=by simp [f']
       unfold K; rw [hp,W]; let u:=sites (C₀ m a); have hu:0≤u:= zero_le_one.trans (sites_pos _); have he:0≤2*r+|q'|-q':=by linarith only [hr,le_abs_self q']; -- tune
       unfold z; nlinarith only [g _ pA.paid α.toRealQ a e',mul_nonneg he hu]
    | succ i hv IH =>
       have b' := IH (by omega)
       have hk : f' (i+1)= f' i/2:=by unfold f'; rw [show i+1-a=i-a+1 from by omega,pow_succ]; ring
       let u:= A.gram i; let u':= A.gram (i+1); let E:= u.v.re-u'.v.re; have hU:0≤ sites (C₀ m (i+1)):=zero_le_one.trans (sites_pos _)
       have hp₁:2*sites (C₀ m i)≤ sites (C₀ m (i+1)):=by
          have hb:= full_a V i B m; rw [Period.same_room,Period.same_room] at hb; exact (by simpa only [show Earn.roomSite (More (C₀ m i))=sites (C₀ m i) from ser_pocket _,show Earn.roomSite (More (C₀ m (i+1)))=sites (C₀ m (i+1)) from ser_pocket _] using hb) -- tune
       have hZ:= he i hv _ e' pA.paid α
       have hpz: pressM (C₀ m (i+1)) u' (l-(i+1)) V- r*sites (C₀ m (i+1))≤ pressM (C₀ m i) u (l-i) V + E:=by unfold E u u'; rw [W]; exact hZ -- tune placeholder
       have pF: K (i+1)≤ K i+E:=by unfold K; rw [hk]; unfold u u' at hpz; nlinarith only [hpz, mul_le_mul_of_nonneg_left hp₁ hr.le, mul_le_mul_of_nonneg_left hp₁ (hx i)]
       have hA : partitionZ u U (S i)=partitionZ u' U (S (i+1)):= (A.balance i (by omega)).trans (A.balance (i+1) e').symm
       unfold n compensated at b' ⊢; rw [norm_mul,Complex.norm_exp,Complex.neg_re] at b' ⊢; rw [←show partitionZ _ _ _=_ from hA]; apply le_trans (Real.exp_monotone pF); rw [Real.exp_add,mul_comm (Real.exp _) (Real.exp E)]; refine (mul_le_mul_of_nonneg_left b' (Real.exp_pos _).le).trans ?_
       rw [←mul_assoc,←Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by change E+(-u.v.re) ≤ -u'.v.re; unfold E; linarith)) (norm_nonneg _)
 apply hu.trans'; apply Real.exp_monotone; have hS:2*r+f' j ≤ s:= by change f' j ≤ r at vT; unfold r at *; linarith
 exact sub_le_sub_left (mul_le_mul_of_nonneg_right hS (zero_le_one.trans (sites_pos _))) _
end Steam
end YM.CF.Py.Rate
