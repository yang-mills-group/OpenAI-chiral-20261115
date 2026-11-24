import Anomaly.Ship.Temper
import Anomaly.Ship.Lender
import YM.SU5.Interaction.Kerosene.FuelDesk
/-!
Paying OrbitRack tariff using the actual Quench on F births and operator
costs from candles. Choose κ=1 (Kf also Quench), Γ Quench, bandwidth 1/B
using L=1+5/b, rate inside operator reserve at 1+8/b. No iterative
investment per footprint.
-/
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

namespace BScale

open Roots Wray Py Ione Lor Push.AbsoluteSums.Animals Vow Stax Cadre Sour Vow.TreasuryFog

variable {F G H S : ℝ→ℝ}
-- indices high.Weight Q via Spade. uses ψ only for denominator/Keeper gifts
local notation "Bb" x:max=> (radiusB x:ℝ)
local notation "Gq"=>allotΨ R.L
open Pail.Dew
def waxIncome (C:ℝ→ℝ)(x:ℝ):= reserveT 2 6 (radiusB x) (runway x) * (C x*(1-degreePrice (radiusB x) (C x) (runway x))⁻¹)
def yokeIncome (C κ:ℝ→ℝ)(x:ℝ):= reserveT 2 6 (radiusB x) (runway x) * ((κ x)⁻¹ * (C x*200))
variable (L:Patch) {E V F U:ℝ→ℝ}
abbrev wallH (E V Z:ℝ→ℝ)(i:ℝ):= spartCost (radiusB i) (Z i) (E i+ V i)
lemma wax_price(R:Patch)(C:ℝ→ℝ)(p:Litt R 2 C): Litt R 2 (waxIncome C):=by
 let S(x):=1-degreePrice (radiusB x) (C x) (runway x); have ht:Tendsto S atTop (𝓝 1):=by
    unfold S; simpa using (show Tendsto (fun x:ℝ=>1-degreePrice (radiusB x) (C x) (runway x)) atTop (𝓝 (1-0)) from (tendsto_const_nhds.sub (deg_chill _ (Chill_v.coin (Q:=R) (p.height_r.low (by omega)))).spine_a))
 let T':= fun x=> (S x)⁻¹; have h:BoreP T':=(BoreP.still 2).tune ((ht.inv₀ one_ne_zero).abs.eventually (ge_mem_nhds (show |(1:ℝ)⁻¹| < |(2:ℝ)| from by norm_num)))
 exact spade_grip (reserve_bond ..) (Litt.more (spade_grip h p) (Eventually.of_forall fun i=>by rw [mul_comm (C i)]))
lemma sig_purchase (E V F U X:ℝ→ℝ)(p:Litt L 2 U)(t:Litt L 2 X)(e:sizeK L.L 2 E)(hv:sizeK L.L 1 V)(hF:Quench L F)(n m:ℕ):
    ∃ J κ:ℝ→ℝ,Litt L 2 J∧ BoreP κ∧
     (∀ᶠ i in atTop,1≤ κ i∧ (∀ p:BudgetPoint,p.B= radiusB i→p.order=6→p.power=2→∃ c:Mantling p (U i) (wallH E V U i) (F i) (κ i) 0 (J i) n m (X i), yσE p (gearOcc (κ i) c.census)=waxIncome J i∧ yσF p (gearOcc (κ i) c.census)=yokeIncome J κ i)∧ yokeIncome J κ i ≤allotΨ L.L i/(Bb i)∧0< J i):=by
 let S(x):= inkScatter n (radiusB x) |U x+spartCost (radiusB x) (U x) (E x+ V x)|
 obtain ⟨J,κ,G,K,T⟩:= sale_ever L _ t S (scatter_b _ (p.add_e (spartan_B p ((e.low (by omega)).accrue hv)))) _ hF m
 refine ⟨J,κ,G,K,?_⟩; filter_upwards [T] with i u; obtain ⟨⟨kx,B⟩,Q,H,Z⟩:=u; refine ⟨kx,fun p v t x=>?_,Z,Q.κval⟩
 have h:Mantling p (U i) (wallH E V U i) (F i) (κ i) 0 (J i) n m (X i):=by
    constructor <;> (rw [v]<;>first| rwa [t]|exact B|exact H.2|exact (add_le_add_left (le_abs_self _) _).trans H.1)
 refine ⟨h,?_,?_⟩
 · unfold waxIncome yσE; -- η=νb
   change reserveT p.power p.order p.B ((p.B:ℝ)⁻¹) * (J i*(1-degreePrice p.B (J i) ((p.B:ℝ)⁻¹))⁻¹)=_
   rw [x,t,v]; rfl
 unfold yokeIncome yσF; change reserveT p.power p.order p.B ((p.B:ℝ)⁻¹) * ((κ i)⁻¹*(J i*200))=_; rw [t,x,v]; rfl
lemma thirstV(L:Side) : sizeK L 1 (fun x=>chillCash (radiusB x)):=by
 let Z(t:ℝ):= Real.exp (- (Bb t)/40)
 have hz:sizeK L 1 Z:=by
    apply (sizeK.tip L (1/40:ℝ) (by norm_num)).low (by omega)|>.cost_d
    filter_upwards with x; unfold Z Neige.tipPay; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; refine le_trans ?_ (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (Nat.div_le_self (radiusB x) _)) (by norm_num : -(1/40:ℝ) ≤ 0)); linarith -- tune
 let V(x):=(1-Real.exp (-1/(Bb x)/4))⁻¹; have hv:BoreP V:=by
    apply BoreP.tune (BoreP.radius_c.grip (BoreP.still 12)); filter_upwards [Work.E01.radiusB_tendsto.eventually_gt_atTop 0] with i t
    let B:ℝ:= radiusB i; have hz:0<B:= Nat.cast_pos.mpr t; have he:B≥1:=Nat.one_le_cast.mpr t
    let Q:= 1/B/4; have ht:0<Q:=by unfold Q; positivity
    have hs:Real.exp Q≤3:= (Real.exp_monotone (show Q ≤1 from (by unfold Q; have ht:1/B≤1:=(div_le_self zero_le_one he); linarith only [ht]))).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
    have hp':0<1-Real.exp (-Q):= sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))
    have hp: V i=(1-Real.exp (-Q))⁻¹:=by unfold V Q B; ring_nf
    rw [hp,abs_of_pos (inv_pos.mpr hp'),abs_of_pos (mul_pos hz (by norm_num:(0:ℝ)<12))]
    refine inv_anti₀ (?_:0<(B*12)⁻¹) (?_: (B*12)⁻¹ ≤1-Real.exp (-Q))|>.trans_eq (inv_inv _)
    · positivity
    rw [Real.exp_neg]; apply le_of_mul_le_mul_left _ (Real.exp_pos Q); rw [mul_sub, mul_one, mul_inv_cancel₀ (Real.exp_pos Q).ne']; have hv:=Real.add_one_le_exp Q
    refine (mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ (B*12)⁻¹)).trans ?_; rw [show 3*(B*12)⁻¹= Q from (by unfold Q; field_simp; ring)]; linarith
 exact (hz.tint (hv.creditK L)) -- 1+0
-- ALL sailors rho budgets. larger C even $exp(B^epsilon)$ works for E. Scope cp needed numeric. Force report smaller.Z.Wands
lemma sails_day (C κ E F:ℝ→ℝ)(e:sizeK L.L 2 E)(p: Quench L F)(b:Litt L 2 C)(v:∀ᶠ x:ℝ in atTop, 1≤κ x∧ 0<C x∧ yokeIncome C κ x≤ allotΨ L.L x/(Bb x))(m:ℕ)(D ε:ℝ)(u:1 ≤ D)(h:0 < ε):
    ∀ᶠ x:ℝ in atTop,let B:= radiusB x; let Y:= F x+(yokeIncome C κ x+yokeIncome C κ x);
       chillCash B*(E x+waxIncome C x) ≤ ε*allotΨ L.L x∧ m*D*Y+chillCash B*Y+chillCash B*Y ≤ ε*allotΨ L.L x∧ packF D B m :=by
 let Q:=allotΨ L.L; let w(x):=chillCash (radiusB x); let vκ:=yokeIncome C κ
 have hf:Quench L F:=p
 let d:=runway; let B:=fun x:ℝ=>radiusB x
 have hv:Tendsto (fun x=>(B x:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
 have ha:Tendsto (fun x=>vκ x/Q x) atTop (𝓝 0):=by
    refine squeeze_zero' ?_ ?_ (tendsto_inv_atTop_zero.comp hv); swap
    · filter_upwards [v,draft_π L.L] with i p k; have hv:0 < Q i:=pow_pos k.2.1 _; rw [div_le_iff₀ hv]; rw [mul_comm]; exact p.2.2.trans_eq (by unfold Q B Function.comp; ring)
    filter_upwards [v,draft_π L.L,Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with i h k u
    unfold vκ yokeIncome; have he:=h.2.1; have ht:0 < κ i:=zero_lt_one.trans_le h.1; unfold reserveT coin_n stilK runway; have hv:0 < Q i:=pow_pos k.2.1 _; positivity
 let Y(x):=F x+(vκ x+vκ x); have ht:Tendsto (fun x=>Y x/Q x) atTop (𝓝 0):=by unfold Y; simp_rw [add_div]; simpa only [add_zero] using (show Tendsto (fun x=>F x/Q x) atTop (𝓝 0) from p.spine_a).add (ha.add ha)
 have hr:sizeK L.L 3 (fun x=>w x*(E x + waxIncome C x)) := (thirstV ..).tint (e.accrue (Litt.height_r (wax_price L C b))); have hp:(Tendsto (fun x=>((m:ℝ)* D)*Y x/Q x+w x* Y x/Q x+w x*Y x/Q x) atTop (𝓝 0)):= by
    have hw:Tendsto w atTop (𝓝 0):=(thirstV L.L).spine -- implicit L? specify
    simp_rw [mul_div_assoc]; simpa only [mul_zero,add_zero] using (((ht.const_mul _).add (hw.mul ht)).add (hw.mul ht)) -- tune
 have hz:∀ᶠ B:ℕ in atTop, packF D B m:=by
    let X(β:ℕ):=D; apply (niceT m X) -- no n
    have hu:Tendsto (fun B:ℕ=>Real.exp ((B:ℝ)/10000)) atTop atTop:=Real.tendsto_exp_atTop.comp (by simpa only [div_eq_mul_inv] using ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const (by norm_num:(0:ℝ)<10000⁻¹)))
    exact (hu.eventually_ge_atTop ((2*D)^m)).mono fun x v=>⟨u,v⟩
 filter_upwards [pill_R (k:=2) _ h hr,hp.eventually (ge_mem_nhds h),draft_π L.L,Work.E01.radiusB_tendsto.eventually hz] with i p v k r
 have hu:0<Q i:=pow_pos k.2.1 _; intro X Y'; refine ⟨p.le, (div_le_iff₀ hu).mp ?_|>.trans_eq (by rfl),r⟩ -- tune
 rw [add_div,add_div]; exact v
end BScale
end YM.CF.Py.Rate
