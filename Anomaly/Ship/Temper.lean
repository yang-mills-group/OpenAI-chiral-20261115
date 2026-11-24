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
lemma spade_grip (h:BoreP H)(p:Litt R 2 F):Litt R 2 (fun x=>H x*F x):=by unfold Litt; simp_rw [mul_div_assoc]; exact h.grip p
lemma spade_one(R:Patch): Litt R 2 (allotΨ R.L):= ((Litt.gearX (R:=R) (BoreP.still 1)) (Eventually.of_forall fun i=>(one_mul (allotΨ R.L i)).symm))
lemma spade_sum (C:ℝ→ℝ)(p:Litt R 2 F)(q:Litt R 2 C) : Litt R 2 fun x=> F x+C x:=p.add_e q
lemma spade_scale (C:ℝ)(p:Litt R 2 F): Litt R 2 fun x=> C * F x:=p.scale_l C
lemma spartan_B (p:Litt R 2 F)(w:sizeK R.L 1 G) : Litt R 2 fun x=> spartCost (radiusB x) (F x) (G x):=by
 let S(k):=Sour.spanV (radiusB k); let X(k:ℝ):= (S k)* (((Bb k)⁻¹)⁻¹); have hx:BoreP X:=by simp_rw [X,inv_inv]; exact span_bore.grip BoreP.radius_c
 let Ta(k):=2*(X k*F k*G k); let W(k):=2*(X k*Ta k*G k)
 have h(A:ℝ→ℝ)(p:Litt R 2 A): Litt R 2 fun k=>2*(X k * A k *G k):=by
    refine Litt.scale_l (Litt.more (spade_grip (H:=G) (BoreP.inert w) (spade_grip (H:=X) hx p)) (Eventually.of_forall fun x=>?_)) _
    rw [mul_comm (X x*A x)]
 exact (show Litt R 2 (fun x=>Ta x+(2:ℝ)⁻¹*W x) from Litt.add_e (h F p) (Litt.scale_l (h _ (h F p)) _))
lemma scatter_b (m:ℕ)(p:Litt R 2 F): Litt R 2 (fun x=> inkScatter m (radiusB x) |F x|) := by
 unfold inkScatter
 let A(k:ℝ):= taxIns (10*radiusB k); have hv:BoreP A:=by
    simp only [A,taxIns,Nat.cast_mul,Nat.cast_ofNat]; exact (BoreP.still _).grip (((BoreP.still _).grip BoreP.radius_c).self _)
 exact spade_grip (hv.grip (BoreP.still _)) (p.abs_t.scale_l _)
-- costs ready with κ from below. No dependency on Force h actual price.Sale
lemma sale_ever (R:Patch)(C:ℝ→ℝ)(p:Litt R 2 C)(X:ℝ→ℝ)(f:Litt R 2 X)(F:ℝ→ℝ)(w:Quench R F) (m:ℕ): ∃ Γ κ:ℝ→ℝ,Litt R 2 Γ∧ BoreP κ ∧
    ∀ᶠ i:ℝ in atTop,(1≤κ i ∧10≤ radiusB i) ∧
     let P:= ThresholdPool (radiusB i) (runway i) (X i) (κ i* (chi_f 6*F i)) (X i) (Γ i)
     P∧(let γ:= Γ i; let η:= runway i; let d:=degreePrice (radiusB i) γ η; |(m:ℝ)*C i|+γ*(1-d)⁻¹≤1∧γ+Real.exp 1*(γ*(1-d)⁻¹+ m*C i) ≤100* γ) ∧ reserveT 2 6 (radiusB i) (runway i) * ((κ i)⁻¹*(Γ i*200)) ≤ allotΨ R.L i/(Bb i):=by
 let E(x):= |X x|+|(m:ℝ)*C x|+allotΨ R.L x; let B(x:ℝ):=(radiusB x:ℝ); let Γ(x):=4*(B x*E x)
 have hv:BoreP B:=BoreP.radius_c
 have he:Litt R 2 E:= (f.abs_t.add_e (show Litt R 2 fun x=>|(m:ℝ)*C x| from (p.scale_l _).abs_t)).add_e (spade_one R)
 have hΓ:Litt R 2 Γ:= (spade_grip hv he).scale_l _
 let r(x):=reserveT 2 6 (radiusB x) (runway x); let k(x):= r x*((Γ x*200)/(allotΨ R.L x)); let κ(x):= 1+B x*k x
 have hK:BoreP k:= (reserve_bond ..).grip (show Litt R 2 fun x=> Γ x*200 from hΓ.scale_v _); have hκ:BoreP κ:=(BoreP.still _).join (hv.grip hK)
 let C'(x):=κ x*(chi_f 6*F x); have ht:Quench R C':= (w.manyF _).bondF hκ
 have hp:Chill_v Γ:= Chill_v.coin (Q:=R) (hΓ.height_r.low (by omega)); let V:=runway; have hh(x:ℝ): V x=(B x)⁻¹:=rfl
 have hX:Chill_v (fun x=>|X x|):= Chill_v.coin (Q:=R) (f.abs_t.height_r.low (by omega))
 let S(x:ℝ):= Sour.spanV (radiusB x); have hz:Chill_v (fun x=> (B x)^2*(S x*|X x|)):= (hX.leanB span_bore).leanB (hv.self _)
 have hV: Tendsto (fun x=>|C' x|/allotΨ R.L x) atTop (𝓝 0):=ht.normF.spine_a
 refine ⟨Γ,κ,hΓ,hκ,?_⟩; filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 10,draft_π R.L,
 hz.spine_a.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/4)),hV.eventually (ge_mem_nhds (zero_lt_one)), -- tune
 (deg_chill _ hp).spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)), (deg_chill _ (hp.cheap 100)).spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)),hp.spine_a.eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)),((hp.leanB span_bore).leanB hv).spine_a.eventually (ge_mem_nhds zero_lt_one)] with x y v xσ cμ dμ eμ γu ps
 have hxb:10≤B x:=by unfold B; exact_mod_cast y
 have hxb':0<B x:=by linarith only [hxb]
 have h' :0<allotΨ R.L x:=pow_pos v.2.1 _; let κt:=κ x
 have hC:0 < E x:=add_pos_of_nonneg_of_pos (by positivity) h'; have hU:0<Γ x:=by unfold Γ; positivity
 have hk:1 ≤ κ x:=by unfold κ k r; unfold reserveT coin_n stilK runway; exact le_add_of_nonneg_right (by positivity) -- field unfolding.Ab
 have w:0 < V x:= by rw [hh]; positivity
 have hy:V x≤1/10:=by rw [hh,one_div]; exact inv_anti₀ (by norm_num) hxb
 refine ⟨⟨hk,y⟩,?_⟩; intro 𝒦
 let d:=degreePrice (radiusB x) (Γ x) (runway x)
 have hb:(1-d)⁻¹ ≤2:=(inv_anti₀ (by norm_num:(0:ℝ)<1/2) (show 1/2≤1-d from (by change d ≤ 1/2 at dμ; linarith only [dμ]))).trans_eq (by norm_num)
 have h:X x=X x:=rfl
 have hr: |X x| < E x:= lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg _)) (lt_add_of_pos_right _ h')
 have hc: |(m:ℝ)*C x|< E x:=lt_of_le_of_lt (le_add_of_nonneg_left (abs_nonneg _)) (lt_add_of_pos_right _ h')
 have he : E x = Γ x*V x/4:=by unfold Γ V; change _=4*(B x* _)*(B x)⁻¹/4; field_simp
 have hdb:B x*(S x*|X x|) ≤ V x/4:=by
    rw [hh, div_eq_mul_inv]; apply (le_inv_mul_iff₀ hxb').2; linarith only [xσ]
 have hxS: S x*|X x| ≤ V x/4:= (le_mul_of_one_le_left (mul_nonneg (show 0 ≤ S x from Nat.cast_nonneg _) (abs_nonneg _)) (show (1:ℝ)≤B x from by linarith only [hxb])).trans hdb
 have hVu:E x≤ Γ x/4:= by rw [he]; linarith only [mul_le_mul_of_nonneg_left hy hU.le,hU]
 have heΓ: |(m:ℝ)* C x| ≤ Γ x:=hc.le.trans (hVu.trans (by linarith only [hU]))
 have hu': Γ x * (1-d)⁻¹≤Γ x*2 := mul_le_mul_of_nonneg_left hb hU.le
 have hv' : Real.exp 1 * (Γ x*3) ≤ 9*Γ x:=by nlinarith only [mul_le_mul_of_nonneg_right Real.exp_one_lt_d9.le hU.le, hU]
 refine ⟨⟨⟨w,(by linarith only [hy])⟩,hU, ((le_inv_mul_iff₀ hxb').mpr ps).trans_eq (mul_one _), ?_, ⟨eμ, dμ.trans_lt (by norm_num)⟩,?_,?_,hxS.trans (by linarith only [w]),?_⟩,?_,?_⟩
 · change |C' x| < Γ x; refine ((div_le_one h'|>.mp cμ).trans_lt ?_); unfold E at hVu; linarith only [hVu,hU,abs_nonneg (X x),abs_nonneg ((m:ℝ)*C x)]
 · change _*(1-d)⁻¹ ≤ _; linarith only [hu',γu]
 · change _+Real.exp 1*(Γ x*(1-d)⁻¹) ≤ _; have ht:= mul_le_mul_of_nonneg_left (show Γ x * (1-d)⁻¹ ≤ Γ x * 3 from by linarith only [hu',hU]) (Real.exp_pos 1).le; linarith only [hv',ht,hU]
 · have hκ: |X x| ≤ Γ x*V x/4:=hr.le.trans_eq he
   rw [show (runway x)⁻¹ = B x from (by change ((B x)⁻¹)⁻¹=_; rw [inv_inv])]
   change _-(V x-S x*_) * Γ x < 0
   nlinarith only [hκ,mul_pos w hU,mul_le_mul_of_nonneg_right hdb hU.le,mul_le_mul_of_nonneg_right hxS hU.le] -- named S align
 · intro γ η q; change |(m:ℝ)*C x|+Γ x*(1-d)⁻¹ ≤ 1 ∧ _; refine ⟨by linarith only [hu',heΓ,γu],?_⟩
   change Γ x+Real.exp 1* (Γ x*(1-d)⁻¹+m*C x)≤ _
   have e:= mul_le_mul_of_nonneg_left (show Γ x*(1-d)⁻¹ + (m:ℝ)*C x ≤ Γ x * 3 from (by linarith only [(le_abs_self _).trans heΓ,hu'])) (Real.exp_pos 1).le; linarith only [e,hv',hU]
 have hρ: κ x ≥ B x*k x:=by unfold κ; apply le_add_of_nonneg_left zero_le_one
 change r x*((κ x)⁻¹*(Γ x*200))≤ allotΨ R.L x/(B x); rw [mul_left_comm (r x), ← div_eq_inv_mul]; apply (div_le_iff₀ (by linarith only [hk])).mpr; refine le_trans ?_ (mul_le_mul_of_nonneg_left hρ (by positivity : (0:ℝ)≤ allotΨ R.L x/B x)); apply le_of_eq; unfold k; have hg:=v.2.1; field_simp <;> ring
end BScale
end YM.CF.Py.Rate
