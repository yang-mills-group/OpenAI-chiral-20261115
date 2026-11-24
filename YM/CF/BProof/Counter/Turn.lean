import YM.CF.BProof.Counter.Ride
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi.Denn
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D' Y Z:Support (More n)}{U:Pane n}
open AnalyticBridge.VerifiedReset Next.Foundations Push.Local PhysicalNext.JointLoad Heir
open Vow Rue Ione Larch Beau Floral
namespace Cart
variable (C:Cart n m)
-- exact Pi
abbrev mark (a:ℝ)(x:CubeP n)(P:BudgetPoint)(U:Pane n):= C.kWh x a * freeze P x.2 U
def PiZ (P:BudgetPoint)(a:ℝ)(U:Pane n):=∑ i:CubeP n,C.mark a i P U
lemma mark_pay (x:CubeP n): |C.mark a x P U| ≤ C.w x.1 x.2*(Compass.compassCost SU.group P*(P.threshold^2*|a|)):=by
 unfold mark kWh; rw [abs_mul,abs_mul,abs_of_nonneg (C.nn ..)]; refine le_trans (mul_le_mul_of_nonneg_left (frost_pay x.2) (mul_nonneg (C.nn ..) (abs_nonneg _))) (le_of_eq ?_); ring
lemma mark_turn(s:Sweep n)(p:C.Turns s)(x:CubeP n): C.mark a ((boxA s).symm x.1,(boxA s).symm x.2) P (flashA s U)=C.mark a x P U:=by unfold mark kWh; dsimp only []; rw [p,frost]
lemma mark_reads(x:CubeP n):LocalOn (Lattice.halo 4 {x.2}) (C.mark a x P):=fun u v t=> congrArg (_*·) (freeze_local x.2 u v t)
lemma PiZ_turn (s:Sweep n)(p:C.Turns s): C.PiZ P a U=C.PiZ P a (flashA s U):= Fintype.sum_equiv ((boxA s).symm.prodCongr (boxA s).symm) _ _ fun i=> (C.mark_turn s p i).symm
lemma PiZ_pay : |C.PiZ P a U| ≤ (Fintype.card (Skye.Seat n):ℝ)*(Compass.compassCost SU.group P*(P.threshold^2*|a|)):=by
 unfold PiZ; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum fun i _=> C.mark_pay i).trans_eq ?_); rw [Fintype.sum_prod_type]; simp only [←Finset.sum_mul,C.day,one_mul,sum_const,card_univ,nsmul_eq_mul]; ring
@[fun_prop] lemma mark_M(x:CubeP n): Measurable (C.mark a x P):=measurable_const.mul (freeze_M ..)
@[fun_prop] lemma PiZ_M : Measurable (C.PiZ P a):=by unfold PiZ; fun_prop
lemma mark_g(x:CubeP n): GaugeInvariant (C.mark a x P):= fun u v=> congrArg (_*·) (freeze_g x.2 u v)
lemma PiZ_g : GaugeInvariant (C.PiZ P a):= fun u v=> sum_congr rfl fun i _=> C.mark_g i u v
private lemma Ring_eq(V: Skye.Orbit n)(x z:Scree.Hub n)(p:x.val.2⊆z.val.2)(F:Copy n)(Ω:Support (More n)): Vow.flick (pur x) F (Ω∩(pur z).val) V=if Disjoint Ω (pur x).val then F V else 0:=by
 have hp:Disjoint (Ω∩(pur z).val) (pur x).val ↔ Disjoint Ω (pur x).val:=by
    constructor
    · exact fun h=>Finset.disjoint_left.mpr (fun i b g=>Finset.disjoint_left.mp h (mem_inter.mpr ⟨b,p g⟩) g)
    exact fun h=>Disjoint.mono_left inter_subset_left h
 unfold Vow.flick; simp only [hp]; split_ifs <;> rfl
private lemma single_W(P:BudgetPoint)(V:Skye.Orbit n)(x:Skye.Seat n) : Vow.march P (pur (block x)) (oV (W x a)) V= moldV _ (a*freeze P x V.1):=by unfold freeze Vow.march; split_ifs; rfl; rw [mul_zero,map_zero]
private lemma pair_eq (j:CubeP n)(V:Skye.Orbit n)(h:FleetS P.threshold V.1):
 moldV _ (C.mark a j P V.1)= Vow.march P (pur (block j.1)) (oV (W j.1 (C.kWh j a))) V+ Vow.march P (pur (stem j)) (oV (C.patch a j)) V+fuelV P (stroke (pur (block j.2)) (pur (block j.1)) (pur (stem j)) (oV (W j.2 (C.kWh j a))) (oV (W j.1 (C.kWh j a)))) V:=by
 unfold mark; rw [←single_W P V j.2]; simp_rw [Vow.march_f V h]; unfold stroke; rw [shade_t]; let D:= flags P.threshold V.1
 by_cases g:Disjoint D (pur (stem j)).val
 · have hp: ¬fuelH D (pur (stem j)):= fun q=> q g.symm
   rw [if_neg hp,if_pos g,if_pos (Disjoint.mono_right (show (pur (block j.2)).val⊆_ from Finset.subset_union_right) g),if_pos (Disjoint.mono_right (show (pur (block j.1)).val⊆_ from Finset.subset_union_left) g)]; change _= _+ (W j.2 (C.kWh j a) V.1-W j.1 (C.kWh j a) V.1)+0; unfold oV; abel
 have hp:fuelH D (pur (stem j)):= fun w=>g w.symm; rw [if_pos hp,if_neg g,Pi.sub_apply,Ring_eq V _ _ Finset.subset_union_right _ _,Ring_eq V _ _ Finset.subset_union_left _ _]; abel
lemma Equality(a:ℝ)(V:Skye.Orbit n)(g:FleetS P.threshold V.1): moldV n (C.PiZ P a V.1)=exponentL P (Er n a+C.Sr a) V.1+ fuelV P (C.Zr a) V:=by
 let D(i:CubeP n):=Vow.march P (pur (block i.1)) (oV (W i.1 (C.kWh i a))) V
 unfold PiZ; rw [map_sum,sum_congr rfl (fun i _=> pair_eq C i V g),sum_add_distrib,sum_add_distrib]; unfold Zr Sr Er
 rw [ripe_H P V _ _,release_v,release_v,tunes]; congr 2
 rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> ?_
 change (∑ j:Skye.Seat n,D (i,j))=Vow.march P (pur (block i)) (oV (W i a)) V
 unfold D; simp_rw [single_W]; rw [←map_sum]; apply congrArg; unfold kWh; dsimp only []; rw [← sum_mul, ←sum_mul,C.day,one_mul]
@[simp] lemma PiZ_zero(a:BudgetPoint)(U:Pane n): C.PiZ a 0 U=0:=by simp [PiZ,mark,kWh]
@[simp] lemma Sr_zero : C.Sr 0=0:=by unfold Sr sunY patch kWh; funext i; simp [W_zero]
private lemma flick_0(x:Aura n)(D): Vow.flick x 0 D=0:=by unfold Vow.flick; split<;>rfl
@[simp] lemma Zr_zero:C.Zr 0=0:=by unfold Zr stroke chasmR kWh; simp [W_zero,show oV (0:InkD n)=0 from rfl,flick_0,show (fun t:Support (More n)=>(0:Copy n))=0 from rfl]
lemma eras (n:Side): Er n 0=0:=by funext i; rw [first]; split_ifs; exact W_zero _; rfl
end Cart
-- pre-choices scalar cost uniformlyK
abbrev CH (P:BudgetPoint)(m:ℕ)(Γ:ℝ):= let A:=P.supportExponent; let L:=TC P m Γ; 1+(Real.exp A*L+Real.exp A*(L+L)+(Cart.places m:ℝ)*(Real.exp (A+2)*(chi_f P.order*(L+L))))
lemma priceCH(P:BudgetPoint)(m:ℕ)(Γ:ℝ)(u:0≤Γ): 0< CH P m Γ:=by
 have hh: 0≤ TC P m Γ:= by unfold TC; have :=Compass.compass_cost_nn SU.group P; positivity
 have hx:=spicy_f P.order; dsimp only [CH]; positivity
lemma usesCH(P:BudgetPoint)(m:ℕ)(Γ:ℝ)(a:ℝ)(u:0≤Γ):let K:= CH P m Γ*(P.threshold^2*|a|); Real.exp P.supportExponent*jet P m Γ a≤ K∧ Cart.leafCost P m Γ a ≤ K∧ Cart.Z_cost P m Γ a (P.supportExponent+1+1) ≤ K:=by
 have ht:=jet_nn m P u a; have he:=spicy_f P.order; have hx: 0≤ Real.exp P.supportExponent*jet P m Γ a:=(by positivity); have hs:0 ≤ Cart.leafCost P m Γ a:=mul_nonneg (Real.exp_pos _).le (add_nonneg ht ht); have hZ:0 ≤ Cart.Z_cost P m Γ a (P.supportExponent+1+1):=mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (mul_nonneg he (add_nonneg ht ht)))
 intro K; rw [show K=P.threshold^2* |a|+(Real.exp P.supportExponent*jet P m Γ a+Cart.leafCost P m Γ a+ Cart.Z_cost P m Γ a (P.supportExponent+1+1)) from (by unfold K CH Cart.leafCost Cart.Z_cost Cart.chi Cart.chargeP jet; rw [show P.supportExponent+1+1=P.supportExponent+2 from by ring]; ring)]; have hp:0≤P.threshold^2*|a|:=mul_nonneg (sq_nonneg _) (abs_nonneg _); exact ⟨by linarith,by linarith,by linarith⟩
end YM.CF.Taxi.Denn
