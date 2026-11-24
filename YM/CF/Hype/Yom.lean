import YM.CF.Hype.Flash
set_option autoImplicit false
set_option maxHeartbeats 865000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
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
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees Bake Vow Larch -- remove
open Vow Lilt Bake Rue Trees NormedSpace
variable {γ e q α γ' KU b:ℝ}{K K':Cusp n} {L:blazeK n}{F E:Pax n}{Q:Aura n→ℝ} (Wp:Wisp P F E h γ c d) (T: ArmsK P K L h) (R: RegBudget n)(u:∀ V:Orbit n,FleetS P.threshold V.1→exponentL P R V.1+fuelV P K' V=coldE P E V)(η0:1 ≤ h) -- all colors.V.Number
lemma add_v(P:BudgetPoint)(F K:RegBudget n){v e:ℝ}(p:IncX (fun _=>False) F P h v)(u:IncX (fun _=>False) K P h e):IncX (fun _=>False) (F+K) P h (v+e):=by
 obtain ⟨Z,g,Y⟩:=p.weight -- field tune
 obtain ⟨Q,w,q⟩:=u.weight
 refine ⟨⟨Z+Q,fun i=>prop_add P i (g i) (w i),fun i=>?_⟩,fun _ v=>v.elim⟩
 apply le_trans _ (add_le_add (Y i) (q i)); rw [←Finset.sum_add_distrib]; refine sum_le_sum fun j _=>?_ ; split_ifs; · exact Eq.le (by unfold BudgetPoint.mass; rw [Pi.add_apply,mul_add])
 rw [add_zero]
local notation "PΞ"=> P.supportExponent+1
local notation "qθ"=> degreePrice P.B γ 1
local notation "qB"=> degreePrice P.B γ' 1
local notation "U'S"=> (γ * (qθ)^0*(1-qθ)⁻¹)
abbrev Cog_P(P:BudgetPoint)(v b:ℝ):= reserveT P.power P.order P.B 1*(b⁻¹*(v*degreePrice P.B v 1^0*(1-degreePrice P.B v 1)⁻¹))
variable (hQ: Anuk K' Q P h)(KB:∀ i:Seat n,tallB Q P.B (P.supportExponent+1+1) i≤ α) (KK:∀ i:Seat n,tallB (hymn L) P.B (P.supportExponent+1+1+1) i≤ KU)
variable (κ dt:ℝ)(u0:1 ≤κ)(qh:0 < γ')(hb:degreePrice P.B γ' 1 < 1)(hk:(α+c)+(γ*degreePrice P.B γ 1^0*(1-degreePrice P.B γ 1)⁻¹)≤1)(hp:κ* KU + Real.exp 1*((γ*degreePrice P.B γ 1^0*(1-degreePrice P.B γ 1)⁻¹)+(α+c)) ≤ γ')(v:IncX (fun _=>False) R P h dt)
local notation "σN"=>Aura n
open Iva
private lemma poll(p:Aura n→ℝ)(V:Orbit n)(u:FleetS P.threshold V.1): let F' :=∑ i:Aura n,owed_E n (p i); F'+ fuelV P (nextE p) V=coldE P (fun i _ => owed_E n (p i)) V :=by
 intro F'; unfold F' fuelV coldE; rw [sum_filter,sum_filter,←sum_add_distrib]; apply sum_congr rfl; intro i _
 by_cases q:pingS P.threshold i.val V.1; · rw [if_pos q, if_neg (show ¬fuelH (flags P.threshold V.1) i from (not_not.mpr ((shoreK _ _ u i.val).mpr q))), add_zero]
 rw [if_neg q,if_pos (show fuelH (flags P.threshold V.1) i from fun g=>q ((shoreK _ _ u i.val).mp g)),nextE,add_neg_cancel]
include Wp T u hQ v KB KK u0 qh hb hk hp η0
local notation "Φπ"=> P.supportExponent+1+1
lemma pearL :∃ (F':RegBudget n)(Kv:ForceBudget n)(a:ℝ), IncX (fun _=>False) F' P h (dt+reserveT P.power P.order P.B 1*d) ∧ Dark (fun _=>False) Kv P h (Cog_P P γ' κ) ∧∀ V:Orbit n,FleetS P.threshold V.1→Palot.hGas (flags P.threshold V.1) (keyL P K F V)=Real.exp a •(exp (exponentL P F' V.1)*fueled P Kv V):=by
 obtain ⟨G,W,LL,C,A,he,ht,hF,hG,hW,hl,hk',hv,wU⟩:=Wp.keep; choose X hx using he; let H' :=∑ i:Aura n,X i
 let S:=K'+ nextE X; have hν:=zero_le_one.trans η0; have Qn:0≤ Q+LL:= add_nonneg hQ.1 fun i=>(hG i).wage hν
 have hΨ: Anuk S (Q+LL) P h:=by refine ⟨Qn,fun i D q l=> ?_⟩; apply (hQ.2 i D q l).plus; exact nom_F η0 P i _ (hx i ▸ hG i) D -- tune
 let τ:Ids n:=Classical.arbitrary _; let T':= sunY univ knotD (fun i=>cloveE W τ (knotD i)); have he':0 ≤ P.supportExponent+1:= (add_pos P.exponent_pos zero_lt_one).le; have hz(i:Seat n): tallB (Q+LL) P.B (P.supportExponent+1+1) i ≤ α+c:=by rw [tall_add]; exact add_le_add (KB _) (hl _)
 refine ⟨R+T',budgetR (roomV P F K S), H',add_v P R T' v (width_v P W wU τ hW hν hk'),dark_F (Qm:=fun _=>False) T hΨ.2 hΨ.1 ht he' zero_lt_one hF zero_lt_one η0 u0 ?_ hz ?_ le_rfl hb qh hp (fun i e y v=> v.elim),?_⟩ -- tune.. ellipsis
 · intro i; apply le_trans _ hk; apply add_le_add_left -- tune side
   obtain ⟨j,y⟩:=i.property
   have hp:(Q+LL) i≤tallB (Q+LL) P.B (P.supportExponent+1+1) j:= (le_mul_of_one_le_right (Qn i) (Real.one_le_exp (mul_nonneg (add_nonneg he' zero_le_one) (by exact Nat.cast_nonneg (coverNumber P.B i.val))))).trans (single_le_sum (s:=Finset.univ.filter (fun i:Aura n=>j∈i.val)) (f:=fun i=>(Q+LL) i * Trees.currency P.B (P.supportExponent+1+1) i.val) (fun i _=>mul_nonneg (Qn i) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,y⟩))
   exact hp.trans (hz j)
 · intro i; apply (tall_m (hymn L) (b:=P.supportExponent+1+1+1) _ (le_add_of_nonneg_right zero_le_one) i).trans (KK i); exact fun i=> sum_nonneg (fun j v=> (T.price _ _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2).wage hν) -- tune Arm names
 intro V t; let W':= exponentL P (R+T') V.1
 have he:coldE P (FeeD P F) V=coldE P (G+E+W) V:=sum_congr rfl fun i q=>hv _ _ (hates (by rw [sdiff_empty]; exact (mem_filter.mp q).2))
 have ht': ∑ i:Aura n,owed_E n (X i)= owed_E n H':= (Finset.sum_smul ..).symm
 have hz:owed_E n H'+fuelV P (nextE X) V=coldE P G V:=by rw [←ht', show G=(fun i:Aura n=> fun _=> owed_E n (X i)) from funext hx]; exact poll X V t
 have hl: owed_E n H'+W'+fuelV P S V=coldE P (FeeD P F) V:=by rw [he,crep,crep, ←u _ t, ←fair_v P W wU τ V]; unfold S W'; rw [toast,ripe_H P V R T',←hz]; abel
 rw [asterT ht he' hF zero_lt_one η0 V t _ hl]; letI :NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ (Cipher n); rw [exp_add,owed_E, ←thim_v, ←Iva.yeaH, ←Complex.ofReal_exp,thim_v]; unfold Lilt.thim; rw [smul_mul_assoc,one_mul,smul_mul_assoc] -- tune
end YM.CF.Larch
