import YM.SU5.Interaction.Kerosene.Lustre
import YM.SU5.Interaction.Kerosene.Rousing
import YM.CF.Rive.New
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees
-- Origin check for FeeD & Force. ALL Orbit.
open Palot Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Gas Ione Stax Bake Cadre Sour Rive Mew
set_option maxHeartbeats 600000
/-- NOTE these are *total* increments for Reg locally (output from FeeD, in addition to uncompressed old PL itself!), and totals for Force costed, not the increments relative incoming. May subtract after all these earnings. This is rate l-2*δ. -/
abbrev clearZone (P:BudgetPoint)(K:Cusp n):Pax n:= FeeD P (fun i=>K i ∅)
abbrev clearWarp (P:BudgetPoint)(K:Cusp n): Cusp n:= roomV P (fun i=>K i ∅) K 0
variable (K:Cusp n)(C:blazeK n)(κ L Γ Γ' κ':ℝ)(T0:Ids n)
structure Reservoir (h:ℝ)(δ:ℝ)(n' : ℕ)(P:BudgetPoint)(K:Cusp n)(C:Cadre.Tape (A:= Seat n))(Γ L:ℝ):Prop where
 frame:∀ X:Aura n, ∀ D⊆ X.val,Fray P h (cipherK n') X D (K X D) (C X D)
 urn : ∀ i:Seat n,tallB (roofL C 1) P.B ((L+δ)+δ) i ≤ Γ
 turf : Turf (fun i=> K i ∅)
noncomputable abbrev dollar (P:BudgetPoint)(a d:ℝ):ℝ:=a*(degreePrice P.B a d)^0*(1-degreePrice P.B a d)⁻¹
local notation "ZCo"=> clearZone P K
local notation "ZD"=> clearWarp P K
local notation "C₁"=> dollar P Γ d
local notation "C₂"=> dollar P Γ' d
variable (A':Reservoir h d m P K C Γ L)
variable (t:0 < d)(w:0 ≤ L)(p:0 < Γ)(q: degreePrice P.B Γ d <1)(hz:1 ≤ h)
include A' t w p q hz
lemma ΩRank : Ready Palot.stern P.B (fun i:Aura n=> C i ∅) (L+d) Γ d (degreePrice P.B Γ d):=by
 have ht := zero_le_one.trans hz; let T:= A'.frame; have hb:Fiery C:=fun i D p=>(T i D p).merit.wage ht
 exact ready_T p t q (fun i=>hb i _ (empty_subset _)) (fun o=> (lam_H C o 1 P.B _ zero_lt_one hb (A'.urn _)).1)
lemma glowTrip (yᵥ:Seat n) : tallB (Vow.hymn C) P.B (L+d) yᵥ ≤ Γ :=by -- change y
 have ht := zero_le_one.trans hz; let T:= A'.frame; have hb:Fiery C:=fun i D p=>(T i D p).merit.wage ht
 have h':= lam_H C yᵥ 1 P.B _ zero_lt_one hb (A'.urn _); exact (Larch.tall_m _ (fun i=>sum_nonneg (fun j p=> hb _ _ (mem_filter.mp p).2.2)) (le_add_of_nonneg_right t.le) _).trans (by simpa using h'.2)
lemma mantle (v:Orbit n)(hp:Rue.FleetS P.threshold v.1): Palot.hGas (flags P.threshold v.1) (hailV (flags P.threshold v.1) K v) = NormedSpace.exp (exponentL P (cast_E (clearZone P K) T0) v.1)*fueled P (budgetR (clearWarp P K)) v:=by
 have u:=(ΩRank K C L Γ A' t w p q hz); let F':=clearZone P K; let W(i:Aura n):=K i ∅; let T:=flags P.threshold v.1
 have ht:exponentL P (cast_E F' T0) v.1=coldE P F' v:=ocean P _ _ (turfK _ A'.turf) _ -- order
 have hx: exponentL P (cast_E F' T0) v.1 + fuelV P 0 v= coldE P F' v := by rw [ht]; simp [fuelV]
 have he:(P.supportExponent+(L-P.supportExponent))=L:=by ring
 let a:=L-P.supportExponent; have hv:0 ≤ P.supportExponent+a:= he.symm ▸ w
 have hg:= asterT (K:=K) (he.symm ▸ u) hv (fun i=>(A'.frame i ∅ (empty_subset _)).merit) t hz v hp (exponentL P (cast_E F' T0) v.1) hx -- tune orientation
 have h0: hailV T K v=keyL P K W v:=by
    funext i; unfold keyL; split; next hg=> unfold hailV; rw [show T∩i.val=∅ from disjoint_iff_inter_eq_empty.mp hg]
    rfl -- tune indentation
 change hGas T (hailV T K v)=_; rw [h0]; exact hg
variable (p':0 < Γ')(H:dollar P Γ d ≤ 1)(htΓ: degreePrice P.B Γ' d <1)(pc:Γ+Real.exp 1*dollar P Γ d ≤ Γ')
-- direct receipt incl lit contexts & tariff conversion.
include p' H htΓ pc
lemma funds_glow (u:0< c) : Dust (budgetR ZD) P h (cipherK m) (L-P.supportExponent) C₂ ∧ SanB (budgetR ZD) (giftK P (L-c)) P h (fun _=>reserveT P.power P.order P.B c*C₂) ∧ ForgeB (cast_E (clearZone P K) T0) (filmK P L) P h (fun _=> reserveT P.power P.order P.B d*C₁) ∧ ∀ i:Aura n, Medal P i.val ∅ (ZCo i) h (spanD i (urnL C) 0):=by
 let F(i):=K i ∅; let F1:=clearZone P K; let Q:Cusp n:=0; have hx:0 ≤ h:= zero_le_one.trans hz
 let Lν:=Reservoir.urn A'; have hy:= frame_v A'.frame
 have HE(i:Aura n)(D:Support (More n))(p:D.Nonempty)(hp:D⊆i.val): Medal P i.val D (Q i D) h ((0:Aura n→ℝ) i):= Medal.zeroT
 have hr:= ΩRank K C L Γ A' t w p q hz; let Vf:= glowTrip K C L Γ A' t w p q hz; let vC(i:Aura n):= C i ∅
 have y(i:Aura n):Medal P i.val ∅ (K i ∅) h (vC i):=(A'.frame i _ (empty_subset _)).merit
 obtain ⟨hd,hk⟩:=rent_x hy HE le_rfl hr w y t hz le_rfl (fun i=>(by rw [Pi.zero_apply,zero_add]; exact H)) (fun i=>show tallB (0:Aura n→ℝ) P.B (L+d) i ≤ 0 by simp [tallB]) Vf le_rfl htΓ p' (by simpa only [one_mul,add_zero] using pc)
 let Cc:= windF C (bagU (urnL C) 0); let hp(i:Seat n): tallB (Vow.hymn Cc) P.B L i ≤ C₂:= (one_mul _).symm.trans_le (hk i)
 have hh(i:Aura n):Medal P i.val ∅ (ZCo i) h (spanD i (urnL C) 0):= glenP _ hz y hr (add_nonneg w t.le) 0
 refine ⟨⟨_,_,flameCard hd (fun X D h=> flareGlow hy (fun i D h=>(A'.frame i D h).loaf) _ _ h) (fun i=> by rw [show P.supportExponent+(L-P.supportExponent)=L by ring]; exact hp i)⟩,quoteK Cc ZD hd (fun i=> by rw [sub_add_cancel]; exact hp i) hx u,quoteE _ F1 hh (turfK _ A'.turf) T0 (thinX hr (add_nonneg w t.le) · 0) hx t, hh⟩
end YM.CF.Vow
#check YM.CF.Vow.funds_glow
#print axioms YM.CF.Vow.funds_glow
