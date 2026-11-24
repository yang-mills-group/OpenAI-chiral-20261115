import YM.CF.Vp929.Stage.Coupon
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
namespace Pitching

namespace Focus
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt Vow Ione Beau
variable {Wk E0 E1 E2 E3 κb Hκ F0 b0 b1 b2 b3 Aχ Γχ r t v Q₀ u:ℝ} {n₀:ℕ}
open Test TestW QuiltB Lor Sour Stockpile

variable (e:1 ≤ K.j)
local notation "κF"=> budS R Wk Pay C'
local notation "k_"=> K.top.clip
local notation "κσ"=> K.below.width
local notation "κL"=> K.below.paths
local notation "cη" i:max => houseP (epoch i) K Aχ Γχ (κF i)
local notation "ſ"=> K.j
local notation "R1"=> R.L.val
local notation "ξt"=> (- (mstar R.L.val:ℝ))
local notation "Ht"=> h
local notation "Xτ" i:max=> shipA (epoch i) R1 k_ κσ κL Aχ
local notation "Tτ" i:max=> shipT (epoch i) R1 k_ κσ κL Aχ Γχ
local notation "Rℓ"=> R.L.val

structure FitB (b:ℕ)(K:Teller SU.group)(e:1 ≤K.j)(α γ P C W:ℝ):Prop where
 wave : aimC K.j e *(Real.exp (-(mstar b:ℝ))*earlyR K α γ W P C) ≤ earlyQ W P C/256
 regular : issueK K α e * earlyR K α γ W P C * 16000 ≤ (b:ℝ)
lemma reach_fit (h:0<Wk)(Pay C:ℝ) :∀ᶠ i:ℕ in atTop, FitB i K e Aχ Γχ Pay C Wk:=by
 let S:= earlyR K Aχ Γχ Wk Pay C; let T:= earlyQ Wk Pay C; have hp:0<T:=by
    have h:= Py.desire HI (mul_pos (by norm_num : (0:ℝ)<512) h); unfold T earlyQ earlyE Stockpile.march; have he(P C:ℝ):0< majorTp P C:=by unfold majorTp rayTop; positivity
    have hc:= he Pay C; positivity
 let X(i:ℕ):= aimC K.j e*(Real.exp (-(mstar i:ℝ))*S); have he:Tendsto X atTop (𝓝 0):= by
    unfold X; simpa only [Function.comp_apply,zero_mul,mul_zero] using (((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.comp starEnd)).mul_const S).const_mul (aimC K.j e))
 filter_upwards [he.eventually (ge_mem_nhds (show 0<T/256 by linarith)),tendsto_natCast_atTop_atTop.eventually_ge_atTop (issueK K Aχ e * S * 16000)] with i p q; exact ⟨p,q⟩
variable (s:Major V Wk b0 b1 b2 b3 Aχ Γχ n₀) {pW:WindV K.j 2}
local notation "κB"=> budS R Wk Pay pW.C
local notation "Η"=> houseP (epoch x) K Aχ Γχ (κB x)
local notation "E" z:max=> houseP (epoch z) K Aχ Γχ (κB z)
local notation "S"=> wrc R Wk Pay pW.C h
local notation "Re"=> earlyR K Aχ Γχ Wk Pay pW.C
local notation "Rt"=> earlyQ Wk Pay pW.C

abbrev χPrice (K:Teller SU.group)(R:Patch)(Pay C Wk Aχ Γχ:ℝ)(x:ℝ):=houseP (epoch x) K Aχ Γχ (budS R Wk Pay C x)
abbrev χPost (K:Teller SU.group)(R:Patch)(Pay C Wk Aχ Γχ:ℝ)(x:ℝ):=2*phase_v (epoch x) (budS R Wk Pay C x)+2*rollFX K.top.clip (epoch x) R.L.val (χPrice K R Pay C Wk Aχ Γχ x)
include s e
lemma χ_tame : Chill_v (fun i=> |χPost K R Pay C' Wk Aχ Γχ i|):=by apply (((βcert (Pay:=Pay) (C':=C') s).cheap 2).noteR ((chill_FX e s).cheap 2)).trend; filter_upwards with i; rw [abs_abs]

variable (hp:1≤ h) (fx : FitB R.L.val K e Aχ Γχ Pay pW.C Wk)
include hp fx
lemma adhere : ∀ᶠ y:ℝ in atTop,
 rollGX K.j e Rℓ (E y) h ≤ S y/256 ∧ couponX K R e Aχ Γχ (E y) y ≤ dleaf R.L y /1000:=by
 let r:= dleaf R.L; filter_upwards [subsidy_X (R:=R) (Pay:=Pay) (pW:=pW),Stockpile.stockpile_ν (R:=R)] with y H g
 have h1:0< r y:=by obtain e:= g.2.2.1; unfold εLeaf at e; unfold r; linarith
 have ht:= posEar (pW:=pW) (Pay:=Pay) s; obtain ⟨t,h',hB⟩:= early s y H ((sq_nonneg _).trans H) hp
 let Ls:ℝ:= R.L.val; let ξ:= εLeaf R.L y; have hh:0 < Ls:= Nat.cast_pos.mpr R.L.property
 have hk:E y ≤ Re * (ξ/Ls):= h'.trans_eq (by unfold ξ Ls; ring)
 let T:= S y; have hs : Rt*(ξ/Ls) ≤ h^2*T:= by apply hB.trans' (le_of_eq ?_); unfold ξ Ls; ring
 let α:= aimC K.j e; have ha:0 ≤ α:=aimC_p e; let Eρ:= Real.exp (-(mstar Rℓ:ℝ)); let c:= E y; have hξ: 0 ≤ ξ:= g.2.2.1.le; have hκ:=div_nonneg hξ hh.le
 constructor
 · change α*(Eρ*c/h^2) ≤ _; rw [←mul_div_assoc]; apply (div_le_iff₀ (pow_pos (show 0<h from zero_lt_one.trans_le hp) 2)).mpr
   suffices α*(Eρ*c) ≤ T/256*h^2 from this
   calc _ ≤ α*(Eρ*Re)*(ξ/Ls):=(mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le) ha).trans_eq (by ring)
        _ ≤ Rt/256*(ξ/Ls):= mul_le_mul_of_nonneg_right fx.wave hκ
        _ ≤ _:=by linarith
 have hc:0 ≤ c:=by
    unfold c; rw [beam_eq (s:=s) (e:=e)]; unfold houseP; have hv: 0≤εp R Pay pW.C y:= (sq_nonneg _).trans H; exact mul_nonneg (add_nonneg ht.2.2 (by norm_num)) (mul_nonneg ht.2.1.le (add_nonneg hv (sq_nonneg _)))
 refine (reachX e hc).trans ((mul_le_mul_of_nonneg_left hk (issue_pos (Aχ:=Aχ) e).le).trans ?_)
 have hhB: issueK K Aχ e * Re ≤ Ls / 16000 := by linarith only [fx.regular]
 rw [←mul_assoc]; refine (mul_le_mul_of_nonneg_right hhB hκ).trans_eq ?_
 unfold ξ εLeaf; field
end Focus
end Pitching
end YM.CF.Py.Rate
