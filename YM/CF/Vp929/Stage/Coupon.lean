import YM.CF.Vp929.Stage.Factory
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
local notation "κs"=> priceB k_

abbrev couponX (K:Teller SU.group)(R:Patch)(z:1≤K.j)(Aχ Γχ r:ℝ)(x:ℝ): ℝ:= r+priceXU K.top.clip K.j z R.L.val (epoch x) r (shipA (epoch x) R.L.val K.top.clip K.below.width K.below.paths Aχ)
abbrev couponY (K:Teller SU.group)(R:Patch)(z:1≤K.j)(Aχ Γχ r:ℝ)(x:ℝ): ℝ:= |priceYT K.top.clip K.j z R.L.val (epoch x) r (shipT (epoch x) R.L.val K.top.clip K.below.width K.below.paths Aχ Γχ)|
abbrev issueK(K:Teller SU.group)(Aχ:ℝ)(z:1≤K.j):= 1+(1+|Ione.wren_K 6 2|)* (|u_early| *aimC K.j z)+priceB K.top.clip*earlyA K.top.clip K.below.width K.below.paths Aχ
local notation "κI"=> issueK K Aχ e
private lemma κsn :0 ≤ κs:=by unfold priceB; have h:= posed k_; positivity
lemma issue_pos : 0 < issueK K Aχ e:=by unfold issueK; have t:=κsn (K:=K); have u:=earlyA_pos k_ κσ κL Aχ; have h:=aimC_p e; positivity
variable (s:Major V Wk b0 b1 b2 b3 Aχ Γχ n₀)
include e
lemma reachX (t:0 ≤ r) : couponX K R e Aχ Γχ r x ≤ issueK K Aχ e*r:=by
 let ξ:= mstar R1; let p:=epoch x; let u:= aimC K.j e; have eu:Real.exp (- (ξ:ℝ)) ≤1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
 obtain ⟨x₁,t₁,e₁⟩:= (show p.order=6 ∧ p.power=2 ∧ p.supportExponent=1 from let_X HI x)
 have he: Real.exp (ξ:ℝ)*Real.exp (-(ξ:ℝ))=1:=by rw [←Real.exp_add,add_neg_cancel, Real.exp_zero]
 let T:= priceU K.j e R1 r
 let α:= |u_early| *u
 have v:0≤p.threshold:=p.threshold_pos.le
 let W:=wren_K 6 2; have ht: profitX T p R1 ≤ (1+|W|)*(α*r):=by
    have ha:0 ≤ u:=aimC_p e
    unfold profitX; rw [x₁,t₁,e₁,one_mul]; unfold T priceU; change _ + W * (Real.exp (ξ:ℝ)*(|u_early| * (u*(Real.exp _*r))))≤_
    have hh: Real.exp (ξ:ℝ)* (|u_early| * (u*(Real.exp (-(ξ:ℝ))*r))) = α*r:=by
       calc _ = |u_early| * u *((Real.exp (ξ:ℝ)*Real.exp (-(ξ:ℝ)))*r):=by ring
            _ =_:=by rw [he,one_mul]
    rw [hh, show (1+|W|)*(α*r)=α*r+|W| *(α*r) from (by ring)]; refine add_le_add ?_ (mul_le_mul_of_nonneg_right (le_abs_self W) (show 0 ≤ α*r from (by unfold α; positivity))); refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right eu t) ha) (abs_nonneg _)) (le_of_eq ?_); unfold α u; ring
 let C:=rollFX k_ p R1 r; have hs:=κsn (K:=K); have hp:0 ≤ C:=by unfold C rollFX; positivity
 have hh:C*|Xτ x|≤ (κs*earlyA k_ κσ κL Aχ)*r:=by
    refine le_trans (mul_le_mul_of_nonneg_left (kit_early k_ κσ κL Aχ p x₁ t₁ e₁ R1) hp) (le_of_eq ?_)
    have hx: p.threshold≠0:=p.threshold_pos.ne'; unfold C rollFX; unfold ξ at he; rw [Real.exp_neg]; field
 change r+(profitX T p R1+C* _)≤_; exact (add_le_add (le_refl r) (add_le_add ht hh)).trans_eq (by unfold W α u issueK; ring)

local notation "pX"=> fun i:ℝ=> cη i
local notation "aT"=> κF
include s
lemma beam_eq : houseP (epoch x) K Aχ Γχ r = houseP HI K Aχ Γχ r:=by
 unfold houseP; obtain ⟨h,t,q⟩:= let_X HI x; have hx:tax_E (epoch x) k_ κσ κL Aχ Γχ=tax_E HI k_ κσ κL Aχ Γχ:= spend_T HI _ _ _ _ _ (epoch x) h t q
 rw [hx]
lemma Chill_a : Chill_v (Fp pX)∧ sizeK R.L 2 pX:=by
 obtain ⟨hx,ht⟩:= (show sizeK R.L 2 aT ∧ Chill_v (Fp aT) from bud_f)
 let A:= tax_E HI k_ κσ κL Aχ Γχ+1
 have hh: pX=fun x:ℝ=> A * aT x:= by funext x; exact beam_eq (s:=s) (e:=e)
 rw [hh]; refine ⟨?_ , hx.scale _⟩
 apply Chill_v.trend (ht.cheap A); filter_upwards with i; unfold Fp; exact Eq.le (congrArg (|·|) (mul_div_assoc _ _ _))
local notation "FT" c:max=> (fun x:ℝ=> rollFX k_ (epoch x) R1 (c x))
local notation "Wu"=> aT

lemma chill_FX : Chill_v (FT (pX)):= by
 let Hp:= (Chill_a (R:=R) (C':=C') (Pay:=Pay) e s).1
 apply (Hp.cheap (κs*Real.exp ξt)).trend; filter_upwards [purse_K HI K.top s.direct] with x t; dsimp only [rollFX,Fp]; rw [show (epoch x).threshold=temp x from t.1]; exact Eq.le (congrArg _ (by ring))
lemma chill_Y : Chill_v fun i:ℝ=> couponY K R e Aχ Γχ (cη i) i := by
 let t(x:ℝ):= epoch x; let D:= Extension.yard R1; let H(x:ℝ):= (epoch x).order; let B(x:ℝ):= Larch.tet_B D (t x).B; have hB: BoreP B:=by simpa only [B,D,t,mul_one] using mist (b:=k_) (σ:=κσ) (C:=κL) (α:=Aχ) 1 R1
 let Z:= pX
 let F:= priceB k_; let A:= aimC K.j e; let U:= A*Real.exp ξt; let X(x:ℝ):= priceU K.j e R1 (Z x); let pA:= Chill_v.coin ((Chill_a e s (Pay:=Pay) (C':=C')).2.low (k:=1) (by norm_num)); have eU: Chill_v X:= by apply (pA.cheap (|u_early| *U)).trend; filter_upwards with i; unfold X priceU U Z A; exact Eq.le (congrArg _ (by ring))
 let Cz(x:ℝ):=|Tτ x|; let α:= Ione.pack_Q 6*(Larch.shine_C D (1+1+1)*Vow.chi_f 6); let G:= fun x:ℝ=> profitY (X x) (t x) R1; have hG: Chill_v G:=by
    apply ((eU.leanB hB).cheap α).trend; filter_upwards with x; unfold G; change |profitY _ _ _| ≤ _; unfold profitY t Extension.wagon Cash.prominence; obtain ⟨e,x₁,t₁⟩:= (show (epoch x).order=6∧ (epoch x).power=2 ∧ (epoch x).supportExponent=1 from let_X HI _); rw [e,t₁]; unfold α B D t; exact Eq.le (congrArg _ (by ring))
 have he:BoreP Cz:=(accountBore k_ κσ κL Aχ R1 Γχ).tune (Eventually.of_forall fun x=> by unfold Cz; rw [abs_abs])
 apply (hG.noteR ((chill_FX e s (Pay:=Pay) (C':=C')).leanB he)).trend; filter_upwards with i; unfold Cz; change abs |G i+ _*_|≤ _
 rw [abs_abs,mul_comm _ (|Tτ i|)]
end Focus
end Pitching
end YM.CF.Py.Rate
