import YM.SU5.FiniteGaugeData.Pannier.PerRoot
/-!
# Amortized offset budget from stencils of the step Shop.
Retains the constants through choice of h. Adapted from `Pitching.Focus.escrow`. -/

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
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'

open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
open Engine Engine.Basin Engine.Docket Dialect
local notation "T_"=> Troupe S' z' (Words S')
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "De"=> T_→ Lo→ Raid D'
local notation "PZ"=> T_→Lo→ Orbit ι→ Cipher ι
local notation "oWell"=> o.muster
local notation "Loχ"=> Palot.leaf (Site (Domain m B))
local notation "Px"=> V_→Loχ→ Orbit ι→ Cipher ι
local notation "Kx"=> V_→ Loχ→ Raid (Scree.Dwell ι)
open Vow Bake Salt Stax Sour Larch
local notation "Θ'" t:max=> (cook S' (Finset.toLeft t)).flags
local notation "δ_"=> (cipherK J.n)
local notation "U_"=> (fullD (n:=ι))
variable {t bL σ κ Bv:ℝ}{nₐ:ℕ}{pW:WindV K.j 2}
variable {Z:Cellar N0 o p p' c f ag Cg} {M:Climate D.pilot R c x t bL σ κ ag Cg Bv nₐ}
namespace Focus
variable (Uq:Focus Z M pW ff)(Ty:Ids (Scree.mid m B))
local notation "Upp"=> ((tolQ p).supportExponent)
variable (Q:β∈ Year R x)(hF:Charged p' w.input K.j R.L.val h f F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> Xs β
local notation "F_"=> (Z.toLid.crew β Q).1
local notation "A0"=> (Z.toLid.choice Q (gross_shape hF (le_refl f)))
variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}
open Appel.Rate Stockpile
variable {κq γq:ℝ}
section
local notation "FΩ"=> (allF R.L x)
local notation "Ef"=> εLeaf R.L x
local notation "Λ"=> thinR R x
variable {C:stationary D c x ag Cg κq Bv nₐ}{Z0:Cellar N0 o p p' c (allF R.L x) ag Cg}(T:Weather C Z0 pW γq)(Vq:Rill.Arch w.G d)(hv:Vq.val=1)
local notation "βΛ"=> Ledge nₐ (dwidth R x) (Scales.y SU.group R.L x)
local notation "Tρ"=> εp R Pay pW.C x
local notation "ψ"=> pre_Phi Z0
local notation "E_s"=> sprayM D.pilot R ag x
local notation "Aρ"=> τa R c x κq (sprayM D.pilot R ag x) h Pay γq
local notation "mK"=> τk R c x κq (sprayM D.pilot R ag x)
local notation "mF"=> τp R c x κq (sprayM D.pilot R ag x)
local notation "PE"=> Pre_T (Z:=Z0) Ty Vq
local notation "PA"=> Pre_A (Z:=Z0) Ty Vq
open Next.Fluctuations.Sector
variable {r b0 b1 b2:ℝ} [Nonempty (Haro.ΘS r)]
variable {Xv:Cusp (mid m B)} (pB:Client K R x w.input p' h (β:ℂ) (F,0))(Ω:Stakehouse (h:=h) p J w b0 b1 b2 r)
local notation "art"=> (articles (Z0:=Z0) Ty Vq)
local notation "Πζ"=> (T.member (matured Ty T Vq hv _ pB).1 pB.1)
local notation "Zq"=> (Z0.toLid)
local notation "Oc"=> (Ys β F)
local notation "ps"=> (Xs β)
local notation "γY"=> (β+w.movement V)
local notation "ηΧ"=> (V.L.path (w.lag+1))
local notation "κ'"=> K.top.clip
local notation "Up'" v:max=> w.step V
variable (Y1: Monk SU.group (w.step V))
local notation "Gρ"=> pulseZ (T:=(w.Φ (V:=V))) (x:=x) (U:=U) (H₀:=Oc) (G:=w.G) (H₁:=ps) Y1
local notation "y"=> (Scales.y SU.group R.L x)
open Rate.Pannier
include o in
private lemma paleroot {C':ℝ}(v: |Corne.arcD Jq x Y1| ≤ Fintype.card (Site (Domain n B))*C') : |Real.log ‖Gρ‖|≤Fintype.card (Site (Domain n B))*(C'+ |D.I.pay|):=by
 unfold pulseZ; rw [Complex.norm_exp,Real.log_exp,Complex.sub_re,Complex.ofReal_re,mul_add]; refine (abs_sub ..).trans (add_le_add v ((Complex.abs_re_le_norm _).trans ?_)); exact (Earn.bankCurrency V (X:=ps) (Y:=Oc) o.SheepR (near_j w.G d W.health).self_of_nhds).trans (mul_le_mul_of_nonneg_left (le_trans (eq_of_he) (le_abs_self D.I.pay)) (by positivity)) -- height
where eq_of_he : o.SheepR.height ≤ D.I.pay:= Eq.le (congrArg Stake.Isle.pay o.id)
-- (b in Year) prices are converted to the strip parameter `y=Scales.y` not bare beta
abbrev cantilever (P:Patch) (V x:ℝ) := ((P.L.val:ℝ)^4-1)*3*(halfLie SU.group*Real.log (Scales.y SU.group P.L x))+V
private lemma invest (a V B C N L Q : ℝ) (hb: |B+a| ≤ bL) (hc:|C+a|≤σ) (hd:|Q| ≤ V*L) (c:0≤N)(f:N ≤ L)
    : |-(4*N)*B+(3*L+N)*C+Q+(3*(L-N))*a| ≤ 4*N*bL+(3*L+N)*σ+V*L:= by
 have h:(0:ℝ)≤3*L+N:=by linarith
 rw [abs_le] at hb hc hd ⊢; constructor <;> nlinarith only [hd.1,hd.2,mul_le_mul_of_nonneg_left hb.1 c,mul_le_mul_of_nonneg_left hb.2 c,mul_le_mul_of_nonneg_left hc.1 h,mul_le_mul_of_nonneg_left hc.2 h]
-- subtract y-logs in both prefactors, keep them for the leading term.
private lemma harvested (e:β∈ Year R x){c1 c2 c3 : ℝ} (h:1 ≤ Scales.y SU.group R.L x)
    (v: |Corne.arcD Jq x Y1| ≤ Fintype.card (Site (Domain n B))*c3)
    (p: |Real.log ( (w.step V).penaltyZ β G5) + halfLie G5 * Real.log (Scales.y SU.group R.L x)| ≤ c1)
    (q: ∀ z≥ (1:ℝ), |Real.log (shotM L z β) + halfLie G5 * Real.log (Scales.y SU.group R.L x)| ≤ c2)
    (T:Weather C Z0 pW γq): |Real.log ‖retail (F:=F) (Z0:=Z0) Y1 e‖| ≤ cantilever R (4*c1+(3*(R.L.val:ℝ)^4+1)*c2+(R.L.val:ℝ)^4*(c3+|D.I.pay|)) x *sites ι := by
 let N : ℝ:= sites ι
 have hN: (Fintype.card (Site (Domain m B)):ℝ) = N:= by rw [site_card,Nat.cast_pow]
 let ℓ := Fintype.card (Site (Domain n B)); have hW:(ℓ:ℝ)=(R.L.val:ℝ)^4*N:=by
    unfold ℓ; rw [site_card]; change (↑((Domain n B).val^4):ℝ)=_; rw [w.sizes]; simp only [Nat.cast_mul,Nat.cast_pow]; unfold N sites; change _= _* ((Domain m B).val:ℝ)^4; ring
 let H:= (Z0.toLid.ZoomB e).hat R x; have hcoast:= coast Z0.toLid C e; have hs: 0< shotM L H β ^ Fintype.card Y1.park.Free:= pow_pos (mul_pos (spare_pos _ D.localPrice (Z0.toLid.pos e)) (point_p (lt_of_lt_of_le zero_lt_one hcoast))) _
 have ht:0<prefactor S' G5 β:= prefactor_pos ..; have hu: Gρ≠0:= Complex.exp_ne_zero _
 unfold retail; rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht.le,Real.norm_of_nonneg hs.le,Real.log_mul (mul_pos ht hs).ne' (norm_pos_iff.mpr hu|>.ne'), Real.log_mul ht.ne' hs.ne',prefactor,Real.log_pow,Real.log_inv,Real.log_pow]
 let V₀:= c3+|D.I.pay|; let Q:=Real.log ‖Gρ‖; let Ayy:=Real.log ((w.step V).penaltyZ β G5); let X':= Real.log (shotM L H β)
 let a:= halfLie G5 * Real.log (Scales.y SU.group R.L x); have ha:0≤a:= mul_nonneg (pen_log_nonneg G5) (Real.log_nonneg h)
 change |_ * (-Ayy) + _ * X' + Q| ≤ cantilever _ (4*c1+(3*↑R.L.val^4+1)*c2+↑R.L.val^4*V₀) x * N
 rw [thinWireCount _,show Fintype.card (Edge (Site (Domain m B))) = Fintype.card (Site (Domain m B))*4 from (Fintype.card_prod ..).trans (by rfl)]; push_cast; rw [hN]
 have hd:0≤N:= hN ▸ (Nat.cast_nonneg (α:=ℝ) _)
 have hl:N≤(ℓ:ℝ):= hN ▸ Jade.Earn.builtLe (w.step V)
 -- absolute estimate; for lower-offset prefer both as in escrow
 have hj:= invest a V₀ Ayy X' N ℓ Q p (q H hcoast) (by rw [mul_comm V₀]; exact paleroot (o:=o) Y1 v) hd hl
 unfold cantilever; change |N*4* (-Ayy)+ (3*ℓ+N)*X'+Q| ≤ (( (R.L.val:ℝ)^4-1)*3*a+ (4*c1+(3*(R.L.val:ℝ)^4+1)*c2+(R.L.val:ℝ)^4*V₀))*N
 rw [abs_le] at hj ⊢
 change -(4*N*c1+(3*ℓ+N)*c2+V₀*ℓ)≤ _ ∧ _ ≤ _+V₀*ℓ at hj
 -- denominator at V₀ not syntatic fix.
 constructor
 · have hz:= hj.1; rw [hW] at hz ⊢; nlinarith only [hz]
 have hz:= hj.2; have hm:= mul_le_mul_of_nonneg_right hl ha; rw [hW] at hm hz ⊢; nlinarith only [hz,hm]

lemma escrow_telescope_prepare (V : Grace K R L)(H:LocalRatio L)(I : Stake.Isle) : ∃ V₀> (0:ℝ),∀ (A C' Pay h ρ:ℝ)(N B:Side)(q:Chi)(d:ℝ)(U:Grasp V.U B d)(W: GivenX V U)(J:Robes N V W)(D:Treaty J q A C' Pay h ρ), D.I=I → ∀ (c:Estimate), ∀ᶠ x:ℝ in atTop,
    ∀ (m n:Side) (w:Location (R:=R) B m n)(o:Pitching w D x)(p p':BudgetPoint)(ag Cg κq Bv:ℝ)(nₐ N0:ℕ) (Z0:Cellar N0 o p p' c (allF R.L x) ag Cg)(C:stationary D c x ag Cg κq Bv nₐ)(pW:WindV K.j 2)(γq:ℝ),Weather C Z0 pW γq → ∀ Y1: Monk SU.group (w.step V),BudgetLaw Z0 (cantilever R V₀ x) Y1:=by
 obtain ⟨z,hz,h⟩:= Jade.Earn.bankDetBoth V.L.cloth
 obtain ⟨c1,t1,V1⟩:= heatmark L H K.bind
 obtain ⟨c2,t2,V2⟩:= flake_cost L H
 let V₀:= 4*c1+(3*(R.L.val:ℝ)^4+1)*c2+(R.L.val:ℝ)^4*(z+|I.pay|)
 refine ⟨V₀,by unfold V₀; positivity,?_⟩
 intro A C' Pay Hh ρ N B q d U W J D hp Q
 subst I
 filter_upwards [h,(Scales.year SU.group R.L).eventually_ge_atTop 1,(Scales.year SU.group R.L).eventually V1] with x hu hv hh m n w o p p' ag Cg κq Bv nₐ N0 Z C P γq T Y1
 constructor; intro b F _ e
 exact harvested Y1 e hv (hu (w.step V) Y1 _ (Z.request.statv b F 0 0 e).hunt.cert) (hh b e (w.step V) rfl) (V2 _ (zero_lt_one.trans_le hv) b e) T
noncomputable def mintPressure (V : Grace K R L)(H:LocalRatio L)(I : Stake.Isle):= (escrow_telescope_prepare V H I).choose
lemma mintPressure_pos (V : Grace K R L)(H:LocalRatio L)(I : Stake.Isle):0 < mintPressure V H I:= (escrow_telescope_prepare V H I).choose_spec.1
end
end Focus
end Pitching
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pitching.Focus.escrow_telescope_prepare
