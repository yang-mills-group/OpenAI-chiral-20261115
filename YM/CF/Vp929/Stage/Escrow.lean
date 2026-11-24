import YM.CF.Vp929.Stage.Oar
import YM.CF.Vp929.Stage.Clothes
import YM.CF.Continuum.Trips
import YM.CF.Continuum.Beluga
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
private lemma axisCount (R:Side): Fintype.card (Edge (Site R)) = Fintype.card (Site R)*4:= (Fintype.card_prod ..).trans (by rfl)
-- geometry-independent px, coarse to fine sites. single-link penaltyZ. Proof via arbitrary same-kernel representative.
private lemma prefixBound (R:Patch)(X:KernelChoices)(C: Set ℝ)(h:IsCompact C) : ∃ V:ℝ,0≤V ∧∀ {c f:Side}(S:StepData c f),S.kernel=X→∀ b∈C,|Real.log (prefactor S G5 b)|≤ Fintype.card (Site f)*(4*V):=by
 let Z: StepData (1:Side) R.L:= ⟨R,X,by simp⟩
 have hc:Continuous fun s=>|Real.log (Z.penaltyZ s G5)|:= ((Push.BetaTransport.penaltyZ_cont Z G5).log (fun i=>(Z.penaltyZ_pos ..).ne')).abs
 obtain ⟨c0,t⟩:= (h.image hc).bddAbove; refine ⟨|c0|,abs_nonneg _,?_⟩; intro c f S hs b v
 unfold prefactor; rw [Real.log_pow,Real.log_inv,abs_mul,abs_neg,abs_of_nonneg (by positivity : (0:ℝ)≤ Fintype.card (Edge (Site c)))]

 have he:S.penaltyZ b G5=Z.penaltyZ b G5:=by unfold StepData.penaltyZ StepData.penaltyWeight; rw [hs]
 have hg: |Real.log (S.penaltyZ b G5)|≤|c0|:=he ▸ (t ⟨b,v,rfl⟩).trans (le_abs_self _)
 have hM: (Fintype.card (Site c):ℝ)≤Fintype.card (Site f):= Jade.Earn.builtLe S
 rw [axisCount]; push_cast
 exact (mul_le_mul (mul_le_mul_of_nonneg_right hM (by norm_num : (0:ℝ) ≤ 4)) hg (abs_nonneg _) (by positivity)).trans_eq (by ring)
private lemma runway (M0:ChartRatio SU.group)(p:LocalRatio M0){b U:ℝ}(u:0< b)(hu:1 ≤ U) :∃ V:ℝ,0≤ V ∧ ∀ s∈Set.Icc (b/2) (2*b),∀ T'∈Set.Icc 1 U, |Real.log (shotM M0 T' s)|≤ V:=by
 let A:=Set.Icc (b/2) (2*b); let H:=Appel.point SU.group 1; let H':= Appel.point SU.group U; have ht (z:ℝ)(e:z∈A):0<z:= lt_of_lt_of_le (half_pos u) e.1
 have hg:ContinuousOn (fun z=>|Real.log (spare M0 z)|) A:=by
    have hp:ContinuousOn coupling A:= Real.continuous_sqrt.continuousOn.inv₀ (fun i w=>(Real.sqrt_pos.mpr (ht i w)).ne'); refine (ContinuousOn.log ?_ (fun i w=>(spare_pos M0 p (ht i w)).ne')).abs; unfold spare; exact ((Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul (hp.pow 2))).pow _).mul continuousOn_const
 obtain ⟨c,t⟩:=(isCompact_Icc.image_of_continuousOn hg).bddAbove; refine ⟨|c|+(|Real.log H|+|Real.log H'|),by positivity,?_⟩
 have hp (u v:ℝ)(w:u≤v): Appel.point SU.group u≤Appel.point SU.group v:= ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (closedBall_subset_closedBall w))
 intro i j s w; let h:= Appel.point SU.group s; have hH:0<H:=point_p (by norm_num); have h': H≤h:= hp _ _ w.1; have he:h≤H':= hp _ _ w.2
 have h₀:=hH.trans_le h'
 rw [shotM,Real.log_mul (spare_pos M0 p (ht i j)|>.ne') h₀.ne']; refine (abs_add_le ..).trans (add_le_add ((t ⟨i,j,rfl⟩).trans (le_abs_self _)) ?_)
 change |Real.log h|≤_; rw [abs_le]; have ha:= Real.log_le_log hH h'; have hb:=Real.log_le_log h₀ he; constructor <;> linarith [neg_abs_le (Real.log H),le_abs_self (Real.log H'),abs_nonneg (Real.log H),abs_nonneg (Real.log H')]

private lemma shoots (fζ:ℝ)(hp:0 ≤ fζ)(u:∀ b∈Year R x,∀ z∈Set.Icc 1 (D.pilot.hat R x), |Real.log (shotM L z b)|≤fζ)(hb:β∈Year R x) (T:Weather C Z0 pW γq): let H:= (Z0.toLid.ZoomB hb).hat R x; |Real.log (shotM L H β ^ Fintype.card Y1.park.Free)|≤ Fintype.card (Site (Domain n B))*(4*fζ):=by
 have ht:=u β hb ((Z0.toLid.ZoomB hb).hat R x) ⟨coast Z0.toLid C hb,by rw [Z0.toLid.hat']; have t:=mul_le_mul_of_nonneg_right (Z0.toLid.rune_enroll hb).2 (show 0 ≤ D.pilot.hat R x/2 from Z0.toLid.park.le); linarith only [t]⟩
 intro H; rw [Real.log_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤ Fintype.card Y1.park.Free)]
 have he:Fintype.card Y1.park.Free ≤ Fintype.card (Site (Domain n B))*4:= by
    rw [←axisCount]; exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
 refine (mul_le_mul (show (Fintype.card Y1.park.Free:ℝ)≤ (Fintype.card (Site (Domain n B)):ℝ)*4 by exact_mod_cast he) ht (abs_nonneg _) (by positivity)).trans_eq ?_; ring
private lemma toll {C':ℝ}(v: |Corne.arcD Jq x Y1| ≤ Fintype.card (Site (Domain n B))*C')(T:Weather C Z0 pW γq): |Real.log ‖Gρ‖|≤Fintype.card (Site (Domain n B))*(C'+ |c.height|):=by
 unfold pulseZ; rw [Complex.norm_exp,Real.log_exp,Complex.sub_re,Complex.ofReal_re,mul_add]; refine (abs_sub ..).trans (add_le_add v ((Complex.abs_re_le_norm _).trans ?_)); exact (Earn.bankCurrency V (X:=ps) (Y:=Oc) o.SheepR (near_j w.G d W.health).self_of_nhds).trans (mul_le_mul_of_nonneg_left (le_abs_self o.SheepR.height|>.trans_eq (congrArg _ T.layout.cloth)) (by positivity))
private lemma amortize (e:β∈ Year R x){c1 c2 c3:ℝ} (v: |Corne.arcD Jq x Y1| ≤ Fintype.card (Site (Domain n B))*c3)(t: |Real.log (prefactor S' G5 β)|≤ Fintype.card (Site (Domain n B))*c1)(hp:0≤c2)(u:∀ b∈Year R x,∀ z∈Set.Icc 1 (D.pilot.hat R x), |Real.log (shotM L z b)|≤c2) (T:Weather C Z0 pW γq): |Real.log ‖retail (F:=F) (Z0:=Z0) Y1 e‖|≤ (↑R.L.val ^4*(c1+4*c2+(c3+|c.height|)))*sites ι:=by
 let W' := Fintype.card (Site (Domain n B)); have hW:(W':ℝ)=R.L.val^4*sites ι:=by

    unfold W'; rw [site_card]; change (↑((Domain n B).val^4):ℝ)=_; rw [w.sizes]; simp only [Nat.cast_mul,Nat.cast_pow]; unfold sites; change _= _* ((Domain m B).val:ℝ)^4; ring
 let H:= (Z0.toLid.ZoomB e).hat R x; have hs: 0< shotM L H β ^ Fintype.card Y1.park.Free:= pow_pos (mul_pos (spare_pos _ D.localPrice (Z0.toLid.pos e)) (point_p (lt_of_lt_of_le zero_lt_one (coast Z0.toLid C e)))) _
 have ht:0<prefactor S' G5 β:= prefactor_pos ..; have hu: Gρ≠0:= Complex.exp_ne_zero _
 unfold retail; rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht.le,Real.norm_of_nonneg hs.le,Real.log_mul (mul_pos ht hs).ne' (norm_pos_iff.mpr hu|>.ne'), Real.log_mul ht.ne' hs.ne']; refine (abs_add_le ..).trans ((add_le_add ((abs_add_le ..).trans (add_le_add t (shoots Y1 c2 hp u e T))) (toll Y1 v T)).trans_eq ?_); change (W':ℝ)*_+ (W':ℝ)*(4*c2)+ (W':ℝ)*_= _; rw [hW]; ring
/-- Offset bound from the step's prefactor, shotM, arcD, pulses.
 Use Λx for this x; any uniformity in x not needed. Moment rate given after Estimate c provision. -/
lemma escrow (D:Treaty J q A C' Pay h ρ)(c: Estimate): ∀ᶠ x:ℝ in atTop, ∃ W:ℝ,0≤W ∧∀ m n w (o:Pitching (m:=m) (n:=n) w D x) p p' ag Cg κq Bv nₐ N0 (Z0:Cellar N0 o p p' c (allF R.L x) ag Cg)(C:stationary D c x ag Cg κq Bv nₐ)(pW:WindV K.j 2)(γq:ℝ),Weather C Z0 pW γq → ∀ Y1: Monk SU.group (w.step V),BudgetLaw Z0 W Y1:=by
 obtain ⟨z,hz,h⟩:=Jade.Earn.bankDetBoth V.L.cloth
 filter_upwards [h,(Scales.year SU.group R.L).eventually_gt_atTop 0] with x h hx
 by_cases he: 1 ≤ D.pilot.hat R x
 · obtain ⟨c1,hc1,t⟩:=prefixBound R K.bind (Year R x) isCompact_Icc
   obtain ⟨c2,hc2,u⟩:=runway L D.localPrice hx he
   refine ⟨↑R.L.val^4*(4*c1+4*c2+(z+|c.height|)),by positivity,?_⟩; intro m n w o p p' ag Cg κq Bv nₐ N0 Z0 C P γq T Y; constructor; intro b F _ v
   refine amortize Y v (h (w.step V) Y _ (Z0.request.statv b F 0 0 v).hunt.cert) (t _ rfl b v) hc2 u T
 refine ⟨0,le_rfl,?_⟩; intro m n w o p p' ag Cg κq Bv nₐ N0 Z0 C P γq T; exact False.elim (he (by have ht:=C.margin; linarith))
end
end Focus
end Pitching
end YM.CF.Py.Rate
