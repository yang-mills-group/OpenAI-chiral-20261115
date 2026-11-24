import YM.CF.Vp929.Stage.Escrow
import YM.SU5.FiniteGaugeData.Reliance.Firm
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
/-- C profile on requests from the actual prescription -- sufficient to make *level* pressure
 (after leading log subtraction) O(1) per site UNIFORMLY in level. y is the next step's y. -/
def capCost (R:Patch)(x a:ℝ) := let h:= (R.L.val:ℝ)^4; let v:= Scales.y SU.group R.L x; -(3*(h-1))* Window.strengthLog (coupling v) + h * a

def CapLaw (R:Patch)(C:ℝ→ℝ)(b:ℝ): Prop := 0 < b ∧ ∀ᶠ x in atTop, C x ≤ capCost R x b
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
private lemma toll {C':ℝ}(v: |Corne.arcD Jq x Y1| ≤ Fintype.card (Site (Domain n B))*C')(T:Weather C Z0 pW γq): |Real.log ‖Gρ‖|≤Fintype.card (Site (Domain n B))*(C'+ |c.height|):=by
 unfold pulseZ; rw [Complex.norm_exp,Real.log_exp,Complex.sub_re,Complex.ofReal_re,mul_add]; refine (abs_sub ..).trans (add_le_add v ((Complex.abs_re_le_norm _).trans ?_)); exact (Earn.bankCurrency V (X:=ps) (Y:=Oc) o.SheepR (near_j w.G d W.health).self_of_nhds).trans (mul_le_mul_of_nonneg_left (le_abs_self o.SheepR.height|>.trans_eq (congrArg _ T.layout.cloth)) (by positivity))
private lemma upper_chunk (z:ℝ)(p:1 ≤ z) : Window.strengthLog (coupling z) ≤ 0 := by
 have he: coupling z≤1:= inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt p)
 exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (Real.log_nonpos (coupling_pos (zero_lt_one.trans_le p)).le he)
-- explicitly negative leading fee = pad formula on ζ with extent Λ, used at EVERY support next-level
private lemma believable {u v Z:ℝ}(p:0≤v)(q:v ≤ u)(d:Z ≤ 0)(x x' k W:ℝ)(h₁:x≤k)(h₂:x'≤k)(h₄:3*(u-v)*Z-x*u≤W)(h₅:W≤3*(u-v)*Z+x'*u): |W|≤ -(3*(u-v)*Z-k*u):=by
 have he:= p.trans q; have hz:= mul_nonpos_of_nonneg_of_nonpos (b:=Z) (show 0 ≤ 3*(u-v) by linarith) d
 rw [abs_le]; exact ⟨by linarith only [h₄,mul_le_mul_of_nonneg_right h₁ he],by linarith only [h₅,hz,mul_le_mul_of_nonneg_right h₂ he]⟩

open Jade.Earn
private lemma glove (e:β∈ Year R x)(ep:1 ≤ (Scales.y SU.group R.L x)) {c1 c2 c3:ℝ}(v: |Corne.arcD Jq x Y1| ≤ Fintype.card (Site (Domain n B))*c3)(T:Weather C Z0 pW γq)
 (K₁: ∀ i:ℝ, 1 ≤ i → Real.exp (pathFees (Domain m B) (Domain n B) (Scales.y SU.group R.L x) c1) ≤ prefactor S' G5 β * (shotM L i β)^Fintype.card Y1.park.Free)
 (K₂:∀ i:ℝ, 1 ≤ i → prefactor S' G5 β * (shotM L i β)^Fintype.card Y1.park.Free ≤ Real.exp (pathFees (Domain m B) (Domain n B) (Scales.y SU.group R.L x) (-c2))) : |Real.log ‖retail (F:=F) (Z0:=Z0) Y1 e‖|≤ capCost R x (max c1 c2+(c3+|c.height|))*sites ι:=by
 let W' := Fintype.card (Site (Domain n B)); have hW:(W':ℝ)=R.L.val^4*sites ι:=by
    unfold W'; rw [site_card]; change (↑((Domain n B).val^4):ℝ)=_; rw [w.sizes]; simp only [Nat.cast_mul,Nat.cast_pow]; unfold sites; change _= _* ((Domain m B).val:ℝ)^4; ring
 have hv: (Fintype.card (Site (Domain m B)):ℝ)=sites ι:= by rw [site_card,Nat.cast_pow]
 let U:= roomSite (Domain n B); let v':= roomSite (Domain m B); have h1:v'=sites ι:= hv
 have h2:U=R.L.val^4*sites ι:=hW
 let H:= (Z0.toLid.ZoomB e).hat R x; have hH:1≤H:= coast Z0.toLid C e
 have hs: 0< shotM L H β ^ Fintype.card Y1.park.Free:= pow_pos (mul_pos (spare_pos _ D.localPrice (Z0.toLid.pos e)) (point_p (lt_of_lt_of_le zero_lt_one (coast Z0.toLid C e)))) _
 have ht:0<prefactor S' G5 β:= prefactor_pos ..; have hu: Gρ≠0:= Complex.exp_ne_zero _
 unfold retail; rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg ht.le,Real.norm_of_nonneg hs.le,Real.log_mul (mul_pos ht hs).ne' (norm_pos_iff.mpr hu|>.ne')]; let G:= Real.log (prefactor S' G5 β * (shotM L H β)^Fintype.card Y1.park.Free)
 let X':=Scales.y SU.group R.L x; let Z':= Window.strengthLog (coupling X')
 have hG: |G| ≤ -(3*(U-v')*Z'-max c1 c2*U):=by
    refine believable (by unfold roomSite; positivity) (builtLe (w.step V)) (upper_chunk X' ep) c1 c2 _ _ (le_max_left ..) (le_max_right ..) ?_ ?_
    · apply le_trans ?_ (Real.log_le_log (Real.exp_pos _) (K₁ H hH)); rw [Real.log_exp]
    refine (Real.log_le_log (mul_pos ht hs) (K₂ H hH)).trans ?_; rw [Real.log_exp]; change 3 * (U-v') * Z' - (-c2)*U ≤ _; exact le_of_eq (by ring)
 change |G+Real.log ‖_‖|≤ _; exact (abs_add_le ..).trans ((add_le_add hG (toll (F:=F) Y1 v T)).trans_eq (by change -(3*(U-v')*Z'-max c1 c2*U)+U*(c3+|c.height|)=_; rw [h1,h2]; unfold Z' X' capCost; ring))

-- D version: spend Treaty.I chosen already, independent of h and exact aperture.
theorem strictEscrow (V:Grace K R L)(L₀:LocalRatio L):
    ∃ d:ℝ,0 < d ∧ ∀ {u:ℝ}{B:Side}{P:Grasp V.U B u}{W:GivenX V P}{N:Side}{J:Robes N V W}{q:Chi}{A C' Pay h ρ:ℝ} (D:Treaty J q A C' Pay h ρ)(c: Estimate),∀ᶠ x:ℝ in atTop,∀ m n w (o:Pitching (m:=m) (n:=n) w D x) p p' ag Cg κq Bv nₐ N0 (Z0:Cellar N0 o p p' c (allF R.L x) ag Cg)(C:stationary D c x ag Cg κq Bv nₐ)(pW:WindV K.j 2)(γq:ℝ),Weather C Z0 pW γq → ∀ Y1: Monk SU.group (w.step V),BudgetLaw Z0 (capCost R x (d+|D.I.pay|)) Y1:=by
 let O:=Classical.choice (YM.Next.Rank.exists_budget SU.group)
 obtain ⟨u,h1,ψ₁⟩:= Jade.Earn.treasury L O K.bind L₀; obtain ⟨v,h2,ψ₂⟩:= Jade.Earn.Reliant.estimate L O K.bind L₀
 obtain ⟨z,hz,h⟩:=Jade.Earn.bankDetBoth V.L.cloth
 refine ⟨max u v+z,by positivity,?_⟩
 intro u₁ B P W N J q A C' Pay h' ρ D c
 filter_upwards [h,(Scales.year SU.group R.L).eventually_ge_atTop 1] with x t p m n w o pA pB ag Cg κq Bv nₐ N0 Z0 C P γq T Y1
 constructor; intro b F _ v
 have he:c.height=D.I.pay:= T.layout.cloth.symm.trans (congrArg Stake.Isle.pay o.id)
 rw [←he, add_assoc]; refine glove (F:=F) Y1 v p (t (w.step V) Y1 _ (Z0.request.statv b F 0 0 v).hunt.cert) T (fun i t'=> ψ₁ (w.step V) Y1 rfl i (Scales.y SU.group R.L x) b t' (zero_lt_one.trans_le p) v.1 v.2) (fun i t'=> ψ₂ (w.step V) Y1 rfl i (Scales.y SU.group R.L x) b t' p v.1 v.2)
end
end Focus
end Pitching
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Pitching.Focus.strictEscrow
