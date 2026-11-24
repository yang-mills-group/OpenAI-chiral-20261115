import YM.SU5.Fineness.Resource
import YM.SU5.FiniteGaugeData.Pannier.Husks
set_option autoImplicit false
set_option maxHeartbeats 164000
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
open Pitching.Focus AnalyticBridge.Annulus1AD
local notation "H'"=> Pannier.halfLie SU.group
variable {P}
lemma sites_as_price (n:Side): (Fintype.card (Site (More n)):ℝ)=sites n:=by rw [site_card,Nat.cast_pow]
private lemma logDrive (M:ℝ)(z:ℝ)(p:z>0)(h:0<M): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2 ≤ a→ x/2≤b → |a-b| ≤ M → |Real.log a-Real.log b| ≤ z:=by
 filter_upwards [eventually_ge_atTop (M*2/z),eventually_gt_atTop (0:ℝ)] with x hx hp a b hA hB H; rw [abs_le] at H ⊢
 have he{a b:ℝ}(hA:x/2≤a)(hB:x/2≤b)(t:a-b≤M): Real.log a-Real.log b≤z:=by
    have ha:0<a:= lt_of_lt_of_le (half_pos hp) hA; have hb:0<b:=lt_of_lt_of_le (half_pos hp) hB
    rw [← Real.log_div ha.ne' hb.ne']; refine (Real.log_le_sub_one_of_pos (div_pos ha hb)).trans (sub_le_iff_le_add.mpr ((div_le_iff₀ hb).mpr ?_)); nlinarith only [t, (div_le_iff₀ p).mp hx, mul_le_mul_of_nonneg_right hB p.le]
 refine ⟨neg_le.mp ?_,he hA hB H.2⟩; rw [neg_sub]; exact he hB hA (by linarith only [H.1])
lemma entryFuel (Q : Grace K R L)(H: LocalRatio L) (M:ℝ)(z:ℝ)(p:z>0)(t: M>0): ∀ᶠ x:ℝ in atTop,∀ a b:ℝ,x/2≤a → x/2≤b →|a-b| ≤ M → ∀ i n F,|entryFin Q i n F a - entryFin Q i n F b|≤ z*sites n:=by
 let f:=H'+1; have hf : 0≤ H':=Pannier.pen_log_nonneg _; have he:0<f:= add_pos_of_nonneg_of_pos hf zero_lt_one; let e:= z/(3*f)
 filter_upwards [eventually_gt_atTop (0:ℝ), logDrive M e (div_pos p (by positivity)) t] with x ht hx a b ha hb hΔ i n F
 have hh:=hx a b ha hb hΔ; let W:=sites n; have hw:1 ≤ W:=sites_pos n
 have hp: entryFin Q i n F a-entryFin Q i n F b= -(H'*(Real.log a-Real.log b)* (3*(W-1))):=by
    unfold entryFin Fineness.gaugedBase; rw [spare_formula _ H.scale ((half_pos ht).trans_le ha),spare_formula _ H.scale ((half_pos ht).trans_le hb),Pannier.shadowLie, sites_as_price]; unfold W; ring
 rw [hp, abs_neg,abs_mul,abs_mul,abs_of_nonneg hf,abs_of_nonneg (show 0≤3*(W-1) by linarith only [hw])]; calc
    _ ≤ (H'*e)*(3*W):=by gcongr <;> linarith
    _ ≤ (f*e)*(3*W):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (div_nonneg p.le (by positivity))) (by positivity)
    _ = _:= (by change _=z*W; unfold e; field_simp)
lemma stage_slope (Q : Grace K R L)(x:ℝ) : Tendsto (hat R.L x) atTop atTop:=by
 have ht: 0 < billX R.L := mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1 < R.L.val by have ht:=Q.tallX; omega)))
 exact tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const ht)
variable {β:ℝ}{c:ℂ}
-- density monotonic growth; compression factor does not normalize by |Γ|
lemma height_earns (Q: Grace K R L)(B:Side) (x:ℝ) : ∀ (C q:ℝ),0 < q → ∀ᶠ i in (atTop :Filter ℕ), ∀ m, C ≤ q*sites (cell m B R.L i):=by
 intro C q h
 let a:ℝ:= R.L.val; have hp:a>1:=by unfold a; exact_mod_cast (show 1 < R.L.val by have ht:= Q.tallX; omega)
 filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hp).eventually_ge_atTop (C/q)] with i ht m
 rw [mul_comm q]; refine (div_le_iff₀ h).mp (ht.trans ?_)
 let N:=mesh m R.L i; have hh:1 ≤ ((More (cell m B R.L i)).val:ℝ):= by exact_mod_cast ((More (cell m B R.L i)).property)
 apply (le_self_pow₀ hh (by decide: (4:ℕ)≠0)).trans' -- expects 1≤ exponent
 have he:R.L.val^i ≤ N.val:= Nat.le_mul_of_pos_left _ m.property
 have hx:N.val ≤ (More (cell m B R.L i)).val:= (Nat.le_mul_of_pos_right (N.val) Nat.zero_lt_two|>.trans (Nat.le_mul_of_pos_right _ B.property))|>.trans (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)
 change (↑R.L.val:ℝ)^i≤ ((More (cell m B R.L i)).val:ℝ); exact_mod_cast he.trans hx
open Fineness
namespace Branch
local notation "X"=> hat R.L x
variable {A:Branch W m k x N0}
variable {i:ℕ}{α:ℝ}(p:Corridor J q h P N0) (a:Bon J q h D delay A)(H:Service V U W J q h D C R0 P N0 delay)
local notation "ζ" n:max=> sites (cell m B R.L n)
def guardFee (W: GivenX V U) := K.top.drift + billX R.L + W.z + |billC R.L|+ billX R.L/512
include a H
lemma yearFit {b:Bet k}(s: Solved P A α b)(e:i<k)(p:A.last.music W.z) :
 let f(r):=(A.gram P b r).beta; X i/2 ≤ f (i+1) ∧ X i/2 ≤ f i ∧ |f i-f (i+1)| ≤ guardFee (W:=W):=by
 intro f; let t:=s.toRealQ; have hQ (z:ℕ)(hz:z≤k): X z/2≤ f z∧ f z≤2*X z:= matched_of_enters (a.clocks z) (a.beta_ok H t z hz).2; let u:= (A.fee P i b).re; let X':=(A.op P i)
 have hp:(A.active P b i).beta=f (i+1)+A.last.move i-u:=by unfold u; rw [← a.fee_eq H t i e]; rfl
 have hv:f i-f (i+1)=A.last.move i-u:=by
    have hq:f i=(A.active P b i).beta:=(a.paysStep H s i e).symm; linarith only [hp,hq]
 have hh : |u| ≤ D (X i) := (Complex.abs_re_le_norm _).trans ((a.posts H).bound _ e _ (a.area H t (i+1)))
 rw [hv]; exact ⟨(hQ _ e).1.trans' (div_le_div_of_nonneg_right (hat_mono (by omega)) (by norm_num)), (hQ i e.le).1, (abs_sub ..).trans (add_le_add (move_pay V W _ A.last p e) (hh.trans (a.clocks i).slow))⟩
omit a
local notation "dL"=> 8* H'*Real.log R.L.val
variable (K) in
def γPay (R: Patch):ℝ:= 8*(Pannier.halfLie SU.group)*Real.log R.L.val
include p
lemma brakeYears (E:LocalRatio L)(s:ℝ)(hv:s>0):∀ᶠ i in atTop,∀ (m:Side)(k:ℕ)(A:Branch W m k x N0)(b:Bet k), Bon J q h D delay A → Solved P A α b→ A.last.music W.z → i<k →
 let G: ℕ→ℝ := fun n=>entryFin V (k-n) (cell m B R.L n) (A.gram P b n).J ((A.gram P b n).beta); let Z(n):=(A.gram P b n).v.re; |(Z i-Z (i+1))-(G (i+1)-G i)| ≤ s*sites (cell m B R.L i):=by
 let C':= dL; let d:= s/3; have ht:d>0:= div_pos hv (by norm_num); let M:=guardFee (W:=W); let T':=1+|M|
 filter_upwards [(stage_slope V x).eventually (p.toll d ht), height_earns V B x |dL| d ht, (stage_slope V x).eventually (entryFuel V E T' d ht (by unfold T'; positivity))] with i u h ξ m k A b t c a e G Z
 let X₀:=A.toSpine.address i; let F:=A.gram P b; let v:= (b.read (i+1)).re; let Hφ:=A.active P b i; let w:=A.corr P b (i+1); let U₀:= A.offset P b (i+1); let P':=A.op P i
 obtain ⟨hu,hκ,hA⟩:= yearFit t H c e a; let G':= entryFin V (k-i) _ (F i).J v
 have hpV:|G' - G i| ≤ d*sites (cell m B R.L i):=ξ v (F i).beta hu hκ ((by rw [abs_sub_comm]; exact hA.trans ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))) : |v-(F i).beta| ≤ T') _ _ _
 have H₀: Heed V X₀ d v U₀ (F i).v :=by
    have hr:=u _ _ _ _ _ (t.request i e) v w.1 (hat_step i ▸ (t.beta_ok H c.toRealQ (i+1) e).2) (t.flow (t.charged H c.toRealQ (i+1) e)) U₀; change Heed V X₀ d v U₀ (A.offset P b i); rw [offset.eq_1 P A b i,dif_pos e]; exact hr
 have hR:crestDue V X₀ v= G (i+1)-G'-C':=by unfold crestDue; change entryFin V (k-1-i) _ _ _-entryFin V (k-1-i+1) _ _ _-_= _; rw [show k-1-i+1=k-i from by omega,show k-1-i=k-(i+1) from by omega]; rfl
 unfold Heed at H₀; rw [hR] at H₀
 have he:=abs_le.mp (h m); change -_ ≤ C'∧C' ≤ d*sites (cell m B R.L i) at he
 change |Z i-Z (i+1)-(G (i+1)-G'-C')| ≤ d*sites (cell m B R.L i) at H₀; rw [abs_le] at hpV H₀ ⊢; unfold d at *; constructor <;> linarith only [he.1,he.2,H₀.1,H₀.2,hpV.1,hpV.2]
omit p H
end Branch
open YM.Fineness
lemma entry_distant (t:0<β)(E:LocalRatio L)(u:1≤K.j)(W:GivenX V U):∃ X> (0:ℝ),∀ m:Side,U.roundZ≤ (Scree.mid m B).val →∀ (T: Interest (Scree.mid m B)) (b:ℝ)(_h:β ≤ b)(i:ℕ), entryFin V i (Scree.mid m B) T b≤X*sites (Scree.mid m B):=by
 let p:=V.W.reserve; let z:= min V.W.parcel 1; have he: 0<z:= lt_min p zero_lt_one
 let k:= (4*Real.log z-200)
 let J:= logFlat L - H'*Real.log β; let F:=3*|J|; let Y:= H'; have hQ:0≤Y:=Pannier.pen_log_nonneg _; have hu : 0≤ F:= mul_nonneg (by norm_num) (abs_nonneg _)
 refine ⟨1+F+Y*|k|, add_pos_of_pos_of_nonneg (by positivity) (by positivity), fun m v T b h i=>?_⟩
 let n:= Scree.mid m B; let N:=More n; let Vn:= sites n; have ht:1≤Vn:= sites_pos _
 have hW: Vn=(Fintype.card (Site N):ℝ):=(sites_as_price n).symm
 let H:= V.L.H i; have hM:= (V.L.roof i).2.1 N; let M:= H.metric.acts N; have hl : k*Vn≤Real.log (leasePart M):= by
    rw [hW]; exact YM.Fineness.tariff he (min_le_right ..) ⟨fun x=> le_trans (mul_le_mul_of_nonneg_right (min_le_left ..) (FreeResolvent.normSum_nn x)) (hM.uniform.1 x).1⟩ hM.symmetric.1
 let Z:= spare L b; have hr:Real.log Z≤|J|:=by
    unfold Z; rw [spare_formula _ E.scale (lt_of_lt_of_le t h), ← Pannier.shadowLie]; refine le_trans ?_ (le_abs_self J); unfold J; gcongr
 have he:= (Cascade.angle_pay T.M K.j U m u v W.health).2.2; unfold entryFin Fineness.gaugedBase; change 3*( (Fintype.card (Site N):ℝ)-1)*Real.log Z - Y * Real.log (leasePart M)+ Cascade.angleFin T.M n K.j ≤ (1+F+Y*|k|)*Vn
 rw [←hW]; have hv:0≤Vn:= (by linarith only [ht]);
 unfold F; nlinarith only [mul_le_mul_of_nonneg_left hl hQ, mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (neg_abs_le k) hQ) hv, he, (mul_le_mul_of_nonneg_left hr (by linarith only [ht]: 0 ≤ Vn-1)), hv, abs_nonneg J]
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Branch.brakeYears
#print axioms YM.CF.Py.Rate.entry_distant
