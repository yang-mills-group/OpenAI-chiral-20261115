import YM.SU5.Relativistic.Tablet
import YM.SU5.FiniteGaugeData.Pannier.Husks
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
open Window Eire Girt VolumeRate
open Pitching Focus Papyrus.GaugeFlux
namespace LocalLimit
open Preparation
variable {P: Preparation} {l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable (p: FairRoute P.P P.J P.h P.N0 Chi.canonical)
local notation "kT" k:max=>Y.uv k
local notation "Xs" i:max k:max s:max => ((Y.voyage i).X (Y.uv k)).gram s
local notation "Mt" i:max=>Y.ir i
local notation "N" i:max s:max => P.Ctor (Y.ir i) s
local notation "E"=>P.V
local notation "T"=>Y.meter
local notation "G5"=> SU.group

def prologue (i k s:ℕ)(β:ℝ) := prebill (E) (More (N i s)) (N i s) (kT k - s) (Xs i k s).J.M β
def chase (i k s:ℕ) := prologue Y i k s (Xs i k s).beta
include p
-- offset paid with target BOTH β. gap β shift O(1) uniform from movement & admissibility.
lemma prepare_offset (ε:ℝ)(e:0<ε): ∀ᶠ s in atTop,∀ i k:ℕ, s< kT k →
   let b:=(Xs i k (s+1)); let a:= Xs i k s
   |((a.v).re - b.v.re)-(chase Y i k (s+1)-prologue Y i k s b.beta)| ≤ ε * sites (N i s):=by
 have τ : Tendsto (hat P.R.L P.x) atTop atTop:= turnover P
 filter_upwards [τ.eventually (p.owes ε e),τ.eventually (prolong (V:=P.V) P.app.post P.app.earns)] with s z t i k hk a b
 let L:= (Y.voyage i).paths (Y.uv k); obtain ⟨ζΨ,hs,hx,-⟩:= L.issued
 let A:= Actual Y.meter (Y.voyage i).funds (Y.voyage i).CapeT (gaugeFreq P (Y.tile*P.M)) (kT k); let Q:=A.toSpine.address s; let f:= (ζΨ.read (s+1)).re; let C:= A.chargeLevel P.P ζΨ (s+1);
 have he:= L.paid.beta_ok P.H hs.toRealQ (s+1) hk; have hp:= L.paid.flow (L.paid.charged P.H hs.toRealQ (s+1) hk); let U:=z Q (p':= (T).a (s+1)) (L.paid.request s hk); let D:= A.offset P.P ζΨ;
 have hw:= U.faith f C (D (s+1)) trivial (submits t (hat_step s ▸ he.2) ⟨hp,Charged.zero.mono (mul_nonneg (by norm_num) t.high.le)⟩)
 unfold chase prologue a b; rw [hx]; change |( (A.offset P.P ζΨ s).re-(D (s+1)).re)-(prebill P.V _ _ (kT k-(s+1)) _ f-prebill P.V _ _ (kT k-s) _ f)| ≤ _
 rw [Branch.offset.eq_1, dif_pos hk,show kT k-(s+1)=Q.lag from (by change kT k-_ = kT k - 1 -s; omega),show kT k-s= Q.lag+1 from (by change kT k-_ = kT k - 1 -s+1; omega)]
 exact hw
omit p
lemma enoughScale : ∃ C:ℝ,∀ᶠ s in atTop,∀ i k:ℕ, s< kT k → |(Xs i k s).beta - (Xs i k (s+1)).beta|≤C:=by
 let A:= |P.V.L.charge 0|+|P.W.C.P|+P.K.top.drift + |SU.group.slopeConstant*Real.log P.R.L.val|
 refine ⟨A+2,?_⟩; filter_upwards [(turnover P).eventually (Chill_v.spine_a P.app.post |>.eventually (ge_mem_nhds zero_lt_one))] with s h i k t
 let L:= (Y.voyage i).paths (Y.uv k); obtain ⟨ζΨ,hs,hx,-⟩:=L.issued; rw [hx,← L.paid.success P.H hs.toRealQ s t (L.paid.paysStep P.H hs s t)]; let X:= Actual Y.meter (Y.voyage i).funds (Y.voyage i).CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k); let Z:= X.toSpine.address s; let β:= (ζΨ.read (s+1)).re; let Φ:= X.op P.P s; let p:= X.chargeLevel P.P ζΨ (s+1); let D:= hat P.R.L P.x s
 have he:= L.paid.beta_ok P.H hs.toRealQ (s+1) t; have hp:= L.paid.flow (L.paid.charged P.H hs.toRealQ (s+1) t); let F:= L.paid.request s t
 have hv := ((L.paid.certified P.H s t).cost (β:ℂ) (p,0) (hat_step s ▸ he.2) ⟨hp,Charged.zero.mono (show 0≤ _ from mul_nonneg (by norm_num) (L.paid.clocks s).leaf.le)⟩).2
 have hM := ((F.statv β p 0 0 (hat_step s ▸ matched_of_enters (L.paid.clocks _) he.2)).dose.fiscal)
 change |(β+(P.V.L.charge Z.lag+Z.fee)- (Φ.Δ β (p,0)).re )- β| ≤_
 have hβ : |(Φ.Δ β (p,0)).re|≤ (1:ℝ) := (Complex.abs_re_le_norm _).trans (hv.trans h)
 unfold A; have ht:= P.V.L.bound Z.lag; change |Z.fee|≤_ at hM; rw [abs_le] at hβ hM ⊢; constructor <;> linarith only [ht,hβ.1,hβ.2,hM.1,hM.2,le_abs_self (SU.group.slopeConstant*Real.log P.R.L.val),neg_abs_le (SU.group.slopeConstant*Real.log P.R.L.val),abs_nonneg (P.V.L.charge 0),le_abs_self P.W.C.P,le_abs_self (P.V.L.charge Z.lag+SU.group.slopeConstant*Real.log P.R.L.val),neg_le_of_abs_le (le_refl |P.V.L.charge Z.lag+SU.group.slopeConstant*Real.log P.R.L.val|)]

private lemma logs_ordered (A e:ℝ)(p:0<e) : ∀ᶠ x:ℝ in atTop,∀ {a b:ℝ}, x≤ a → x ≤ b → |a-b| ≤ A → |Real.log a-Real.log b| ≤ e:=by
 filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (A/e)] with x hp hq a b u v t
 have he(a b:ℝ)(k:x ≤ a)(l:x≤ b)(h:a-b≤A) : Real.log a-Real.log b ≤e:=by
    have ht:0<b:=hp.trans_le l; have hx:0<a:=hp.trans_le k; rw [← Real.log_div hx.ne' ht.ne']; apply (Real.log_le_sub_one_of_pos (div_pos hx ht)).trans
    have hB:a/b ≤ 1+e:=by rw [div_le_iff₀ ht]; nlinarith [(div_le_iff₀ p).mp hq]
    linarith
 rw [abs_le] at t ⊢; constructor; · linarith only [he b a v u (by linarith only [t.1])]
 exact he a b u v t.2
private lemma spent_log (b:ℝ)(e:ℝ)(p:0<e) : ∀ᶠ x:ℝ in atTop,∀ {a v:ℝ},x ≤ a → x ≤ v →|a-v|≤b→|Real.log (spare P.L a)- Real.log (spare P.L v)| ≤ e:=by
 let C':= Fintype.card SU.group.ColorIndex; let A:ℝ:= C'/2; have he:0≤A:=by unfold A; positivity
 filter_upwards [logs_ordered b (e/(A+1)) (div_pos p (by linarith)), eventually_gt_atTop (0:ℝ)] with x h u a v z g hB
 have hp:= h z g hB; rw [spare_formula P.L P.chart.scale (u.trans_le z),spare_formula P.L P.chart.scale (u.trans_le g)]; change |(_-A*_)-(_-A*_)|≤ e; rw [show (logFlat P.L-A*Real.log a)-(logFlat P.L-A*Real.log v)= A*(Real.log v-Real.log a) by ring,abs_mul,abs_sub_comm,abs_of_nonneg he]; apply (mul_le_mul_of_nonneg_left hp he).trans; rw [← mul_div_assoc,div_le_iff₀ (show (0:ℝ)<A+1 by linarith)]; nlinarith
include p
-- dialect
lemma renew_offset (ε:ℝ)(e:0<ε): ∀ᶠ s in atTop,∀ i k:ℕ, s< kT k →
 let a:=(Xs i k s); let b:=Xs i k (s+1)
 |(a.v.re-b.v.re)-(chase Y i k (s+1)-chase Y i k s)|≤ ε * sites (N i s):=by
 let η:=ε/4; have ht:0<η:=by unfold η; positivity
 obtain ⟨C,hp⟩:= enoughScale Y
 filter_upwards [hp,prepare_offset Y p η ht, ((turnover P).atTop_div_const zero_lt_two).eventually (spent_log (P:=P) C η ht)] with s hf v q i k t a b
 let h:= (Y.voyage i).X (Y.uv k); let x:= hat P.R.L P.x; let U:=sites (N i s); let Va:= prologue Y i k s b.beta
 have hz:x s ≤ x (s+1):= by unfold x; exact hat_mono (by omega) -- tune params
 have hu:x s/2≤ b.beta:=le_trans (by exact div_le_div_of_nonneg_right hz zero_le_two) (h.pull.sift _ t).1; have hl:= q (h.pull.sift s t.le).1 hu (hf i k t); have hd:Fintype.card (Site (More (N i s)))= (More (N i s)).val^4:= site_card _
 have hU:1 ≤ U:=sites_pos _
 have hc: |chase Y i k s-Va|≤3*η*U:=by
    unfold chase Va prologue prebill preGa views; rw [hd,Nat.cast_pow]; change |(_+_+_)-(_+_+_)|≤_; let A:= (3:ℝ)*U-3
    have he:0≤A:=by unfold A; linarith
    let Z(t:ℝ):=Real.log (spare P.L t); change |((A*Z a.beta+_)+_)-((A*Z b.beta+_)+_)|≤_
    rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub, ← mul_sub,abs_mul,abs_of_nonneg he]; change |Z a.beta - Z b.beta|≤η at hl; unfold A at *; apply (mul_le_mul_of_nonneg_left hl he).trans; nlinarith
 have he:=v i k t; change |(a.v.re-b.v.re)-(chase Y i k (s+1)- Va)|≤ η*U at he; change _≤ ε*U; unfold η at *; rw [abs_le] at he hc ⊢; constructor <;> linarith
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.renew_offset
