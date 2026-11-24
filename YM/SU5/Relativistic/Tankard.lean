import YM.SU5.Relativistic.Toast
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


private lemma few_f (i s:ℕ)(M:Tulip.Male): seaPrec P.K.j (N i s) M ≤ 0:=by
 let n:= (N i s); let U:Bkg (More n):=1; let W:=P.U; let a:= spar P.K.j M U; let V:=changeM (m:=Vale.mesh (Y.ir i) P.R.L s) W U M; have hZ: P.U.roundZ≤ n.val:= P.J.gran.trans ((Y.voyage i).ownership s).size; have ht :Cube.Guard U P.d :=(Kennel.near_g (n:=More n) _ P.dpos).self_of_nhds
 have hY: Sea a V:= sea_g hZ U ht M; have he:=orb_snap a (tickA n) (0:Op (Single n)) V hY (mateK n) (tickB n) ((W.broadness _ hZ M).projection _ ht) (carts_p _ (cutM_idp _)) (rank_z n (j:=P.K.j) (by rw [P.kJ]; decide) M).symm
 change -OrbT _ _ _≤_; rw [←he]; unfold skyGlow; rw [add_zero,quant_one,act_one]; apply Real.log_nonpos (norm_nonneg _); calc
    _ ≤ _:= norm_inner_le_norm ..
    _ = _:= by rw [(tickB n).2,hY.2,mul_one]

-- pre cost small at one height large. (or all) no assume sea+
lemma costs_b {A:ℝ}(h: Inflation A P) : ∀ᶠ s:ℕ in atTop, ∃ D> (0:ℝ),∀ i k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k →
   Real.exp (chase Y i k s-D*sites (N i s)) ≤ ‖Buffered.vac0 P.U (Xs i k s) ((Y.voyage i).CapeT s)‖:=by
 filter_upwards [compensates Y h, (turnover P).eventually_ge_atTop 2] with s u v;
 let x:= hat P.R.L P.x s; let d:= P.K.top.clip.direct; let Z:= mulch x+(A+1); let i:= Fintype.card SU.group.ColorIndex
 let k₀:= 3*|logFlat P.L|+ 2*i*|Real.log d|- (-(Z)); refine ⟨|k₀|+1,by positivity,fun j k g t=>?_⟩
 let y:=(Xs j k s); let b:= N j s; let X:=More b; have hp: 2 ≤ X.val:= Nat.le_mul_of_pos_left 2 b.property; let μ:=sites b; let pβ:= ((Y.voyage j).X (Y.uv k)).pull.sift _ t; have hz:1 ≤ y.beta:= le_trans (by linarith only [v]) pβ.1; have h0:=zero_lt_one.trans_le hz
 let M:=Y.uv k-s; let H:= P.V.L.H M
 let Dg:ℕ:= Fintype.card (ScrollB G5 X)
 have hv : (Fintype.card (Site X):ℝ)= μ:=by rw [site_card,Nat.cast_pow];
 have hj: (Dg:ℝ) ≤ 4*μ*i:= by
    have ht: Dg ≤ Fintype.card (Ink G5 X):= Fintype.card_le_of_embedding (fast G5 X); apply (Nat.cast_le.mpr ht).trans_eq; unfold Ink Papyrus.GaugeFlux.Bond Fixed.Pivots.Link Lattice.Edge; rw [Fintype.card_prod,Fintype.card_prod]; push_cast; rw [show Fintype.card Axis=4 from rfl,hv]; unfold i; push_cast; ring
 let V:=P.V
 have he := (primal_g V M X hp).2
 have hL:=Real.log_le_log (show 0<d^Dg from pow_pos P.K.top.clip.quadratic_pos _) he; rw [Real.log_pow] at hL
 let S:= spare P.L y.beta; have hS:Real.log S ≤ |logFlat P.L|:=by unfold S; rw [spare_formula _ P.chart.scale h0]; exact le_trans (sub_le_self _ (mul_nonneg (by positivity) (Real.log_nonneg hz))) (le_abs_self _)
 apply (le_trans ?_ (u j k g t)); apply Real.exp_monotone; unfold chase prologue prebill preGa views; rw [hv]; have ht:= few_f Y j s y.J.M; have hM:1≤ μ:= sites_pos _
 change (3*μ-3)*Real.log S+ -(1/2)*Real.log (costDet G5 H X) + seaPrec P.K.j _ y.J.M - _≤ -Z* μ; unfold k₀ at *; let A':= Real.log d; have he:-(Dg:ℝ)*A'≤ Dg*|A'|:=by have hh:=neg_abs_le A'; nlinarith only [hh, show (0:ℝ)≤Dg by positivity]
 have hx:=mul_le_mul_of_nonneg_right (le_abs_self k₀) (zero_le_one.trans hM) -- restore name
 nlinarith only [hM,ht,hL,he,(mul_le_mul_of_nonneg_left hS (show 0≤3*μ-3 by linarith)), hx, mul_le_mul_of_nonneg_right hj (abs_nonneg A'), abs_nonneg (logFlat P.L)]

local notation "Wv" i:max k:max s:max=> Buffered.vac0 P.U (Xs i k s) ((Y.voyage i).CapeT s)
include p
lemma pressed {A:ℝ}(h: Inflation A P)(ε:ℝ)(e:0<ε):∀ᶠ s:ℕ in atTop,∀ i k:ℕ,(Y.voyage i).kick≤ k→ s≤ Y.uv k→ Real.exp (chase Y i k s-ε * sites (N i s)) ≤ ‖Wv i k s‖:=by
 let r:=ε/2; have hr:0<r:= by unfold r; positivity
 let a:= ((P.R.L.val:ℝ)^4); have ha:2≤a:=by
    have he:(2:ℝ)≤ P.R.L.val:=by exact_mod_cast (show 2≤ P.R.L.val by have h:= P.V.tallX; omega)
    exact he.trans (le_self_pow₀ (one_le_two.trans he) (by norm_num))
 obtain ⟨t₀,h₀⟩:= eventually_atTop.mp ((costs_b Y h).and (renew_offset Y p r hr))
 obtain ⟨T₀,hT,TU⟩:= (h₀ _ le_rfl).1
 let m(i:ℕ)(s:ℕ):=sites (N i s)
 have H(j i k:ℕ)(z:(Y.voyage i).kick≤k)(t:t₀+j≤ Y.uv k): Real.exp (chase Y i k (t₀+j) - (r+T₀*a⁻¹^j)*m i (t₀+j))≤ ‖Wv i k (t₀+j)‖:=by
    induction j with
    | zero=> apply (TU i k z t).trans'; apply Real.exp_monotone; have hx:=sites_pos (N i t₀); change _ ≤ _- T₀*m i t₀; have hμ:1 ≤ m i t₀:=hx; rw [Nat.add_zero,pow_zero,mul_one]; nlinarith only [hμ,hr]
    | succ j ih=>
       have h:= ih (by omega); let s:=t₀+j
       rw [show t₀+(j+1)=s+1 from (Nat.add_assoc ..).symm]
       have hv:= (h₀ s (Nat.le_add_right ..)).2 i k t -- type t mismatch add_assoc
       let A0:= (Xs i k (s+1)); let B:= (Xs i k s); let C:= (m i s); let Z0:= B.v.re-A0.v.re;
       have he : ‖Wv i k (s+1)‖ = Real.exp Z0 * ‖Wv i k s‖ :=by
         let D:= ((Y.voyage i).X (Y.uv k)); let ht := show partitionZ (D.gram (s+1)) P.U ((Y.voyage i).CapeT (s+1))=partitionZ (D.gram s) P.U ((Y.voyage i).CapeT s) from (D.balance (s+1) (by omega)).trans (D.balance s (by omega)).symm
         change ‖compensated P.U A0 _‖= _*‖compensated P.U B _‖; unfold compensated; rw [norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp,show partitionZ A0 P.U _=_ from ht,← mul_assoc, ←Real.exp_add,Complex.neg_re,Complex.neg_re,show Z0 + -B.v.re= -A0.v.re by unfold Z0; ring]
       have hp:(m i (s+1))= a*C:=expansionStep Y i s; rw [he]; apply (mul_le_mul_of_nonneg_left h (Real.exp_pos Z0).le).trans'; rw [←Real.exp_add]; apply Real.exp_monotone; rw [hp, pow_succ]; let Q:=T₀*a⁻¹^j; change chase _ _ _ _ - (r +T₀*(_*a⁻¹))*(a*C) ≤ Z0 +(chase _ _ _ s-(r + Q)*C); rw [show (r+T₀*(a⁻¹^j*a⁻¹))*(a*C)=r*a*C+Q*C from ?_]; swap; · unfold Q; field_simp
       change |Z0- (chase Y i k (s+1)- chase Y i k s)| ≤ r*C at hv; have he :1≤C:=sites_pos _; nlinarith only [(abs_le.mp hv).1,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hr.le) (zero_le_one.trans he)]
 have hk:Tendsto (fun s:ℕ=> r+T₀*a⁻¹^s) atTop (𝓝 r):= by simpa using tendsto_const_nhds (x:=r)|>.add ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0≤a⁻¹) (by rw [inv_lt_one₀ (by positivity)]; linarith)).const_mul T₀)
 obtain ⟨q,Q⟩:=eventually_atTop.mp (hk.eventually (ge_mem_nhds (half_lt_self e)))
 filter_upwards [eventually_ge_atTop (t₀+q)] with s z i k t y; obtain ⟨j,rfl⟩:= Nat.exists_eq_add_of_le (show t₀ ≤ s by omega);
 apply (H j i k t y).trans'; apply Real.exp_monotone; apply sub_le_sub_left (mul_le_mul_of_nonneg_right (Q j (by omega)) (zero_le_one.trans (sites_pos _)))
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.pressed
