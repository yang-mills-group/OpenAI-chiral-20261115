import YM.CF.Vp929.Pre.Weights
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
namespace Stockpile

local notation "y_"=> (Scales.y SU.group R.L)
def thinR (R:Patch)(x:ℝ)(z:ℂ):Prop:= let y:=Scales.y SU.group R.L x; 51/100*y< z.re∧z.re< 19/10*y∧ |z.im| < dwidth R x/(100*(1+Real.log y)^2)
local notation "Yf"=> εLeaf R.L
variable{X G E γ A₀:ℝ→ℝ}(pκ:sizeK R.L 1 X)(qκ:Jade.warmK X)(hγ:sizeK R.L 1 γ)(pG:Jade.warmK γ)(pE:∀ n,sizeK R.L n E)(cE:Estimate.Economic c R)(tF:Jade.warmK c.F) {z:ℂ}
local notation "gL"=> Scales.g SU.group R.L
local notation "T_φ" x:max=> Rround R.L x
local notation "θν"=> ((8:ℝ)*(100:ℝ)^6)
local notation "Pad_" x:max=> tablePad R c pW.C Pay x (X x) ρ h (E x) (γ x)
include R
lemma window_open (x:ℝ): IsOpen {z| thinR R x z}:= IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re) (IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const) (isOpen_lt Complex.continuous_im.abs continuous_const))
private lemma roof_room (n₁:ℕ):∀ᶠ x in atTop,∀ z,thinR R x z→let v:=dwidth R x;|z.im| ≤ v/10 ∧ ∀ x'∈ Metric.ball (z.re:ℂ) (5*(v/10)),x'∈ Ledge n₁ v (y_ x):=by
 let M:= widthS n₁+3; filter_upwards [(Scales.year SU.group R.L).eventually_gt_atTop 1,((Pitching.plantd (R:=R)).eventually_ge_atTop (200*((M:ℝ)+2)))] with x p q z H v
 dsimp only [thinR] at H; let y:=y_ x; let b:=Esti.plow x; let nz:0< b:=zero_lt_one.trans_le (Scales.size _); have he:0< y:= by linarith
 have hk :1≤b:=Scales.size _; have hs:0< v:= div_pos he (pow_pos nz _); have hp0: 100*((M:ℝ)+1)*v≤ y:= by
    have hz:b≤b^6:=le_self_pow₀ hk (by norm_num); have ht:100*((M:ℝ)+1)≤ b^6:=by change 200*((M:ℝ)+2) ≤ b at q; linarith
    unfold v dwidth; change 100*((M:ℝ)+1) * (y / b^6) ≤ y; rw [← mul_div_assoc,div_le_iff₀ (pow_pos nz _)]; nlinarith
 constructor
 · have t:100 ≤ 100*(1+Real.log y)^2:=by have h:=Real.log_nonneg p.le; nlinarith
   exact (show |z.im| < v/(100*(1+Real.log y)^2) from H.2.2).le.trans (div_le_div_of_nonneg_left hs.le (by norm_num) (by linarith))
 intro u k; have ht: ‖u - (z.re:ℂ)‖ < 5*(v/10):= by simpa only [Metric.mem_ball,dist_eq_norm] using k
 have h₁:|u.re-z.re| < v/2:= by have hp:= (Complex.abs_re_le_norm (u-(z.re:ℂ))).trans_lt ht; rw [Complex.sub_re,Complex.ofReal_re] at hp; linarith
 have he (z:ℂ): z∈ Ledge n₁ v y→True:=fun _=>trivial
 have hx:(widthS n₁:ℝ)+3=M:=by unfold M; push_cast; rfl
 have p (Y:ℝ):= (abs_lt.1 h₁)
 refine ⟨?_ ,?_ ,?_⟩
 · rw [hx]; linarith [H.1,(abs_lt.1 h₁).1]
 · rw [hx]; linarith [H.2.1,(abs_lt.1 h₁).2]
 have hh:= (Complex.abs_im_le_norm (u - (z.re:ℂ))).trans_lt ht; rw [Complex.sub_im,Complex.ofReal_im,sub_zero] at hh; linarith
private lemma tax_lens :∀ᶠ x in atTop,∀ b≥ march*(Scales.g SU.group R.L x)^3,∀ z,thinR R x z→ (Real.log (2*largage R x)-Real.log (2*b))*(|z.im|/(dwidth R x/10))/Real.log 3 ≤ Real.log 2:= by
 let K:=Real.log 2; have h0:0<K:=Real.log_pos (by norm_num); let H:=Real.log 3; have h1:0<H:=Real.log_pos (by norm_num)
 filter_upwards [(Real.tendsto_log_atTop.comp (Scales.year SU.group R.L)).eventually_ge_atTop (1/(H*K)), stockpile_ν (R:=R),(Scales.year SU.group R.L).eventually_gt_atTop 1] with x hc J t b p z u
 let g:=gL x; let y:=y_ x; let v:=dwidth R x; have h:0<v:= div_pos J.1 (by have h:= (Scales.size x); unfold Esti.plow; positivity)
 have gZ:0<g:=J.2.1; let r:= T_φ x; have hu:0<r:= (lt_of_lt_of_le zero_lt_one J.2.2.2); have ht:r^2=y:=by rw [← mul_left_inj' (show g^2 ≠0 from (pow_pos J.2.1 _).ne')]; rw [Scales.yg2 _ _ J.1]; unfold r Rround; unfold g; field_simp [J.2.1.ne']
 have hk:1≤r:=J.2.2.2
 have he:g^3≤ b:= by refine le_trans ?_ p; apply le_mul_of_one_le_left (pow_nonneg J.2.1.le _) (by norm_num[march]);
 have hy:100*v > 0:=mul_pos (by norm_num) h; have hb:0<b:=(pow_pos J.2.1 _).trans_le he; have pL:1<y:=t
 let a:= Real.log y; have hp:0<a:=Real.log_pos pL
 have hρ : |z.im|/(v/10) ≤ (1/(10*(1+a)^2)) := ((div_le_iff₀ (by positivity:v/10>0)).2 ((show |z.im| < v/(100*(1+a)^2) from u.2.2).le.trans_eq (by field_simp <;> ring)))
 have hm : Real.log (2*largage R x) - Real.log (2*b) ≤ 3*a:=by
    have hv: g^2 = y⁻¹:=by
       have H: g^2*y=1:= (mul_comm ..).trans (Scales.yg2 SU.group R.L J.1); field_simp; nlinarith
    have hB:b≥y⁻¹/y:=by apply le_trans _ he; rw [←hv, div_eq_mul_inv, ←hv]; have hu: g≤1:= (one_le_inv₀ gZ).mp hk; nlinarith [pow_le_pow_of_le_one gZ.le hu (show 3≤4 by norm_num)]
    rw [show largage R x=y from ht,←Real.log_div (by positivity) (by positivity), show 3*a=Real.log (y^3) from (by unfold a; rw [Real.log_pow]; push_cast; rfl)]
    refine Real.log_le_log (by positivity) ?_; field_simp at hB ⊢; nlinarith [mul_le_mul_of_nonneg_right hB (show 0≤y by linarith)]
 have hl:H*K*a ≥ 1:= by have hc:(1:ℝ)/(H*K) ≤ a:= hc; nlinarith [(div_le_iff₀ (mul_pos h1 h0)).1 hc]
 refine le_trans (div_le_div_of_nonneg_right (mul_le_mul hm hρ (by positivity) (by positivity)) h1.le) ?_
 change _ / H ≤ K; field_simp; nlinarith [mul_le_mul_of_nonneg_right hl hp.le,mul_pos h1 h0]
include pκ qκ hγ pG pE cE A
lemma delivery (w0:0<ρ)(w1:1≤h)(n:ℕ) : ∀ᶠ x in atTop,∀ z,thinR R x z→ Signal x R.L (Pad_ x) n (dwidth R x) z:=by
 let G:= tube_p (ρ:=ρ) (Pay:=Pay) (A:=A) pκ hγ qκ pG pE cE pW.C w0 w1; filter_upwards [G, stockpile_ν (R:=R),roof_room (R:=R) n,tax_lens (R:=R)] with x h0 h1 hp h_ z p
 let t:=dwidth R x; let T:= Pad_ x; have ht: 0 < T.width:= div_pos (div_pos h1.1 (pow_pos (zero_lt_one.trans_le (Scales.size x)) _)) (by norm_num); refine ⟨ht,(hp z p).1,(hp z p).2,fun b hv=>?_⟩
 apply h_ b _ z p; have hg:0 ≤ march:=by norm_num [march]
 change b ∈ ({T.bF,T.bK,T.bA,T.bE}:Set ℝ) at hv; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv; rcases hv with hv|hv|hv|hv<;> (rw [hv]; apply mul_le_mul_of_nonneg_left _ hg); exact le_add_of_nonneg_left (abs_nonneg _); exact le_add_of_nonneg_left (abs_nonneg _); exact le_add_of_nonneg_left (abs_nonneg _); exact h0.2
end Stockpile
end Focus
end Pitching
end YM.CF.Py.Rate
