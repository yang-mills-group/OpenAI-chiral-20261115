import YM.CF.Fans.Tee
import YM.CF.Song.Fish
import YM.CF.Rive.Lyric
import YM.CF.Rive.New
import YM.CF.Song.Loom
import YM.CF.Rive.Cart
import YM.CF.Song.Bingo
import YM.CF.Rive.Greet
import YM.CF.Rive.Fawn
import YM.CF.Rive.Coal
import YM.CF.Rive.Fare
import YM.CF.Rive.Pact
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Oise Mew
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
local notation "sN"=>mid N B
local notation "θo"=> Hest.Budget R.L R.odd_side Y.P.den X.P.den G Y.M K.j
local notation "TΦ"=> (Thera.yet_one)
-- expose program β for ALL basis. Output C history ζ trial independent. avoid choices depend on post path.ClockB. Stencil projection sizes. Integrated maturity of L.
open Corne
-- STEP TAKE. define substance tested with Apert budgets.B. K n with k in Sheep input. Not requiring CPS mu on β.L.path
variable {ρ α γ:ℝ}{F:Pilot}{Z:Pluck R}{P₁ P₂:BudgetPoint}
local notation "τ"=> (radiusB x)
open Girt Eire
variable{H₀: GramM (mid P B)}{H₁:GramM (mid N B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{pK L':ℝ}{q q':Chi}{H:Muster G S x d T}
variable {Q₁:Type}[Fintype Q₁][LinearOrder Q₁]
variable (Mk:Monk SU.group S)(A₀:Ids (mid N B))(T₁:Ids (mid P B))
variable (Xo Yo:Mew.Key Q₁→ RegBudget (mid P B))(Zo:Mew.Key Q₁→ForceBudget (mid P B)) -- no scalar change
local notation "P0" i:max=> color_b H₀ H₀.beta (Xo i) (Yo i) (Zo i) H₀.v
variable(hX:∀ i U,River (fun z:Key Q₁=>Xo z i U))(hY:∀ i U,River (fun z:Key Q₁=>Yo z i U))(hZ:∀ i U,River (fun z:Key Q₁=>Zo z i U))
variable {r₁:ℕ}
variable (M':Sheep V U W G H₀.J H₁.J (k+2) n A)
-- extend trivial outside ball to all Ward variant. no estimates there.
variable (Lx:∀ v: Key Q₁,Girt.BaseL U G (color_b H₀ H₀.beta (Xo v) (Yo v) (Zo v) H₀.v) G₀ G₁ q' pK)
variable (Y_:Fend V H M' Z F q H₀.p H₁.p γ α j l r₁)(U_:∀ X: Support (Domain P B), Lend P B d X)(w':Hive.Vista U H₀.J.M H₀.J.P U_ (k+2) M'.q ((Fintype.card Play:ℝ)*L') M'.lot M'.tone)
local notation "G'" v:max=> GroupD Mk A₀ T₁ (H₁:=H₁) (Lx v) Y_ U_ w'
open Stilo
open Jade Pail Nor Yaw Pig Wray
variable {u:Key Q₁}(F0:Mew.Key Q₁ → Troupe S r₁ (Words S)→ Palot.leaf (Site (Domain N B))→ Orbit (mid N B)→ Cipher (mid N B))(Uq: ∀ u∈hill Q₁,∀ i X, LullT V F Z (X:=H₁) (Y:=color_b H₀ H₀.beta (Xo u) (Yo u) (Zo u) H₀.v) M' U_ w' Y_ (Lx u) i (Stilo.beamH X.val) (F0 u i X))
open Bake Vow Lilt
variable (Ys:Mew.Key Q₁→ Troupe S r₁ (Words S)→ Palot.leaf (Site (Domain N B))→ Raid (LeanV (Single (mid N B)))) {HH LΞ Lx0 b Kk Hh:ℝ}{ι':ℕ}
variable (L0:∀ u∈hill Q₁,StageP V H (color_b H₀ H₀.beta (Xo u) (Yo u) (Zo u) H₀.v) H₁ U)(Pinc: ∀ i∈hill Q₁, GroV V F Z (X:=H₁) (Y:=color_b H₀ H₀.beta (Xo i) (Yo i) (Zo i) H₀.v) M' U_ w' Y_ (Lx i) (Ys i) (F0 i) HH Lx0 1)(wV:1≤Kk)(h2:Kk ≤Hh)(vΞ:∀ i∈hill Q₁,ScaledV (stampY Hh Kk) (tolQ H₁.p) HH Lx0 x 1 (Ys i))(bQ:H₁.p.B=radiusB x)(hz:0 ≤ HH)
local notation "Θ"=> (tolQ H₁.p).supportExponent
local notation "TΞ" z:max i:max j:max=> taxV H₁.p (Ys z) HH i j
local notation "PW"=> grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 1
variable (k₀ k₁:ℕ)(s s0:ℝ)(A_: Roof (mid N B) s s0 k₀ G₀)(A₁: Roof (mid P B) s s0 k₁ G₁)(heV:k₀+k₁ ≤ radiusB x) (hz':s ≤ s0)(hq:s0 <d)(hy:0 < s)(hT:Stake.PondP V F x s pK j l (k+2))
local notation "PX"=> H₁.p
local notation "Pδ"=> grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0
local notation "Bν"=> fun i:Mew.Key Q₁=> (fun U:Aura (mid N B)=> cone_f (F0 i) U ∅)
variable {J_:ℕ}{cq vl:ℝ}(Hp:∀ i∈hill Q₁,LookZ V (Xm:=H₁) (Xu:=color_b H₀ H₀.beta (Xo i) (Yo i) (Zo i) H₀.v) M' Y_ (Lx i) U_ w' J_ cq vl)
variable (σ:Q₁→Site (Domain P B))(ho:∀ i:Scree.Hub (mid P B),Hush σ i.val.2 (fun z=> Xo z i))(hp:∀ i:Scree.Hub (mid P B),Hush σ i.val.2 (fun z=> Yo z i))(hv:∀ i:Force (mid P B),Hush σ i.val.1.val.2 (fun z=> Zo z i))
local notation "Dν" z:max=> cone_f (F0 z)
variable(Y1: Monk SU.group S)
include hT A_ A₁ L0 heV hz' hq hy wV h2 vΞ bQ hz Pinc
open Larch Cadre Sour Haro
local notation "oδ"=> (cipherK k₀)
local notation "K1" v:max=> pence_v H₁.p (Ys v) HH
include hX hY hZ Hp ho hp hv
variable (u0:cipherK k₀ ≤ 10*H₁.p.B)
open Sour Haro Tap Ione Larch Nor Stax Salt
open Push.AbsoluteSums Trees
local notation "BN"=> (Scree.mid N B)
variable {R0:Tulip.Male} -- remove
variable (qK:QuotaH V.f V.g V.F1 V.F2) {RA a₀ b₀ c₀:ℝ}{qL:Mast SU.group (Domain N B)} [Nonempty (ΘS RA)] (AA: BondL (Py.tatE V qK (mid N B)) (Py.tagE V qK (mid N B)) (body_Q (N:=(mid N B)) RA) b₀ c₀ a₀ s0)(u':ΘS RA)(hR:TagT (Py.tatE V qK (mid N B)) (Py.tagE V qK (mid N B)) (body_Q (N:=mid N B) RA) s0)
variable{zB z0 z1:ℝ}(kZ:HopeT s0 z0 z1 H₁.p.order)(vt:H₁.p.threshold ≤ z1)(tH: H₁.p.threshold ≤ s)(hw:k₀+10 ≤ H₁.p.B)(hf:cipherK k₀ ≤ 5*H₁.p.B)(w0:1≤ HH)(vY:3≤ H₁.p.B)
local notation "Θv"=> AA.bead HH H₁.p
local notation "Dν_" z:max=> (fun Y:Aura (mid N B)=>Dν z Y ∅)
variable {d' v0 μa σ₀ κa γ0:ℝ}(hA:0 < a₀)(pp0:2*(wu H₁.p+2)*Fief.tileN 1≤ a₀/2/2*H₁.p.B)(r0:feeΨ H₁.p a₀ b₀ c₀ HH≤ d')(hw':0≤ d')(eP:1 ≤κa)(g0:grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0+κa*(Hh⁻¹*(grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0)) < μa)(qp:0 ≤ μa)(qa:spanV H₁.p.B*μa ≤1)(qd: spanV H₁.p.B * d' ≤ wΨ)(qc:d'+spanV H₁.p.B*d'*μa-(wΨ-spanV H₁.p.B*d')*μa<0) -- q' shadow rename
local notation "ψW"=> (spanV H₁.p.B*d'*μa+ spanV H₁.p.B*wΨ⁻¹*μa*d')
local notation "Ψz" i:max=> pivotS AA A_ (hy.trans_le hz') HH (cone_f (F0 i)) w0 vt tH hw hf vY kZ u'
local notation "WΦ" z:max=> (cone_f (F0 z))
local notation "Gv" z:max=> old_Q (F0 z)-old_Q (F0 0)
local notation "σr"=> Kk -- existing 
variable (hγ:0 < γ0)(htγ:degreePrice H₁.p.B γ0 wΨ < 1)
local notation "PE"=> (Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 1)+Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 1))
local notation "PK"=> (Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0)+Kk⁻¹ * (grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0))
local notation "γx"=> degreePrice H₁.p.B γ0 wΨ
include w0 eP g0 qp hw' hγ htγ hf
open Next.Fluctuations.Sector
open Oise Sour Py Haro BondL Palot Vow
variable (q_μ hμ:ℝ)(Y0:ℂ)(L0':ℝ)(Kc: Cusp (mid N B))(eV:RegBudget (mid N B))(Vx:Aura (mid N B)→ℝ)(rp:Anuk Kc Vx H₁.p HH)
local notation "Pv" => (↑(prefactor S SU.group H₀.beta):ℂ) * (↑((shotM L (F.hat R x) H₀.beta)^Fintype.card Y1.park.Free):ℂ) * pulseZ (T:=T) (x:=x) (U:=U) (H₀:=H₀) (G:=G) (H₁:=H₁) Y1
variable {qF v1 qρ Ls Rt:ℝ}(qv:0< qF)(hpq:degreePrice H₁.p.B qF 1 ≤ qρ)(hZ0:qρ<1)(pa:L0'+v1+Beau.rateΓ H₁.p γ0 wΨ ≤1)(pσ:κa*(κa⁻¹*μa) + Real.exp 1*(Beau.rateΓ H₁.p γ0 wΨ+(L0'+v1)) ≤ qF)(hx_μ:∀ i:Seat (mid N B),tallB Vx H₁.p.B (H₁.p.supportExponent+1+1) i ≤ L0')
variable (p_k:H₁.J.M=upMale R.L R.odd_side H₀.J.M)(po_μ:Complex.exp Y0=((prefactor S SU.group H₀.beta:ℝ):ℂ)*(((shotM L (F.hat R x) H₀.beta)^Fintype.card Y1.park.Free:ℝ):ℂ)*pulseZ (T:=T) (x:=x) (U:=U) (H₀:=H₀) (G:=G) (H₁:=H₁) Y1* Complex.exp H₀.v*Complex.exp (↑Ls))(p_μ:∀ Y:Orbit (mid N B), Rue.FleetS H₁.p.threshold Y.1→coldE H₁.p (FeeD H₁.p (fun j=> cone_f (F0 0) j ∅)) Y= (owed_E (mid N B) (Ls+enerS_K H₁ Rt Y))+exponentL H₁.p eV Y.1+fuelV H₁.p Kc Y) -- expresses output RE.Spark RA Ku must same, emit EQ
variable(pL:∀ i:Orbit (mid N B), IsStarProjection (spar K.j H₁.J.M (G₀ i)))(pc0:qK.2=H₁.J.M)(pt0:(qK.1 (mid N B)).val=H₁.J.P)
include Y1 rp qv hpq hZ0 pa pσ hx_μ p_k po_μ p_μ pL
-- correct arbitrary offsets; ℂ units on mark.Forecast.Ph.Point. scale per tag budget.
local notation "aX"=> H₁.p.supportExponent+1+1
lemma primal_V (p0:μa+μa+σr*(PK+(PE+ψW+ψW))≤γ0) :
 let p:=H₁.p; let F':=fun z:Key Q₁=>WΦ z; let W':= fun z=> FeeD H₁.p (nixV (F' z)); let Wox:=fun z=>W' z-W' 0 -- remove
 (∀ z∈hill Q₁,Turf (Wox z)) ∧ (∀ i:Aura (mid N B),∀ v:Orbit (mid N B),River fun z:Key Q₁=>Wox z i v) ∧ (∀ i:Aura (mid N B),Hush (S.ratio.parent∘σ) i.val (fun z=>Wox z i)) ∧ (∀ z∈hill Q₁, ∃ C:Aura (mid N B)→ℝ,(∀ i:Aura (mid N B),Medal H₁.p i.val ∅ ((Wox z) i-(old_Q (F0 z)-old_Q (F0 0)) i) HH (C i))∧∀ i:Seat (mid N B),tallB C H₁.p.B (aX) i ≤ PE+ψW+ψW+2*σr⁻¹*(γ0*γx^1*(1-γx)⁻¹)+2*(γ0*γx^2*(1-γx)⁻¹)) ∧
 ∀ (Q:Mew.Key Q₁→ Cusp (mid N B))(Cq:Mew.Key Q₁→ Aura (mid N B)→ℝ)(ap:∀ i∈hill Q₁,Anuk (Q i) (Cq i) p HH)(hL:∀ z∈hill Q₁,∀ v:Seat (mid N B),tallB (Cq z) p.B (p.supportExponent+1+1) v ≤ v1),(∀ i:Aura (mid N B),∀ D⊆ i.val, Hush (S.ratio.parent∘σ) i.val fun z=> Q z i D)→ (∀ i:Aura (mid N B),∀ D⊆i.val,∀ v:Orbit (mid N B),River fun z:Key Q₁=> Q z i D v) → ∀ (V':Key Q₁→RegBudget (mid N B))(s:Key Q₁→ℂ), (∀ z∈hill Q₁,∀ x:Orbit (mid N B),Rue.FleetS p.threshold x.1 →coldE p (Wox z) x=s z • (1:Cipher (mid N B))+exponentL p (V' z) x.1+fuelV p (Q z) x)→ let R':=fun z=>budgetR (roomV p (nixV (F' z)) (F' z) (Kc+Q z)); (∀ i:Force (mid N B),Hush (S.ratio.parent∘σ) i.val.1.val.2 (fun z=>R' z i))∧(∀ i: Force (mid N B),∀ v:Orbit (mid N B),River fun z:Key Q₁=>R' z i v) ∧∀ i∈hill Q₁, SanB (R' i) (giftK p (p.supportExponent+(1:ℝ)/2)) p HH (fun _=>reserveT p.power p.order p.B (1/2:ℝ)*(κa⁻¹*(qF*qρ^0*(1-qρ)⁻¹)))∧∀ v:Orbit (mid N B),Rue.FleetS p.threshold v.1→ Scree.stove U G₀ (P0 i) G₁ G S q' pK 0 v=Scree.denZ (Jade.spark_B H₁ (eV+ V' i) (R' i) Rt (Y0+s i)) U G₀ v :=by -- ABI scope
 intro p F_Wox W' Wox
 obtain ⟨pT,pR0,h0,Vx'⟩:= talent V Xo Yo Zo hX hY hZ M' Lx Y_ U_ w' F0 Ys L0 Pinc wV h2 vΞ bQ hz k₀ k₁ s s0 A_ A₁ heV hz' hq hy hT Hp σ ho hp hv (show _≤_ from le_trans hf (by omega))
 have pR i D (_:D⊆i.val) t:=pR0 i D t; have h i D (_: D ⊆ i.val):=h0 i D
 let I(z):= K1 z; let B_:=I
 let Fv(z):= nixV (F_Wox z) -- name tune
 have hu(z)(v:z∈hill Q₁):ArmsK H₁.p (WΦ z) (I z) HH:= spiceF V F Z (X:=H₁) (Y:=P0 z) M' U_ w' HH Y_ (Lx z) (L0 z v) _ _ _ A_ A₁ heV hz' hq hz _ _ (Pinc z v) (half_lt_self hy) (half_pos (Lx z).legal.1) (half_lt_self (Lx z).legal.1) (fun i t q=> (hT Y_ i t q).1) (by rw [bQ]; exact Nat.le_trans (by norm_num) Y_.fireK.blade)
 let Lμ:= grain_q H₁.p.B H₁.p.order H₁.p.power 1 Lx0 0; have hpz:=lt_of_lt_of_le zero_lt_one eP
 have hj(z)(v:z∈hill Q₁)(j:Seat (mid N B)):tallB (Vow.hymn (I z)) H₁.p.B (aX) j≤κa⁻¹ * μa:=by
    let A:=I z; have he(i):0 ≤ Vow.hymn A i:=sum_nonneg (fun x p=> ((hu z v).price _ _ (mem_filter.mp p).2.1 (mem_filter.mp p).2.2).wage hz); let C:= Hh⁻¹*Lμ; have hL:tallB (Vow.hymn A) H₁.p.B (H₁.p.supportExponent+1+1+1) j ≤ C:= (Vx' z v|>.2 j).1; have hzC:0 ≤ C:= le_trans (sum_nonneg (fun i _=> mul_nonneg (he i) (Real.exp_pos _).le)) hL; have hc:0 ≤ Hh⁻¹:=inv_nonneg.mpr (zero_le_one.trans (wV.trans h2)); have H:0 ≤ Lμ:=by by_contra! u; exact (not_lt_of_ge hzC) (mul_neg_of_pos_of_neg (inv_pos.mpr (zero_lt_one.trans_le (wV.trans h2))) u)
    exact (tall_m _ he (le_add_of_nonneg_right zero_le_one) j).trans (hL.trans ((le_inv_mul_iff₀ hpz).mpr ((le_add_of_nonneg_left H).trans (le_of_lt g0))))
 let yS:= H₁.p.supportExponent+1+1; have he(z)(v:z∈ hill Q₁)(X):= (Vx' z v|>.1 X ∅ (empty_subset _)).merit
 have hW:= (show 0 < wΨ from (by norm_num [wΨ])); have ht':wΨ ≤1:=by norm_num [wΨ]
 have hN(K: Aura (mid N B)→ℝ)(hK:0 ≤ K)(z: Seat (mid N B)): tallB K H₁.p.B (yS+wΨ) z ≤ tallB K H₁.p.B Θ z:=tall_m _ hK (add_le_add_right ht' _) z -- add_le arg?
 let Vp:=PE+ψW+ψW; have hxV:PE ≤ Vp:=by
    have hg:0≤ spanV H₁.p.B:=Nat.cast_nonneg _; have hb:0 ≤ ψW:=by positivity
    exact le_trans (le_add_of_nonneg_right hb) (le_add_of_nonneg_right hb)
 have hx(i)(p:i∈hill Q₁)(y:Seat (mid N B)):tallB (Sour.urnL (I i)) H₁.p.B (yS+wΨ) y ≤ μa:=by
    refine (hN _ (fun j=> (he _ p j).wage hz) y).trans ((Vx' i p|>.2 y).2.trans ?_); refine (le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans eP) ?_)).trans (le_of_lt g0); exact le_trans (sum_nonneg (fun j _=> mul_nonneg (sum_nonneg (fun k v=> ((hu i p).price j k (mem_filter.mp v).2.1 (mem_filter.mp v).2.2).wage hz)) (Real.exp_pos _).le)) (Vx' i p|>.2 y).1 -- sum synt
 let E:=fun i=> old_Q (F0 i)-old_Q (F0 0); have hK:=zero_lt_one.trans_le wV
 have hp'(i)(p:i∈hill Q₁):∃ (A:Aura (mid N B)→ℝ), Ready Palot.stern (PX).B A yS γ0 wΨ γx ∧ (∀ X:Aura (mid N B),Medal PX X.val ∅ (Fv i X) HH (A X)) ∧ ∃ C: Aura (mid N B)→ℝ, (∀ X:Aura (mid N B), Medal PX X.val ∅ (Wox i X-E i X) HH (C X))∧∀ X:Seat (mid N B),tallB C (PX).B yS X≤Vp+2*σr⁻¹*(γ0*γx^1*(1-γx)⁻¹)+2*(γ0*γx^2*(1-γx)⁻¹):=by
    obtain ⟨x,A,C,HA,w,Hc,v⟩:= leaf_X V Xo Yo Zo M' Lx Y_ U_ w' F0 Ys L0 Pinc wV h2 vΞ bQ hz k₀ k₁ s s0 A_ A₁ heV hz' hq hy hT i p
    let Bp:= urnL (I i)+urnL (I 0)+Kk • (C+A); have hc(j):0≤ C j:= (Hc j).wage hz; have ha(j):0 ≤ A j:= (HA j).wage hz; have hA(j):0 ≤ Kk *((C+A) j):=mul_nonneg hK.le (add_nonneg (hc _) (ha _))
    have hp'(Y):Medal H₁.p Y.val ∅ (Fv i Y) HH (Bp Y):=(he _ p Y).big ((le_add_of_nonneg_right ((he _ roots Y).wage hz)).trans (le_add_of_nonneg_right (hA Y)))
    have hx'(Y): Medal H₁.p Y.val ∅ (Fv 0 Y) HH (Bp Y):=(he _ roots Y).big ((le_add_of_nonneg_left ((he _ p Y).wage hz)).trans (le_add_of_nonneg_right (hA Y)))
    have htB:Ready Palot.stern H₁.p.B Bp yS γ0 wΨ γx:=by
      refine ready_T hγ hW htγ (fun j=>(hp' j).wage hz) ?_
      intro t; unfold Bp; rw [Larch.tall_add,Larch.tall_add,Larch.tall_s,Larch.tall_add]; exact (add_le_add (add_le_add (hx i p t) (hx _ roots t)) (mul_le_mul_of_nonneg_left (add_le_add ((hN _ hc t).trans (v t)) (((hN _ ha t).trans (w t)).trans hxV)) hK.le)).trans p0
    let q0:= Fv i-Fv 0-E i
    have hy (Y):Medal H₁.p Y.val ∅ (Fv i Y-Fv 0 Y) HH (Kk⁻¹*Bp Y):=by
        rw [show Fv i Y-Fv 0 Y=E i Y+q0 Y from by unfold q0; simp only [Pi.sub_apply,add_sub_cancel]]; refine ((Hc Y).plus (HA Y)).big ((le_inv_mul_iff₀ hK).mpr (le_add_of_nonneg_left ?_)); exact add_nonneg ((he _ p Y).wage hz) ((he _ roots Y).wage hz)
    have hy0(j:Aura (mid N B))(x:Orbit (mid N B)): Fv i j x-Fv 0 j x=E i j x +q0 j x:=by unfold q0; simp only [Pi.sub_apply,add_sub_cancel]
    refine ⟨Bp,htB,hp',_, fun Y=> Rive.liftT Y Kk hK htB w0 hp' hx' hy HA (E i) hy0 x,fun j=>?_⟩
    exact Rive.loft_T Kk hK htB w0 hp' hx' hy HA _ hy0 x _ ((tall_m A ha (le_add_of_nonneg_right hW.le) j).trans (((hN _ ha j).trans (w j)).trans hxV))
 choose! Hm hc ha E' hv' hzG using hp'
 have he:0≤p.supportExponent+1:=by linarith [p.exponent_pos]
 let Gs(z):= nixV (F_Wox z); have ht(z w): Turf (W' z):= turfK (Gs z) (pT z w)
 have h2b(j:Aura (mid N B)):Hush (S.ratio.parent∘σ) j.val (fun z=> W' z j):= lore_H Gs p (S.ratio.parent∘σ) (fun i=> h i ∅ (empty_subset _)) j
 have h1b(j:Aura (mid N B))(x):River (fun z=> W' z j x):= lore_Y Gs p w0 (fun i v=>pR i ∅ (empty_subset _) v) Hm (add_nonneg he zero_le_one) hc ha ((ready_pos _ _ (hc 0 roots)).le) htγ j x
 refine ⟨fun z t i x j=> congrArg₂ (·-·) (ht z t i x j) (ht 0 roots i x j),fun i v=> river_minus _ _ (h1b i v) (zeroR _),fun i z t w s p=> congrArg (fun v=> v-W' 0 i) (h2b i z t w s p),fun z u=>⟨_,hv' z u,hzG z u⟩,?_ ⟩
 intro Q C α u ux d_ V' Tx t R'
 let Lν(z):=Kc+Q z
 have hQ(z w): Anuk (Lν z) (Vx+C z) p HH:=⟨add_nonneg rp.1 (α z w).1,fun i j p t=> (rp.2 i j p t).plus ((α z w).2 i j p t)⟩
 obtain ⟨l,b,f⟩:= open_Q F_Wox pT Hm B_ hc ha hu w0 hj eP pa hpq hZ0 qv pσ Lν (fun z=>Vx+C z) hQ (fun z t v=> (by rw [Larch.tall_add]; exact add_le_add (hx_μ _) (u _ t _))) _ pR h (fun i D t v=> dub_V (zeroR _) (d_ i D t v)) (fun i D t a u b v p=>congrArg (fun x=> Kc i D +x) (ux i D t a u b v p)) -- ABI
 refine ⟨l,b,fun i hi=>⟨f i hi,fun x hx=>?_ ⟩⟩
 let Zs:=Pv; have h_t:= po_μ
 let s':ℂ:= (↑Ls:ℂ)+Tx i; have hm: Complex.exp (Y0+Tx i)=Zs*Complex.exp H₀.v*Complex.exp s':=by unfold s'; rw [Complex.exp_add,h_t, Complex.exp_add]; exact mul_assoc ..  -- placeholder
 have ht(v:Orbit (mid N B))(h':Rue.FleetS p.threshold v.1): Palot.hGas (flags p.threshold v.1) (keyL p (F_Wox i) (nixV (F_Wox i)) v)= Complex.exp (s'+enerS_K H₁ Rt v) • (exp (exponentL p (eV+V' i) v.1)*fueled p (R' i) v):=by
    apply glint (hc i hi) he (ha i hi) zero_lt_one w0 v h' (eV+V' i) (s'+enerS_K H₁ Rt v); change coldE p (W' i) v= _; have hp':W' i= W' 0+ Wox i:=by unfold Wox; abel
    nth_rw 1 [hp']; rw [crep,t i hi v h',p_μ v h']; change _= (_+ (_:ℂ)) • (1:Cipher (mid N B))+ _ + _; unfold s'; rw [add_smul,add_smul,ripe_H,toast]; rw [show owed_E _ _=(Ls:ℂ) • 1+(↑(enerS_K H₁ Rt v):ℂ) • (1:Cipher (mid N B)) from ?_ ]; swap; · unfold owed_E Lilt.thim; rw [add_smul]; rfl
    abel
 exact tree_Vζ V F Z (X:=H₁) (Y:=P0 i) M' U_ w' HH Y1 Y_ (Lx i) (L0 i hi) k₀ k₁ s0 A_ A₁ heV hz' hq hy hT _ _ (Pinc i hi) p_k pL _ _ _ _ hm _ hx _ (fun v h=>by rw [key_c]; exact ht v h) -- shadow L0+F*
end YM.CF.Rive
#print axioms YM.CF.Rive.primal_V
