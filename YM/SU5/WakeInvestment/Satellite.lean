import YM.SU5.WakeInvestment.MarginShelf
import SatinThinMuseum
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

-- Three counterparties. Q already bought at scene (including boundary/defect penalty stock).
-- In scene costs κ tested on actual configurations, retain mixed comparator's real price.
-- Wick uses all Sig rotations here.
structure LeadHall (s i k:ℕ)(f ι:ℝ)(φ:Pane (N s i)→ℝ)(c:Side)(r:Ratio c (More (N s i))) (M:ℝ) : Prop where
 copy : ∀ t:Signed, ∃ (W:Altar SU.group (More (N s i))→ℝ) (Q R1 R2:ℝ), ContDiff ℝ 1 W ∧ (∀ i, |W i| ≤ R1) ∧ (∀ i, ‖fderiv ℝ W i‖ ≤ R2) ∧
    let F:=Y.uv k-s; let u:=θ s; let S:= RootBook Y i k s
    Q + plumeCost (P.V.L.mood F) (P.V.L.tied F) W ι + trend*R2^2*ι^2 ≤ M ∧ ∀ a:Support c, ∀ D:Finset (Lattice.Face (Per (More (N s i)))), Gleam.Wake.nearScene (P.V.L.mood F) (P.V.L.tied F) S.p r (radiusB u) S.beta (ageC u) (shieldC u) (f*S.p.threshold) (Q+healthC u*(trap r (radiusB u) a+trap_s (radiusB u) D)) a D ι (φ ∘ (pull t 0)) W

abbrev authNear (s i k:ℕ)(f z:ℝ):Prop:= let R:=RootBook Y i k s; z ≤ R.beta*Gleam.Wake.unitDueN P.K.top.clip (f*R.p.threshold)/2

def launchHall (s i k:ℕ)(f z κ k':ℝ)(x:Pane (N s i)):= Papal.frost_bill Y s i k (θ s) κ k' x*Real.exp (z* (misdemean (f*(RootBook Y i k s).p.threshold) x).card)

def launchPrice (s i k:ℕ)(f z κ k' ι:ℝ)(φ:Pane (N s i)→ℝ)(x:Pane (N s i)):= launchHall Y s i k f z κ k' x*Real.exp (ι*φ x)

lemma frost_hires(s i k:ℕ)(ht:s≤Y.uv k)(κ k':ℝ): Papal.frost_bill Y s i k (θ s) κ k'=Gleam.twice_angled (P.V.L.path (Y.uv k-s)) P.K.top.clip (RootBook Y i k s).p (RootBook Y i k s).beta κ k' (shieldC (hat P.R.L P.x s)) (n:=More (N s i)):=by obtain ⟨p,h,g,S⟩:= Papal.prices_plot Y s i k ht; rw [←h,←g]; rfl
lemma frost_now (s i k:ℕ)(ht:s≤Y.uv k)(κ k':ℝ): Envelope (Papal.frost_bill Y s i k (θ s) κ k'):= by rw [frost_hires Y s i k ht κ k']; exact env_twice (P.V.L.mood (Y.uv k-s))
lemma launchHall_env (s i k:ℕ)(ht:s≤Y.uv k)(f z κ k':ℝ) : Envelope (launchHall Y s i k f z κ k') :=(frost_now Y s i k ht κ k').mul ((conduct ..).exp)
lemma launchPrice_env (s i k:ℕ)(ht:s≤Y.uv k)(f z κ k' ι:ℝ) (φ:Pane (N s i)→ℝ)(p:Envelope φ): Envelope (launchPrice Y s i k f z κ k' ι φ):= (launchHall_env Y s i k ht f z κ k').mul (expEnv p ι)

-- Providing these extra measurements as they're needed later for enrolling actual masks
structure affordableRatio (s i:ℕ) (c:Side) (r:Ratio c (More (N s i))) : Prop where
 paying: Odd r.count.val
 breathing : respire (θ s) P.R.L r.count.val
 sequester: 2*(r.count.val+1) < (More (N s i)).val
 horizon: hallBill (radiusB (θ s))≤ r.count.val/2

lemma neritic (f:ℝ)(hf:0<f)(f1:f≤1) : ∀ᶠ s in atTop, ∀ i k:ℕ,s ≤ Y.uv k → ∃ (c:Side) (r:Ratio c (More (N s i))), affordableRatio Y s i c r ∧ ∀ κ k' ι z:ℝ, Papal.freeR Y s i k κ → Papal.coolR Y s i k k' →
     authNear Y s i k f z → ∀ (φ:Pane (N s i)→ℝ) (Q:ℝ), Envelope φ → GaugeInvariant φ → LeadHall Y s i k f ι φ c r Q → (∫ x,launchPrice Y s i k f z κ k' ι φ x∂ prior SU.group (More (N s i))) ≤ Real.exp (Papal.gBaseR Y s i k+7* ξ s*sites (N s i)+Q):=by
 let V:=P.V; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let T:=|K|
 filter_upwards [(turnover P).eventually (atNear f hf f1 P.K.top.clip gaugeRules P.chart (V.L.mood 0).width P.K.top.paths_pos.le V.W.bar P.R.L T (abs_nonneg K)),(turnover P).eventually (outside_reserve P.R.L T P.chart (abs_nonneg K)),ciViGeometry P] with s hp hh h i k ht
 obtain ⟨W,y,u,c,r,w,v⟩:= h (Y.ir i); let n:= N s i; let L:= More n; let x:=θ s
 let R:= RootBook Y i k s; obtain ⟨p',z',v',b',_⟩:= Papal.prices_plot Y s i k ht; let F:=Y.uv k - s; let X:=V.L.H F; have he:R.p.threshold=temp x:=p' ▸ (Y.meter.boot s).1; have hm:=V.L.roof F
 have hc(i): (Precision.K (X.metric.acts L)) i i≤ T:= (YM.Fineness.stairEstimate X P.K.width.le hm.1.2.1 i).trans (le_abs_self _)
 refine ⟨c,r,⟨v.symm ▸ y, v.symm ▸ u,w,?_⟩,?_⟩
 · rw [v]; exact (hh R.beta b'.1 b'.2 W.val y u).1
 intro κ k' ι z0 hκ hk' h0 φ Q vH vg H
 unfold launchPrice launchHall; rw [frost_hires Y s i k ht]; apply nearTurns (V.L.mood F) ι R.beta κ k' z0 (shieldC x) (f*R.p.threshold) _ R.p φ vH; intro t
 obtain ⟨W0,q0,R1,R2,hW,hw,hL,hc0,p⟩:=H.copy t
 have hS:=hp W y u R.p R.beta b' he κ k' hκ hk' z0 h0 L c r w v (V.L.tied F) (V.L.mood F) (hm.2.1 L) V.W.reserve hc ι q0 R1 R2 (φ:=φ ∘ (pull t 0)) (show Envelope _ from ⟨vH.meas.comp (by apply (prior_pull _ _).measurable),vH.cost.choose, fun _=> vH.cost.choose_spec _⟩) (Push.Local.invariant_pull vg t 0) W0 hW hw hL p
 refine hS.trans (Real.exp_monotone ?_); have heq:Roof P.L R.beta L X + 7*meterC x * ↑(Fintype.card (Site L))=Papal.gBaseR Y s i k+7* ξ s*sites n:=by unfold Gleam.Roof Papal.gBaseR Fineness.gaugedBase L; rw [Pannier.shadowLie,sites_as_price] -- maps?
 linarith only [hc0,heq]

lemma nearCash (A f:ℝ)(hf:0<f): ∀ᶠ s in atTop, ∀ i k:ℕ, s≤Y.uv k→ authNear Y s i k f (Real.log (θ s)*A):=by
 let q:=P.K.top.clip; let P':= P.V; have he:= near_flake (q:=q) f hf; have ho:= BProof.coin_budget (b:=0) (e:=3/2) (c:=1) (f:=0) (by exact Or.inr (Or.inl ⟨rfl,(by norm_num)⟩)) A 1 zero_lt_one (a:=0)
 filter_upwards [(turnover P).eventually_gt_atTop (1:ℝ),(turnover P).eventually he,(turnover P).eventually ho] with s v p y i k t; let R:= RootBook Y i k s; let x:=θ s
 obtain ⟨h,_,_,hp,-⟩:= Papal.prices_plot Y s i k t
 have hv:R.p.threshold=temp x:=h ▸ (Y.meter.boot s).1
 apply le_trans _ (p R.p R.beta hp.1 hv); rw [mul_comm,← BProof.coinLog (show 1<x from v)] -- x abbrev
 simpa only [one_mul] using y.le

variable {I:Type*}[Fintype I]
local notation "gear" n:max=> Lattice.Face (Per (More n))

def ordinary (B:Finset (gear n))(t:ℝ)(U:Pane n) := ∀ e∈ B, SU.group.chord (faceValue U e) ≤ t
noncomputable def missAll (B:I→Finset (gear n))(τ:ℝ)(U:Pane n): ℕ:= (univ.filter fun i=> ¬ ordinary (B i) τ U).card
lemma ordinary_meas (B:Finset (gear n))(t:ℝ): MeasurableSet {x:Pane n| ¬ ordinary B t x}:=by
 rw [show {x:Pane n| ¬ordinary B t x}=⋃ i:↥B,{x:Pane n| i.val∈misdemean t x} from ?_]; exact MeasurableSet.iUnion fun i=> scan ..; ext x; simp [ordinary,misdemean]
lemma missedEnv (B:I→Finset (gear n))(τ t:ℝ): Envelope (fun U:Pane n=> t*(missAll B τ U):Pane n→ℝ):=by
 have he(i:Pane n): t*(missAll B τ i :ℝ)=∑ j:I, if ordinary (B j) τ i then 0 else t := by
    unfold missAll
    have he(j:I): (if ordinary (B j) τ i then 0 else t)=(if ¬ ordinary (B j) τ i then t else 0):= by simp
    simp_rw [he,←sum_filter]; rw [sum_const,nsmul_eq_mul,mul_comm]
 simp_rw [he]; exact Envelope.sum _ _ (fun j=> Envelope.piece (by simpa only [← Set.compl_setOf,compl_compl] using (ordinary_meas (B j) τ).compl) (Envelope.const _) (Envelope.const _))
lemma satellites (B:I→Finset (gear n))(τ:ℝ)(U:Pane n)(h:Set.PairwiseDisjoint Set.univ B): missAll B τ U ≤ (misdemean τ U).card :=by
 unfold missAll
 let X:= univ.filter fun i:I=>¬ordinary (B i) τ U
 let Z:=misdemean τ U
 have hw(i:↥X) : ∃ j:gear n, j∈ B i.val ∧ j∈ Z:=by
    have hp:¬ordinary (B i.val) τ U:=(mem_filter.mp i.2).2; unfold ordinary at hp; push Not at hp; obtain ⟨j,hH,hG⟩:=hp; exact ⟨j,hH,mem_filter.mpr ⟨mem_univ _,hG⟩⟩
 choose g g₁ g₂ using hw; let W (i:↥X): ↥Z:=⟨g i,g₂ i⟩; refine card_le_card_of_injective (f:=W) (fun i j v=> Subtype.ext ?_); by_contra t; apply disjoint_left.mp (h (Set.mem_univ _) (Set.mem_univ _) t) (g₁ i); rw [show g i=g j from congrArg Subtype.val v]; exact g₁ j
universe u
/-- Satellite toll. No volume slack needed. Still at arbitrary tests, buys also with h varying with
β. In particular the manuscript fixed P_∗ purchase at this phase is log(x)*P_∗,
and with the specified v=s apertures T from Q boxes (any number). `f=1/100` can be used
also when **T^lift** via rotations (def of the test sets A, incl all P pull faces).
"Disjoint" in force-user's own Face coordinates on this torus, ANY disjoint sets (not claim of
disjointness of particular transported sets until their layout hypotheses). Also bigger invoice
and more general sites purchasable the same way on that motion, no Mask recollection. Retains
both flake need and even the scene Mark exp purchase. -/
lemma prepaidMoment(f:ℝ)(p:0<f)(h:f≤1) : ∀ᶠ s in atTop, ∀ i k:ℕ,s ≤ Y.uv k → ∃ (c:Side) (r:Ratio c (More (N s i))), affordableRatio Y s i c r ∧ ∀ κ k' ι z:ℝ, 0≤z → Papal.freeR Y s i k κ → Papal.coolR Y s i k k' →
     authNear Y s i k f z → ∀ (I:Type u)[Fintype I](A:I→Finset (gear (N s i))), Set.PairwiseDisjoint Set.univ A → ∀ (φ:Pane (N s i)→ℝ) (Q:ℝ), Envelope φ → GaugeInvariant φ → LeadHall Y s i k f ι φ c r Q →
       (∫ U:Pane _, Papal.frost_bill Y s i k (θ s) κ k' U * Real.exp (z*(missAll A (f*(RootBook Y i k s).p.threshold) U)) * Real.exp (ι*φ U)∂ prior SU.group (More (N s i))) ≤ Real.exp (Papal.gBaseR Y s i k+7* ξ s*sites (N s i)+Q):=by
 filter_upwards [neritic Y f p h] with s H i k ht; obtain ⟨c,r,v,q⟩:= H i k ht; refine ⟨c,r,v,fun κ k' ι z h0 vκ vk' hZ I _ A h φ Q a t ℓ=> le_trans ?_ (q κ k' ι z vκ vk' hZ φ Q a t ℓ)⟩
 let τ:= f*(RootBook Y i k s).p.threshold; apply integral_mono ((((frost_now Y s i k ht κ k').mul ((missedEnv A τ z).exp)).mul (expEnv a _)).integrable (prior SU.group (More (N s i)))) ((launchPrice_env Y s i k ht f z κ k' ι φ a).integrable _); intro U
 exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (satellites A τ U h)) h0)) (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le)

-- A call leaving out φ even keeps same toll. Important in Gauge and Spin power cases.
theorem nearRent (f A:ℝ)(p:0<f)(h:f≤1)(a:0≤A): ∀ᶠ s in atTop,∀ i k:ℕ,s ≤ Y.uv k → ∀ κ k':ℝ,Papal.freeR Y s i k κ → Papal.coolR Y s i k k' →
     ∀ (I:Type u)[Fintype I](B:I→Finset (gear (N s i))), Set.PairwiseDisjoint Set.univ B →
       (∫ U:Pane _, Papal.frost_bill Y s i k (θ s) κ k' U * (θ s)^ (A * (missAll B (f*(RootBook Y i k s).p.threshold) U:ℝ)) ∂ prior SU.group (More (N s i))) ≤ Real.exp (Papal.gBaseR Y s i k+7* ξ s*sites (N s i)):=by
 filter_upwards [(turnover P).eventually_gt_atTop (1:ℝ),nearCash Y A f p,prepaidMoment.{u} Y f p h] with s u t v i k g κ k' p0 h0 I _ B hD
 obtain ⟨c,r,L,w⟩:= v i k g; have he: 1<θ s:=u; let χ:= f*(RootBook Y i k s).p.threshold; let F:= fun _ : Pane (N s i)=> (0:ℝ)
 have hL:= w κ k' 0 (Real.log (θ s)*A) (mul_nonneg (Real.log_nonneg he.le) a) p0 h0 (t i k g) I B hD F 0 (Envelope.const _) (fun _ _=>rfl) ?_
 · simpa only [Real.rpow_def_of_pos (zero_lt_one.trans he), ←mul_assoc (Real.log (θ s)), zero_mul, Real.exp_zero, mul_one,add_zero] using hL
 constructor; intro i₀; let W:= fun _ : Altar SU.group (More (N s i))=> (0:ℝ); refine ⟨W,0,0,0,contDiff_const, (fun i=>by simp [W]),(fun i=>by simp [W]),?_⟩; constructor
 · simp [plumeCost]
 intro a D x y U _ _ _ _; have h:0≤healthC (θ s):=(BProof.coin_pos ..).le; simp only [zero_mul, zero_add]; unfold trap trap_s; positivity
#print axioms nearRent
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
