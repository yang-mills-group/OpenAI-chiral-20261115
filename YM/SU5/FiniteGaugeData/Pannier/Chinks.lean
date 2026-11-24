import YM.SU5.FiniteGaugeData.Pannier.Husks
import YM.CF.Buffered.Merchant
import YM.CF.Continuum.PayTax
/-! # Absolute gauge charge (price heat-order-of-Haar separately).
Uses Axial tree. Each Estimate at the observing level s, qualified high enough,
including with a per bad-face price (which may be arbitrarily assigned after
geometry selected). -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace Pannier
open Graph Next.Rank LocalLimit
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V:Grace K R L)
variable {N M B:Side} {β:ℝ}
local notation "G₅"=>SU.group
local notation "c₀"=> K.top.clip
def roughness (t:ℝ)(U:Pane N): Finset (Face (Per (More N))):= univ.filter (fun x=> SU.group.chord (faceValue U x)>t)
def flakes (t:ℝ)(U:Pane N):ℝ := (roughness t U).card
private lemma coupling_eq (b:ℝ)(hb:0<b): b * coupling b^2=1:=by unfold coupling; rw [inv_pow,Real.sq_sqrt hb.le]; exact mul_inv_cancel₀ hb.ne'
private lemma coupling_le (v b:ℝ)(hv:0<v) (hb:v/2≤b): coupling b ≤ 2*coupling v :=by
 unfold coupling; have hb':0<b:= lt_of_lt_of_le (half_pos hv) hb
 have hp:=Real.sqrt_pos.mpr hv; have he:= Real.sqrt_pos.mpr hb'
 rw [← div_eq_mul_inv,inv_le_comm₀ (by positivity :(0:ℝ)< Real.sqrt b) (by positivity : (0:ℝ)< 2 / Real.sqrt v)] -- order? 
 simp only [inv_div]; nlinarith [Real.sq_sqrt hv.le,Real.sq_sqrt hb'.le]

private lemma striking (c:Clip) (η:ℝ) : ∀ᶠ v:ℝ in atTop,0<v ∧ ∀ b∈Set.Icc (v/2) (2*v), coupling b ≤ temp v ∧ η ≤ (temp v)/(2*coupling b/strength c):=by
 let w(v:ℝ):= Real.exp (Real.log (Real.log v)^2)
 have ht:Tendsto w atTop atTop:= Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))
 let e:=|η|
 let s:= strength c
 have he:= strength_pos c
 filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually_ge_atTop 2,ht.eventually_ge_atTop (4*e/s)] with v p q t
 refine ⟨p,fun b ⟨x,h⟩=>?_⟩
 let g:= coupling v
 have hg:0<g:=coupling_pos p
 have h':0<coupling b:= coupling_pos (lt_of_lt_of_le (half_pos p) x)
 have hx:=coupling_le v b p x
 change coupling b≤2*g at hx
 change coupling b ≤ g*w v ∧ η ≤ (g*w v)/(2*coupling b/s)
 constructor
 · exact hx.trans (by nlinarith only [hg,q])
 refine (le_abs_self _).trans ((le_div_iff₀ (by change 0<s at he; positivity : (0:ℝ)<2*coupling b/s)).mpr ?_)
 rw [←mul_div_assoc,div_le_iff₀ (show 0<s from he)]
 change e* _ ≤_
 have hu:= mul_le_mul_of_nonneg_left ((div_le_iff₀ (show 0<s from he)).1 t) hg.le
 have hv:= mul_le_mul_of_nonneg_left hx (abs_nonneg η)
 change e * _ ≤ e * _ at hv
 linarith

local notation "annual"=> strength K.top.clip
local notation "fI"=> Fintype.card (Face (Per (More N)))
local notation "cI"=> (fI:ℝ)
private lemma fleece (U:Pane N) (c:Clip) {t g E:ℝ} (hb:0<g) (ht: E ≤ t/(2*g/strength c)) :
    E*flakes t U ≤ ∑ i: Face (Per (More N)), SU.group.chord (faceValue U i)/(2*g/strength c) :=by
 let f (i:Face (Per (More N))):= SU.group.chord (faceValue U i)/(2*g/strength c)
 let F:=roughness t U; have hc:= strength_pos c; have h'I:(0:ℝ)<2*g/strength c:=by positivity
 have he(i):0≤f i:= div_nonneg (SU.group.chord_nonneg _) h'I.le
 refine le_trans (b:=∑ i∈F,f i) ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>he i))
 have hx:=sum_le_sum (s:=F) (f:=fun _=>E) (g:=f) fun i v=> ht.trans (div_le_div_of_nonneg_right ((show _>t from (mem_filter.mp v).2).le) h'I.le)
 rw [sum_const,nsmul_eq_mul] at hx; unfold flakes; rw [mul_comm]; exact hx

private def flame (c:Clip) (β:ℝ) (u:SU.group.El):ℝ := Real.exp (-(SU.group.chord u/(2*coupling β/strength c)))
-- purchase, for this V. Point estimate applies without `Envelope` or exponent offset yet.
include V in
private lemma surface_item (k:ℕ)(p:BudgetPoint)(v:ℝ)(hv:0<v)(e:p.threshold=temp v)(b:matchedX v β) (κ:ℝ)(tX:taxPart V p (2*v)≤1)
    (u:coupling β ≤ temp v)(hh:κ ≤ temp v /(2*coupling β / strength K.top.clip))(U:Pane N):
    Real.exp (-(V.L.path k).inChannels K.top.clip p β U + κ*flakes p.threshold U) ≤ Real.exp ((Fintype.card PlaqAxes+ (1:ℝ))*sites N) * (∏ i:Face (Per (More N)), flame K.top.clip β (faceValue U i)) :=by
 let c:=annual
 let t:= coupling β / c
 have he:=strength_pos c₀
 have hx:0<β:= lt_of_lt_of_le (half_pos hv) b.1; have hq:= coupling_pos hx
 have hp:= (CF.Window.per_channel (N:=More N) (V.L.mood k) hq (coupling_eq β hx) (e.symm ▸ u) U)
 have hl:= fleece U c₀ hq (show κ≤ p.threshold / (2*coupling β/strength K.top.clip) from e.symm ▸ hh)
 let S : ℝ:= sites N
 have ha : cI=(Fintype.card PlaqAxes:ℝ)*S:=by
    rw [show fI= Fintype.card (Site (More N))*Fintype.card PlaqAxes from Fintype.card_prod ..,site_card]; unfold S sites; push_cast; ring
 have hz:0≤S:= zero_le_one.trans (sites_pos _)
 have ht: taxY (More N) β p.threshold K.top.paths V.W.bar ≤ S := (tax_price V N b.2).trans ((mul_le_mul_of_nonneg_right tX hz).trans_eq (one_mul _))
 unfold flame; rw [← Real.exp_sum,←Real.exp_add]
 apply Real.exp_monotone
 let F(i:Face (Per (More N))):=SU.group.chord (faceValue U i)/(2*coupling β/c)
 change -(V.L.path k).inChannels _ _ _ _+_≤ ((Fintype.card PlaqAxes:ℝ)+1)* S+∑ i,-F i
 have heq(i: Face (Per (More N))): SU.group.chord (faceValue U i)/(coupling β/annual) = 2*F i:=by unfold F c; field
 simp_rw [ha,heq,←mul_sum] at hp
 change κ* _ ≤ ∑ i,F i at hl
 rw [sum_neg_distrib]; linarith

local notation "dG" => SU.group.lieDim
local notation "Lk"=> Module.finrank ℝ SU.group.Color
-- upper of the gauge frame. Keep abs tax pre-H: tends zero at sufficiently high resolution.
private abbrev bloomH (U : Clip) (Z:HaarBudget SU.group) := Z.big*(4/Next.Rank.strength U)^dG
private lemma geometry_haar (U:Clip)(Z:HaarBudget SU.group) :0< bloomH U Z:= mul_pos (lt_of_lt_of_le zero_lt_one Z.big_ge) (pow_pos (div_pos (by norm_num) (strength_pos _)) _)
private lemma cover_gauge (U:Clip)(Z:HaarBudget SU.group)(v:ℝ)(hx:0<v)(b:matchedX v β) :
   (∫ V: Pane N, (∏ i:Face (Per (More N)), flame U β (faceValue V i))∂prior G₅ (More N)) ≤ Real.exp (((3*(sites N)-3))*( Real.log (bloomH U Z) - halfLie G₅*Real.log v)):=by
 let f:= flame U β; let g:= coupling β; let t:= 2*g/strength U
 have hp :0<g:= coupling_pos (lt_of_lt_of_le (half_pos hx) b.1); have he:0<t:=div_pos (by positivity) (strength_pos _); have hh:Continuous f:= by unfold f flame; fun_prop
 have hv(U): f U ≤1:= Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (SU.group.chord_nonneg U) he.le)); have hl(U) : 0 ≤ f U:= (Real.exp_pos _).le
 have ht:1<(More N).val:=by have h:=N.property; exact lt_of_lt_of_le one_lt_two (Nat.le_mul_of_pos_left 2 h)
 let x:= coupling v; have hg:0<x:=coupling_pos hx; have hw:t≤ (4/strength U)*x:=by
   have H:t ≤ 4*x/strength U:= div_le_div_of_nonneg_right (by linarith [show g≤2*x from coupling_le v β hx b.1]) (strength_pos _).le; exact H.trans_eq (by ring)
 -- enough small factor per pivot
 have hC:(∫ y,f y ∂SU.group.probHaar) ≤ bloomH U Z*x^dG:=by
    calc _ ≤ _ := Z.high t he
         _ ≤ Z.big*((4/strength U)*x)^dG := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le hw _) (zero_le_one.trans Z.big_ge)
         _ = _ := by rw [mul_pow]; ring
 apply (Next.Rank.Axial.elimination ht f hh hl hv).trans (le_trans (pow_le_pow_left₀ (integral_nonneg hl) hC _) ?_)
 have hsize: ((↑(3*Fintype.card (Site (More N))-3):ℝ))=3*sites N-3:=by
   have h := Fintype.card_pos (α:=Site (More N)); rw [Nat.cast_sub (by omega),site_card,Nat.cast_mul, Nat.cast_pow]; unfold sites; push_cast; rfl
 have he: halfLie SU.group= dG/ (2:ℝ):= by rw [shadowLie]; simp only [Gauge.ColorIndex,Fintype.card_fin]
 rw [←hsize, Real.exp_nat_mul]; refine Eq.le ((congrArg (fun c:ℝ=> c^(3*Fintype.card (Site (More N))-3)) ?_)) -- number notation
 rw [show Real.log _-halfLie SU.group*Real.log v= Real.log (bloomH U Z)+dG*Real.log x by rw [he]; unfold x coupling; rw [Real.log_inv,Real.log_sqrt hx.le]; ring,Real.exp_add,Real.exp_log (geometry_haar ..),Real.exp_nat_mul,Real.exp_log hg]

/-- estimate on ℂ-valued integrals on the single observing city's
true prior. Kappa real per declared bad observation-face, alpha cost per gauge site. -/
def SugarBill (V:Grace K R L)(D:ℝ) (N:Side)(p:BudgetPoint)(k:ℕ) (x b κ α:ℝ):Prop :=
    ∀ (f:Orbit N→ℂ), Integrable f (city N) →
      (∀ u:Orbit N, ‖f u‖≤ Real.exp ( -(V.L.path k).inChannels K.top.clip p b u.1 + κ*flakes p.threshold u.1 + α*sites N )) →
      ‖∫ u,f u∂city N‖ ≤ Real.exp ((α+D-LocalLimit.mulch x)*sites N)
local notation "U₀" => (K.top.clip)
local notation "Θ" => (V.L.path)
private abbrev canopy (U:Clip)(Z:HaarBudget SU.group):ℝ:= (Fintype.card PlaqAxes + (1:ℝ)) +3*|Real.log (bloomH U Z)|+1
include V
private lemma bodega (Z:HaarBudget SU.group) (p:BudgetPoint)(k:ℕ)(v:ℝ)(hv:0<v)(e:p.threshold=temp v)(b:matchedX v β) (κ α:ℝ)(tX:taxPart V p (2*v)≤1) (u:coupling β ≤ temp v)(hh:κ ≤ temp v /(2*coupling β / strength K.top.clip))(V0:3*halfLie SU.group*Real.log v ≤ sites N): SugarBill V (canopy K.top.clip Z) N p k v β κ α:=by
 intro f hF fH
 let X:= sites N; let c:ℝ:= Fintype.card PlaqAxes+1
 -- careful Nat add? specify
 let φ(U:Pane N):= Real.exp ((α+c)*X) * ∏ i:Face (Per (More N)), flame U₀ β (faceValue U i)
 have hL:Continuous φ:=by
    apply continuous_const.mul; exact continuous_finsetProd _ (fun i _=> (show Continuous (flame U₀ β) from by unfold flame; fun_prop).comp (continuous_travel _ _))
 have hφ: Integrable φ (prior G5 (More N)):= hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hx: Integrable (fun u:Orbit N=>φ u.1) (city N):= ((measurePreserving_fst (μ:=prior G5 (More N)) (ν:=depot N)).integrable_comp hφ.aestronglyMeasurable).mpr hφ
 apply (norm_integral_le_integral_norm ..).trans; apply le_trans (b:=∫ u:Orbit N,φ u.1∂city N)
 · apply integral_mono hF.norm hx; intro y; apply (fH y).trans; unfold φ; rw [Real.exp_add,add_mul]; rw [Real.exp_add (x:=α*X) (y:=c*X)]
   apply (mul_le_mul_of_nonneg_right (surface_item V k p v hv e b κ tX u hh y.1) (Real.exp_pos (α*X)).le).trans
   unfold X c; apply le_of_eq; ring
 rw [CF.Window.usesPrior _ hφ]; unfold φ; rw [integral_const_mul]
 apply le_trans (mul_le_mul_of_nonneg_left (cover_gauge (N:=N) K.top.clip Z v hv b) (Real.exp_pos _).le)
 rw [←Real.exp_add]; apply Real.exp_monotone
 let J:= Real.log (bloomH c₀ Z); unfold canopy mulch; have hs:0 ≤ (3:ℝ)*X-3:= by nlinarith [show 1≤ X from sites_pos _]
 have he':(3*X-3)*J ≤ 3*|J| * X:= by nlinarith only [abs_nonneg J,mul_le_mul_of_nonneg_left (le_abs_self J) hs]
 change (α+c)*X+(3*X-3)*(J-halfLie _*Real.log v) ≤ (α+(c+3*|J|+1)-_)* X; change _ ≤ X at V0; linarith

-- actually upper comparison's permission (side threshold after stopping level)
lemma acquires (Z:HaarBudget SU.group) (κ:ℝ):∀ᶠ x:ℝ in atTop,∃ n:ℕ,∀ (p:BudgetPoint)(k:ℕ)(b:ℝ)(α:ℝ)(N:Side), matchedX x b → p.threshold=temp x → n≤ N.val → SugarBill V (canopy K.top.clip Z) N p k x b κ α :=by
 let f(x:ℝ):=x*((2*K.top.paths)*temp x^3+ (2*K.top.paths)*temp x^4)+V.W.bar*temp x^2
 have ht:Tendsto f atTop (𝓝 0) := Buffered.Alloy.Tariff.uproot ..
 filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one),striking c₀ κ] with x h ⟨p,t⟩
 obtain ⟨n,hp⟩:= exists_nat_gt (3*halfLie SU.group*Real.log x)
 refine ⟨n,fun p' k b α N t' e H=> ?_⟩
 obtain ⟨h1,h2⟩:= t b t'
 refine bodega V Z p' k x p e t' κ α ?_ h1 h2 (hp.le.trans ?_)
 · unfold taxPart; rw [e]; apply le_trans (le_of_eq ?_) h; unfold f; ring
 have hh: n≤ (More N).val:= H.trans (Nat.le_mul_of_pos_right _ (by decide : (0:ℕ)<2)); exact (show (n:ℝ)≤ (More N).val from Nat.cast_le.mpr hh).trans (le_self_pow₀ (Nat.one_le_cast.mpr (More N).property) (by decide : (4:ℕ)≠0))

omit V in
def blossom (K:Teller SU.group):ℝ:= canopy K.top.clip (exists_budget SU.group).some
omit V in
lemma blossom_ok (K:Teller SU.group):0≤ blossom K:=by unfold blossom canopy; positivity
lemma gaugedBudget (κ:ℝ):∀ᶠ x:ℝ in atTop,∃ n:ℕ,∀ (p:BudgetPoint)(k:ℕ)(b:ℝ)(α:ℝ)(N:Side), matchedX x b → p.threshold=temp x → n≤ N.val → SugarBill V (blossom K) N p k x b κ α := acquires V (exists_budget SU.group).some _
end Pannier
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.Pannier.gaugedBudget
