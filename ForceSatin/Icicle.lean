import ForceSatin.Moon
import ForceSatin.Falcon
set_option autoImplicit false
set_option maxHeartbeats 520000
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
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H:Bed} {Z:PathData SU.group} {p:BudgetPoint} {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H Z)(L:Side)
variable {v' τ:ℝ}{A:Support cN}{D:Finset (Cell (More N))}(M0:Floor H q (More N) τ v') (O:Bid.Sworn H (More N) SU.group)
open ProbabilityTheory
-- goblet has FIXED terms sizes only in each b; entry of warpS product is path component of allowed reps.
abbrev LensGauge (N:Side):= ShapeLight SU.group (More N)
structure Goblet (N:Side) where
 f : FC (Single N)
 lo : List (LensGauge N)
 cabin : List (CablePrice N)
 mask : List (ℝ × Support (More N)) -- CAN vary. VOTE actual thresholds on masks
abbrev glare (K:Goblet N)(U:Pane N) (y:ℝ):ℝ:= (K.lo.map (fun i=>colorLeg i y U)).prod
def onGlow (K:Goblet N)(U:Pane N):Prop:=∀ p∈K.mask,pingS p.1 p.2 U
abbrev carG (K:Goblet N)(U:Pane N):= cadence K.cabin _root_.id U
noncomputable def craft (K:Goblet N)(y:ℝ)(U:Pane N): FC (Single N):= if onGlow K U then (carG K U*(glare K U y:ℂ)) • K.f else 0
abbrev gust (K:Goblet N)(Q:Wave (Single N)) (w:ℝ):ℂ:=carG K 1 * (w:ℂ) * alleyR (mateK N) Q K.f
noncomputable abbrev wickedF (G:Goblet N)(Y:ℝ)(H₁:Z.Bounds q η CS W)(P:Attached H Z)(Q:Wave (Single N)) : ℂ:= gust G Q (axisSumC G.lo _root_.id H₁ P Y)
-- Attach B infer Bed? underscore can't be inferred from Z. use variable.
structure Scaled (K:Goblet N)(S:Support (More N))(m:ℕ)(t x:ℝ):Prop where
 spin : Street S m 1 K.f
 wick : K.lo.length ≤ m
 cabin : K.cabin.length ≤ m
 lodge : ∀ i∈K.lo, Lattice.halo (colorCash SU.group) {i.1.1} ⊆ S
 stroll : ∀ i∈K.cabin, quilt i ⊆ S ∧ (i.walk.length:ℝ) ≤ voucher x
 fund : ∀ i∈K.mask,i.2⊆S ∧ t*temp x ≤ i.1 -- t with p actual
 every : ∀ i∈ K.lo, ∃ p∈K.mask, i.1.1∈p.2 ∧ p.1 ≤ temp x
namespace Scaled
variable {T S} {m:ℕ} {G:Goblet N} (h:Scaled G S m t x) {b C:ℝ}(δ:0<b) (mail:CF.Papyrus.Franc.postage 4 b) (hx:Celery L m q R x b)(v:|y| ≤ fabric x)
variable (hp:p.threshold=temp x) (Q:Wave (Single N)){M:Tulip.Male}(V:IsStarProjection (FlatPaneP 4 M N))(J:Sea (FlatPaneP 4 M N) Q) (bp:matchedX x β)
include hx h v
lemma colorSense {U:Pane N}(g:onGlow G U)(i:LensGauge N)(y0:i∈ G.lo): |colorLeg i y U|≤ ledgerV m x:= by
 obtain ⟨p₀,a,z,h⟩:= h.every i y0
 exact ((color_cash i U (g p₀ a) z |>.trans (mul_le_mul_of_nonneg_left h (abs_nonneg _))).trans (mul_le_mul_of_nonneg_right v (Work.E09.temp_pos (zero_lt_one.trans_le hx.range)).le)).trans hx.cap
include δ
lemma glowing (U:Pane N): Street S m (staple x) (craft G y U):=by
 let V:=ledgerV m x; have hp:1 ≤ V:= Real.one_le_rpow hx.range (branch_p ..).le; have hz:0≤ V:=zero_le_one.trans hp; unfold craft
 split
 next t' =>
    have hk:|glare G U y| ≤ V^m:= (Lull.low (fun i=> colorLeg i y U) G.lo hz (colorSense R L h hx v t')).trans (pow_le_pow_right₀ hp h.wick)
    apply Street.enlarge _ le_rfl (Street.scale _ h.spin)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_one]; apply le_trans (mul_le_mul (carriage ..) hk (abs_nonneg _) zero_le_one); apply le_trans _ hx.perk; have hi:= ivyFloor δ.le m; rw [one_mul]; exact (pow_le_pow_left₀ hz (by change V≤2*V; linarith only [hz]) _).trans (le_mul_of_one_le_right (by unfold ledgerV; have v:0 < x:= zero_lt_one.trans_le hx.range; positivity) hi)
 rw [←show (0:ℂ) • (1:FC (Single N))=0 from zero_smul ℂ _]; apply Street.enlarge _ (Nat.zero_le _) (Street.scale _ Street.one); rw [norm_zero,zero_mul]; exact (Real.rpow_nonneg (zero_le_one.trans hx.range) _)
variable (σ:Signed)(b1:Seat N){k t':ℝ} {x':Altar SU.group (More N)}
noncomputable abbrev coreWhiff (G:Goblet N)(y:ℝ)(σ:Signed)(b:Seat N)(Q:Wave (Single N))(q:Clip)(k:ℝ)(x:Altar SU.group (More N)):ℂ:= gust G Q (Solace.prism G.lo q k y _root_.id σ b x)
omit hx h v δ in
lemma core_regular (y:ℝ): ContDiff ℝ 1 (coreWhiff G y σ b1 Q q k):=by
 unfold coreWhiff gust; exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (prismDiff ..))).mul contDiff_const
-- h include remove so lemma arity
include V J mail O M0
omit v in
lemma wickPost (g: |k| ≤ 4) : ‖wickedF G k B P₁ Q‖ ≤ staple x:=by
 have he:= bonnetBound B P₁ M0 O (W:=G.lo) (f:=_root_.id) 4 g h.wick -- need include O M0
 have hv:=palmPrice δ mail m h.spin V J; have hz:= ivyFloor δ.le m
 unfold wickedF gust; simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact (mul_le_mul ( (mul_le_mul (carriage ..) le_rfl (abs_nonneg _) zero_le_one).trans ((one_mul ..).trans_le he)) hv (norm_nonneg _) (by exact (abs_nonneg ..).trans he)).trans hx.wick
include bp hp
omit O M0 in
lemma looping (f: Tiling cN N r)(i: coveredWidth L x r) (U:f.forest.Slice SU.group) (X Y:Exterior.fieldDir SU.group (More N) 1)(rate0:D=weak (t*p.threshold) (f.forest.drape U))(ha:A=broken r (sax x) (f.forest.drape U))(z: fullLease A D (S.image (affine σ b1)) r (radiusB x))(Hc:TrustLogs (X+Y) (f.forest.drape U) r A (tuition L x)) : let Z':= y*coupling β;
    ‖stencilC Q σ b1 (craft G y) (f.forest.drape U) - coreWhiff G Z' σ b1 Q q (ledgerV m x) (starFee B P₁ r A D (radiusB x) Y β X)‖ ≤ spry x:=by
 intro Z'; let x':= starFee B P₁ r A D (radiusB x) Y β X; let U':=f.forest.drape U; let H:=Lattice.pull σ b1 U'
 let κ:=ledgerV m x; have hK:1≤κ:=Real.one_le_rpow hx.range (branch_p ..).le; have hκ:0<κ:=zero_lt_one.trans_le hK; have hb:β>0:=(half_pos (zero_lt_one.trans_le hx.range)).trans_le bp.1
 have hp0:onGlow G H:=fun i a=> pingClear σ b1 (rate0 ▸ z) (le_trans (by rw [hp]) (h.fund i a).2) (h.fund i a).1 -- specify include hp bp
 have ht: ‖alleyR (mateK N) Q G.f‖ ≤ _:=palmPrice δ mail m h.spin V J
 let mK:= (2*κ)^m
 let r₁:=tuition L x
 let s:ℝ:= m*(flange*(voucher x*r₁)); have hv: x≥0:=zero_le_one.trans hx.range
 have hs:‖carG G H-carG G 1‖ ≤ s:= tracks S f U σ b1 (sax x) hx.sax_p _ (ha ▸ z) _root_.id G.cabin (fun i a=>(h.stroll i a).1) _ _ (Real.rpow_nonneg hv _) (fun i a=>(h.stroll i a).2) (hx.onTree _ i.2) hx.charm h.cabin
 let a:= glare G H y; let c:= Solace.prism G.lo q κ Z' _root_.id σ b1 x'; let s0:= fabric x * slotError R (colorCash SU.group) r₁; let r:ℝ:=Lull.loan*s0; let l:= m*mK*r; have hp₁:0≤ s:=mul_nonneg (by positivity : 0≤ (m:ℝ)) (mul_nonneg flange_p.le (mul_nonneg (Real.rpow_nonneg hv _) hx.charm))
 have hc:|c| ≤ mK:=compareFeeU σ b1 _ _ hK Z' h.wick _
 have he: |a-c| ≤ l:=by
    have ho:0≤r:= mul_nonneg Lull.loan.prop (mul_nonneg ((abs_nonneg _).trans v) (slot_zero ..)); have ho':1 ≤ 2*κ:= (by linarith only [hK])
    let A(i:LensGauge N):= colorLeg i y H; let g(i:LensGauge N):=duskLeg Z' σ b1 q i x'; have he(i)(v:i∈G.lo):|A i|≤κ:= colorSense R L h hx ‹|y|≤fabric x› hp0 i v
    apply le_trans (compareAt A (fun i=> scarfLens κ (g i)) G.lo ho' ho (fun i a=> (he i a).trans (show κ ≤ 2*κ from by linarith only [hK])) (fun i _=>(velvetBound κ _ hκ).2.1) (fun i a'=>?_))
    · unfold l mK; gcongr <;> apply h.wick
    have E:stint _ _ _ _ (caper i σ b1):=z (affine σ b1 i.1.1) (mem_image_of_mem _ (h.lodge i a' (halo_subset _ _ (mem_singleton_self _))))
    have hi:|A i-g i|≤ s0:=(grant_lane B P₁ i σ b1 Hc hx.charm hx.radius hb E hx.sec).trans (mul_le_mul_of_nonneg_right v (slot_zero ..)); rw [←(velvetBound κ _ hκ).2.2 (he i a')]; exact (hose_lp _ _ _ hκ).trans (mul_le_mul_of_nonneg_left hi Lull.loan.prop)
 unfold stencilC; rw [show craft G y (pull σ b1 (f.forest.drape U))=_ from if_pos (_ : onGlow G H)]; swap; · exact hp0
 let B:=alleyR (mateK N) Q; let Y₁:=B G.f
 rw [map_smul,smul_eq_mul]; change ‖carG G H*(a:ℂ)*Y₁-carG G 1*(c:ℂ)*Y₁‖ ≤ _
 rw [←sub_mul,show carG G H*(a:ℂ)-carG G 1*(c:ℂ)=carG G H*((a-c:ℝ):ℂ)+(carG G H-carG G 1)*(c:ℂ) from (by push_cast; ring),norm_mul]; refine (mul_le_mul ( (norm_add_le ..).trans ?_) ht (norm_nonneg _) (show 0≤l+s*mK from add_nonneg ((abs_nonneg _).trans he) (mul_nonneg hp₁ ((abs_nonneg _).trans hc)))).trans hx.curvature
 rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real]; exact add_le_add ((mul_le_mul (carriage ..) he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)) (mul_le_mul hs hc (abs_nonneg _) hp₁)
omit hp in
lemma inScript : let G0:= coreWhiff G (y*coupling β) σ b1 Q q (ledgerV m x)
    ContDiff ℝ 1 G0 ∧ (∀ u,‖G0 u‖ ≤ staple x) ∧ (∀ u v,‖G0 u-G0 v‖ ≤ staple x*traceNorm (S.image (affine σ b1)) (u-v)) ∧
       ‖stamenMean B P₁ G0 - wickedF G (y*coupling β) B P₁ Q‖ ≤ spry x:=by
 intro F; let y':= y*coupling β; let z:= wickedF G y' B P₁ Q
 let V':= ledgerV m x; have ht:1≤ V':=Real.one_le_rpow hx.range (branch_p ..).le; let e:= Solace.prism G.lo q V' y' _root_.id σ b1; let J':=alleyR (mateK N) Q G.f; have hh:‖J'‖≤ ivy b m:= palmPrice δ mail m h.spin V J
 let u:= (2*V')^m; have hu(x):|e x| ≤ u:= compareFeeU σ b1 _ _ ht y' h.wick x; have hy:= stipend hx.range bp v
 let P₀:=carG G 1; have he(v:ℂ): ‖P₀*v*J'‖ ≤ ‖v‖*ivy b m:=by rw [norm_mul,norm_mul]; exact mul_le_mul ((mul_le_mul (carriage ..) le_rfl (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) hh (norm_nonneg _) (norm_nonneg _)
 refine ⟨core_regular Q σ b1 (G:=G) (y*coupling β), fun x=> ((he (e x)).trans (mul_le_mul_of_nonneg_right ((Complex.norm_real _).trans_le (hu x)) (zero_le_one.trans (ivyFloor δ.le m)))).trans hx.perk,fun x z=>?_,?_⟩
 · unfold F coreWhiff gust; rw [←sub_mul,←mul_sub,←Complex.ofReal_sub]; apply (he _).trans; let k:= traceNorm (S.image (affine σ b1)) (x-z); have hkp:0 ≤ k:= traceNorm_p ..; rw [Complex.norm_real]; have E: |e x-e z| ≤ m*u*(Lull.loan*chordAllowance q 4)*k:= compareFeeV σ b1 _ _ ht y' hy h.wick h.lodge x z
   refine (mul_le_mul_of_nonneg_right E (zero_le_one.trans (ivyFloor δ.le m))).trans ?_; refine le_trans (Eq.le ?_) (mul_le_mul_of_nonneg_right hx.cusp hkp); unfold u; ring
 unfold stamenMean; let K:= (stamen B P₁ (More N)).starProjection; let d:= axisSumC G.lo _root_.id B P₁ y'; let μ:= stdGaussian (Altar G5 (More N)); let W:= ∫ i,e (K i)∂μ
 have hp: |d-W| ≤_:= compareFee B P₁ M0 O σ b1 _ _ ht y' hy h.wick (bark m) -- let annotations maybe infer RHS
 change ‖(∫ i,P₀*(e (K i):ℂ)* J'∂μ)-P₀*(d:ℂ)*J'‖≤ _; rw [integral_mul_const,integral_const_mul,integral_complex_ofReal,←sub_mul,←mul_sub,←Complex.ofReal_sub]; apply (he _).trans; rw [Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]; exact (mul_le_mul_of_nonneg_right hp (zero_le_one.trans (ivyFloor δ.le m))).trans hx.finu
#print axioms glowing
#print axioms looping
#print axioms inScript
end Scaled
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
