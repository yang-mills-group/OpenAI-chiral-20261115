import YM.SU5.Registration.Affine.HaloBudget
import YM.SU5.Registration.Affine.BaseTickets
import YM.SU5.Registration.Affine.Collateral
/-!
  # The Euclidean, late-consultation fields over our M4 map
  Unprojected ColorHil -> G uses coherence of this same elected character. G
  has powers w.r.t. actual physical clock, not arbitrary GNS Hilbert built per axis.
  Work with WPermit estimates on ANY stamped family with coefficients at its
  native printed height. Use to compute Schwinger prices and ordered transfer.
  Projection in pricing sharp readings from G is only qualified where authorized
  (`Ellis` & all-coordinate separations etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
-- a fixed (after purchase) extra normalization. Then qualify cap & all estimates where used. Uses ANY x for powering (allow per x), not requiring power uniform here but still threshold norms processed over all x. Chosen character held exactly.
noncomputable def Swatch.boost (W:P.Swatch)(c:ℂ) : P.Swatch:= { fieldA:= W.fieldA, rate:= fun i=> c*W.rate i }
lemma Swatch.boost_finishes (W:P.Swatch)(c:ℂ)(p:W.Finishes): (W.boost P c).Finishes:=p
lemma Swatch.boost_stages (W:P.Swatch)(c:ℂ)(s t:ℝ≥0)(i:ℕ): (W.boost P c).Wstage x a s t i=c • W.Wstage x a s t i:= (smul_smul ..).symm
lemma Swatch.WPermit.boost (W:P.Swatch)(c:ℂ)(h:W.WPermit x a): (W.boost P c).WPermit x a:=by
 refine ⟨h.thin,?_,fun t u=>?_⟩
 · obtain ⟨k,C,e,s⟩:= h.budget; refine ⟨k,‖c‖*C,mul_nonneg (norm_nonneg _) e,fun t p q=>?_⟩; filter_upwards [s t p q] with i u; rw [W.boost_stages,norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left u (norm_nonneg _)
 simp_rw [W.boost_stages]; exact (Flying.scaled (tendsto_const_nhds (x:=c)) (h.arriving _ u)).Cauchy
lemma ModSpaces.extend (W:P.Swatch)(c:ℂ)(p:P.ModSpaces a W): P.ModSpaces a (W.boost P c):=by
 refine ⟨p.1,fun t u r q=>?_⟩
 let b':=‖c‖; have hb:0≤b':= norm_nonneg _; let ε:= r/(b'+1); have he:0<ε:=by unfold ε; positivity
 obtain ⟨g,h,z,v⟩:= p.2 t u ε he; refine ⟨g,fun i=>c • h i,z,?_⟩
 filter_upwards [v] with k v i; rw [W.boost_stages P i a,← P.cane_scaled, dist_eq_norm, ←smul_sub, norm_smul,← dist_eq_norm]; have hf:ε*(b'+1)=r:= div_mul_cancel₀ _ (by positivity); exact (mul_le_mul_of_nonneg_left (v i) hb).trans (by change b'*ε≤r; linarith only [hf,he])

-- *** Price a weighted coalition issue at ALL x ***
variable (Q:P.Register)
variable (g h i:ℕ)
section
variable (v:ℕ→ℕ)(q:StrictMono v)(b:ℕ→ℝ)(V:Coalition)
local notation "M"=>timeMesh P.par
local notation "N" s:max w:max=> whenly M s w
lemma stage_weather (y:P.Spectrum0 3) (l:List Axis)(t:ℝ≥0)(p:whenly (timeMesh P.par) (v i) P.roomy ≤ t):
    P.stageH a (P.advocate 3 x a) ((P.pleading y g h i V v b q).pivot P l) t t= ∑ j'∈ V.voters,(V.w j':ℂ) • ((P.rewardK g h:ℂ) • ((b (i+j'):ℂ) • P.stageH a (P.advocate 3 x a) ((P.basePlay y g (v (i+j'))).pivot P l) t t)):= by
 -- proof from Rise/EntireCanvas

 let s:= parliament i V v; let y₀(k:ℕ):=P.basePlay y g (v (i+k)); let D:=P.basePlay y g (v i); let R(a:ℕ):= V.w a * (P.rewardK g h*b (i+a)); let w:=D.zoom P s
 let T':= P.pleading y g h i V v b q
 have w' : N s (w a)=N (v i) P.roomy:= P.zoomMoney a D s (le_max_left ..)
 have hb(k:ℕ)(p:k∈ V.voters): (y₀ k).s ≤ s:= le_trans (le_sup (f:=fun k=>v (i+k)) p) (le_max_right ..)
 -- prove zoom from steps; avoid elimination reducing definitions of `pleading` in theorem passed args except at last
 have ht(k:ℕ)(e:k∈V.voters)(a:Axis): (y₀ k).zoom P s a≤ w a:=by
    -- p.time monotone. Can use zoom def arithmetic
    have he:v i≤ v (i+k):=q.monotone (by omega); apply Nat.mul_le_mul_right P.roomy (Nat.pow_le_pow_right P.par.R.L.property (by change s-v (i+k) ≤ s-v i; omega)) -- syntax tune
 refine (P.pivot_boxes a (P.advocate 3 x a) y₀ V.voters s w hb (fun i=> D.zoomP P i s) ht R l t (w'.trans_le p)).trans ?_
 refine sum_congr rfl fun k h=>?_ ; unfold R; rw [Complex.ofReal_mul, Complex.ofReal_mul,mul_smul,mul_smul]; -- maybe h shadow

end
variable (v:ℕ→ℕ)(q:StrictMono v)(u:ℕ→(ℕ×ℕ)→ℝ)(V:ℕ→ Coalition)(y:P.Spectrum0 3)(l:List Axis)
local notation "K₀"=>P.cinema y g h v u V q
local notation "A₀" p:max=> Swatch.ordinary (fun i=> ((K₀ i).pivot P p))
local notation "Υ" L:max=> P.baseFlight y g h L u v
local notation "B₀" L:max=> (Υ L).boost P (P.rewardK g h:ℂ)
local notation "R'"=> P.advocate 3
lemma passport_mantle : P.Mantle a (A₀ l) (B₀ l) V:=by
 refine ⟨fun j=>?_,fun t h₀=>?_⟩
 ·
   refine (P.legislative_shelf j y g h v u q V).congr fun i=>?_
   refine NNReal.eq ?_; rw [← Apron.width_real]; change _= ((((K₀ i).pivot P l).allowance P j):ℝ); rw [←Apron.width_real, Apron.pivot_w] -- rewrite on lhs tune
 filter_upwards [(P.width_floor v q).eventually (ge_mem_nhds h₀)] with i u₀ x
 change (1:ℂ) • P.toStageG a (R' x a) (P.stageH a (R' x a) ((K₀ i).pivot P l) t t)= _; rw [one_smul]; rw [show P.stageH a (R' x a) ((K₀ i).pivot P l) t t= _ from P.stage_weather x a g h i v q (fun n=> u n (g,h)) (V i) y l t u₀]; unfold SatinRegistration.offer; rw [map_sum]; refine sum_congr rfl fun k z=> ?_
 rw [map_smul,map_smul]; dsimp only; rw [(P.baseFlight y g h l u v).boost_stages P x a,P.base_ride]; unfold tenderH; rfl

-- All epoch feasibility. Develop WP not changing list, parameter structure carries passports ANY gauge fields (incl reflect y-taken). h1 argument not unnecessary if includes powers for W all x.
universe uΩ
structure PlanetaryG (P:Spine)(A:ℕ→P.Apron) : Prop where
 purchase : ∀ a:Axis,∀ l:List Axis,let W:= ordinary (fun i=>(A i).pivot P l); P.ThresholdPrice a W ∧ ∀ x:P.Spectrum0 3,W.WPermit x a
 reads {I:Type uΩ}(a:Axis)(f:I→ List Axis)(B:I→P.Swatch)(t:∀ i x,(B i).WPermit x a)(L:List I)(p:I→Vantage)(_:∀ i,B i=ordinary (fun k=>(A k).pivot P (f i)))(_:LightsCross a L p)(_:StarCluster L p):P.Passport a L B t p
open Papal Regis.Head.Brecht
-- Universe parameter only costs this same transaction; can generalize in proof drawing instance (PS / dummy flexible).
include Q
lemma planet_purchase {E C:ℝ} (S₁:P.NightCop)(L':Odd P.par.R.L.val) (z:Earnings P E C g h v u) (w:PaidSubsidy g h u)(tq:∀ᶠ s:ℕ in atTop, treasury E C P s (s+1) (s+1)) : PlanetaryG.{uΩ} P (K₀):=by
 -- `u` schema -> reader any list
 have t(a:Axis)(l:List Axis): P.ThresholdPrice a (B₀ l) ∧ P.ModSpaces a (B₀ l) ∧ (∀ x:P.Spectrum0 3, (B₀ l).WPermit x a) :=by
    obtain ⟨a',p,vp⟩:= P.base_grant a y g h l u v S₁ L' z tq w; let h₀:= ModSpaces.extend P a _ (P.rewardK g h:ℂ) p; exact ⟨ModSpaces.funds P a _ h₀,h₀,fun x=> WPermit.boost P x a (Υ l) _ (vp x)⟩ -- rename v collision below
 have h₀(a:Axis)(l:List Axis):= P.passport_mantle a g h v q u V y l
 refine ⟨fun a l=>⟨P.mantle_threshold a _ _ _ (h₀ a l) (t a l).1,fun x=> Mantle.card P x a _ _ _ (h₀ a l) ((t a l).2.2 x)⟩,?_⟩
 intro I a f B z₀ l p u' F U; let C₁(i:I):=(B₀ (f i)); let t':= fun (i:I) (x:P.Spectrum0 3)=> (t a (f i)).2.2 x
 refine P.passport_coating a l B C₁ (fun _=> V) (fun i=>Eq.mp (congrArg (fun g=> P.Mantle a g (C₁ i) V) (u' i).symm) (h₀ a (f i))) t' z₀ (fun i=> (t a (f i)).2.1.1) p F ?_
 intro σ q₀ tv z; exact P.copass a l p C₁ Q F tv U (fun i _=> (t a (f i)).2.1) (fun i _ b=> (t b (f i)).1) z t' -- shadow t. actual order binder print.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.planet_purchase
#print axioms Spine.passport_mantle
