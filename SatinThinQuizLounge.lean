import SatinFixedContrastNovember4
import SatinThinQuizSignal
/-!
# Milestone 15.III. Continuity and point-to-point price at the strict-order boxes

`commonWell` indeed, even identifying its exact grid price in this experiment's
boxes; compare `Six/Encounters`. This is in addition to the norm estimate for
smears, NOT a claim of norm convergence of point samples without ordering or of
unsmeared t=0 field operators. Price moving centers keeping the WHOLE APERTURE strictly separated between the two families, even for the closure of a pair of
strictly-separated boxes. Can thus ask both our main *smeared* consultation (seam)
and point-center tests. IMPORTANT: This is for the requested (−,+)-side pairings of
OUR TWO kinds of Apron (with the earlier one the Euclidean `kiss`). In particular
not claiming convergence for `=time`, or outside these orderings to OTHER Apron
pairings or more general ongoing correlations.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 290000
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
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "E"=> (Ε).E
local notation "γ"=> P.cartage 3 ξ
local notation "π'"=> P.wealth 3 ξ

-- equality of the ACTUAL height anywhere in two separated boxes, along these shrinking series.
private lemma oneAirport (A B:P.Apron)(t:ℕ)(u:A.s≤t)(v:B.s≤t)(p q:Cover)(J:P.Ellis 3 x)(h:∀ j:Axis,P.meshPose t p j+A.realWidth P j< P.meshPose t q j-B.realWidth P j):
   P.commonWell 3 x (usher (A.kiss P 3) B) (usher (P.meshPose t p) (P.meshPose t q)) [false,true]= P.singleState 3 t x (P.issuing t (A.kiss P 3) p * P.issuing t B q):=by
 let X:= P.meshPose t p; let Y:= P.meshPose t q; let f:=usher (A.kiss P 3) B; let d:= usher p q; let r:=P.vtile t∘d; let L:List Bool:=[false,true]
 have he: P.laysM ∘ r=usher X Y:= funext fun k=>by cases k<;> rfl
 have ht(j:Axis): P.Turnstile j f L (usher X Y):= List.pairwise_pair.mpr (h j)
 have hu:P.Plenum f L (P.laysM∘r):= ⟨fun k=> ⟨L,List.Perm.refl _,he.symm ▸ (ht k)⟩⟩
 have h':P.Turnstile 3 f L (P.laysM∘r):= he.symm ▸ (ht 3)
 have hz:= (P.entirely_now 3 x f L J 3 r h' hu).symm.trans (P.turn_purchase 3 ξ f d t L h' (fun i _=>by cases i <;> first|exact u|exact v))
 exact (P.common_cult 3 x f (usher X Y) L J (List.Perm.refl _) (ht 3)).trans ((congrArg (P.memorial 3 ξ f L) he.symm).trans (hz.trans ((P.single_agrees 3 3 x t _).trans (congrArg (P.singleState 3 t x) (show P.fullScroll t f d L=_ by change _*(_*1)=_; rw [mul_one]; rfl)))))

variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "Λ"=> P.profilesZ x V w
local notation "W"=> P.soldTrumpet A c r n w
variable (T:P.HandleWith x c r A n)
local notation "B[" z "," i "]"=> P.sold_birth x A c r n w z i T
local notation "l₀" => ([false,true]:List Bool)
local notation "I₀" a:max i:max => (W a i).kiss P 3
variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x) (μ:ℝ)(a b:Lead.Clan)
variable (U Y:Doorway)(Z:U.Later Y thinAlongOrder 0)
include R Z
lemma illuminate_shrink_boxes : ∀ᶠ i in atTop,∀ p∈closure U.invites,∀ q∈closure Y.invites,∀ j:Axis,
   p j+(I₀ a i).realWidth P j < q j-(W b i).realWidth P j:=by
 let t(j:Axis):ℝ:= Y.lower j-U.upper j; have ht(j:Axis):0<t j:=by
    apply sub_pos.mpr; simpa only [thinAlongOrder,ite_true,Pi.zero_apply,mul_zero,add_zero] using Z j
 have e : ∀ j:Axis,∀ᶠ i:ℕ in atTop,(W a i).realWidth P j + (W b i).realWidth P j < t j:= fun j=>by
    apply ((R.slender a j).add (R.slender b j)).eventually (gt_mem_nhds (by simpa using ht j))
 filter_upwards [eventually_all.mpr e] with i h p α q τ j
 have ha:p j≤ U.upper j:= (show p ∈ Icc U.lower U.upper from (show p∈ U.sealing from U.doorSeal ▸ α)).2 j
 have hb:Y.lower j≤ q j:= (show q ∈ Icc Y.lower Y.upper from (show q∈ Y.sealing from Y.doorSeal ▸ τ)).1 j
 rw [Apron.kiss_width]; linarith only [ha,hb, (show (W a i).realWidth P j+(W b i).realWidth P j< Y.lower j-U.upper j from h j)]
include J
lemma illuminate_point_grid : ∀ᶠ i in atTop,∀ t:ℕ,c (n i)≤t →∀ p q:Cover,P.meshPose t p∈closure U.invites→ P.meshPose t q∈closure Y.invites→
   P.commonWell 3 x (usher (I₀ a i) (W b i)) (usher (P.meshPose t p) (P.meshPose t q)) l₀= P.singleState 3 t x (P.issuing t (I₀ a i) p* P.issuing t (W b i) q):=by
 filter_upwards [P.illuminate_shrink_boxes x A c r n w V g h T R a b U Y Z] with i e t ht p q f s; refine oneAirport P x _ _ t ht ht p q J ?_; intro j; specialize e _ f _ s j; rw [Apron.kiss_width] at e; exact e
omit J Z
lemma illuminate_paces {s:ℝ}{p:ℕ→ℝ}(u:0<s)(e:Tendsto p atTop (𝓝 s)):
   Tendsto (fun i=> P.cradleG x (W a i) B[a,i] (p i)) atTop (𝓝 (Λ a s)):=by
 let t := s/2; have h₁:0<t:=half_pos u; have ht:t<s:=half_lt_self u
 have hz:Tendsto (fun i=>(p i - t).toNNReal) atTop (𝓝 (s-t).toNNReal):= continuous_real_toNNReal.continuousAt.tendsto.comp (e.sub_const t)
 rw [(R.energy a).2.1 _ _ h₁ ht.le]; refine (((heat_both _ _ (Ε)).tendsto _).comp (hz.prodMk_nhds (R.heated_points a t h₁).2)).congr' ?_
 filter_upwards [e.eventually (lt_mem_nhds ht)] with i u; exact (cradlePositive (Ε) _ t (p i) h₁ (le_of_lt u)).symm
include J
lemma illuminate_curve {p q:ℕ→ Vantage}{f t:Vantage}(u:Tendsto p atTop (𝓝 f))(v:Tendsto q atTop (𝓝 t))(e:f 3<t 3):
   Tendsto (fun i=> P.commonWell 3 x (usher (I₀ a i) (W b i)) (usher (p i) (q i)) l₀) atTop (𝓝 (P.pointPrism x V w (t-f) a b)):=by
 let z:= t-f; let d:ℕ→ Vantage:= fun i=> q i-p i; let w'(i):ℝ:= d i 3; let X:= z 3; let Y:=P.cradleG x
 have hX:0<X:= sub_pos.mpr e; have hu:0<X/2:=half_pos hX
 have hv:Tendsto d atTop (𝓝 z):= v.sub u; have ht:Tendsto w' atTop (𝓝 X):=(continuous_apply _).continuousAt.tendsto.comp hv
 let f (k:Lead.Clan)(i):= Y (W k i) B[k,i] (w' i/2); let Q:= fun y:Vantage × G=> γ y.1 y.2
 have he(k:Lead.Clan):Tendsto (f k) atTop (𝓝 (Λ k (X/2))):= P.illuminate_paces x A c r n w V g h T R k hu (ht.div_const 2)
 refine ((he a).inner (𝕜:=ℂ) (((show Continuous Q from P.caravan 3 _ Prod.fst Prod.snd continuous_fst continuous_snd).tendsto _).comp (hv.prodMk_nhds (he b)))).congr' ?_
 filter_upwards [((R.slender a 3).add (R.slender b 3)).eventually_lt ht (by simpa only [zero_add] using hX)] with i t'
 exact (P.at_half_gap x _ _ B[a,i] B[b,i] (p i) (q i) J (by linarith only [show (W a i).realWidth P 3+(W b i).realWidth P 3<(q i) 3-(p i) 3 from t'])).symm
omit R J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_point_grid
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.illuminate_curve
