import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Six.Encounters
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six Set
open Spectral Caino Spectral.Orbit.Prairie
open FrameBound
open Matrix
section
variable (H:Hilbert)
private lemma any_combination (F:Lead.Clan→ H.space) (z:Lead.Clan→ℂ) (d:ℝ) :
 star z ⬝ᵥ ((Matrix.gram ℂ F-(d:ℂ) • (1:CrossRead)) *ᵥ z) = ((‖FrameBound.combination Lead.Clan H F z‖^2-d*(∑ i,‖z i‖^2):ℝ):ℂ):=by
 rw [sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,star_dotProduct_gram_mulVec,dotProduct_smul, inner_self_eq_norm_sq_to_K, smul_eq_mul]
 have he: star z ⬝ᵥ z=((∑ i,‖z i‖^2:ℝ):ℂ):=by
   unfold dotProduct; push_cast
   exact Finset.sum_congr rfl fun i _=> Complex.conj_mul' (z i)
 rw [he]
 push_cast; rfl
private lemma measured_floor (F:Lead.Clan→ H.space) (d:ℝ) (v: (d:ℂ) • (1:CrossRead) ≤ Matrix.gram ℂ F):Coercive Lead.Clan H F d:= by
 rw [Matrix.le_iff,posSemidef_iff_dotProduct_mulVec] at v
 intro a; have he:=v.2 a
 rw [any_combination] at he
 apply sub_nonneg.mp; exact_mod_cast he
-- Slack statement in the ordered experiment. Compact unit sphere argument for
-- the regulator lower bound with arbitrarily small slack.
private abbrev ClanBall:= EuclideanSpace ℂ Lead.Clan
private lemma confidence (F:ℕ→Lead.Clan→H.space)(f:Lead.Clan→H.space)(d b:ℝ)(v:Coercive Lead.Clan H f d)
    (p:b < d) (t:∀ i,Tendsto (fun n=> F n i) atTop (𝓝 (f i))) : ∀ᶠ n in atTop, Coercive Lead.Clan H (F n) b:=by
 by_contra! u
 have hx(m:ℕ):∃ n≥m,∃ a: EuclideanSpace ℂ Lead.Clan, ‖a‖=1∧‖FrameBound.combination Lead.Clan H (F n) a.ofLp‖^2<b:=by
    obtain ⟨n,r,u⟩:= (u.and_eventually (eventually_ge_atTop m)).exists
    refine ⟨n,u,?_⟩; by_contra! x
    exact r (FrameBound.extend_bound Lead.Clan H _ x)
 choose y r g q c using hx
 obtain ⟨a,e,l,s,h⟩:= (isCompact_sphere (0:ClanBall) 1).tendsto_subseq (x:=g) (fun n=>by simpa using q n)
 have hl:Tendsto (y ∘ l) atTop atTop := (tendsto_atTop_mono r tendsto_id).comp s.tendsto_atTop
 have ht:Tendsto (fun n=>FrameBound.combination Lead.Clan H (F (y (l n))) (g (l n)).ofLp) atTop (𝓝 (FrameBound.combination Lead.Clan H f a.ofLp)):=by
    exact tendsto_finsetSum _ fun i _=> ((((PiLp.continuous_apply 2 _ i).tendsto a).comp h).smul ((t i).comp hl))
 have he:= le_of_tendsto (ht.norm.pow 2) (Eventually.of_forall (fun i=> (c (l i)).le))
 have hv : ∑ i:Lead.Clan,‖a.ofLp i‖^2=1:= by
    have hw: ‖a‖=1:= by simpa using e
    calc _ = ‖a‖^2:= (sq_coefficients Lead.Clan a).symm
         _ = 1:=by rw [hw]; norm_num
 have x:= v a.ofLp; rw [hv,mul_one] at x
 exact p.not_ge (x.trans he)
private lemma includes_floor (G:Hilbert) (l:H.space→ₗᵢ[ℂ]G.space) (f:Lead.Clan → H.space)(d:ℝ)(v:(d:ℂ) • (1:CrossRead)≤gram ℂ f): Coercive Lead.Clan G (fun x=> l (f x)) d:=
 let t : gram ℂ (l ∘ f) = gram ℂ f:= Matrix.ext (fun i j=> l.inner_map_map ..)
 measured_floor G (l ∘ f) d (v.trans_eq t.symm)
end
section pricing
variable {P:Spine} {x:P.Spectrum0 3} {s n:ℕ} {A:Set E4} {F:SampleDose} (L:P.ReflectMeter x s n F A)
local notation "H"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "T"=> P.arrayReading x s n 0 (flipDose F 3) F
local notation "A'"=> P.arrayFine x s n
include L
set_option maxHeartbeats 2000000 in
lemma ReflectMeter.recorder(t:ℕ)(p:s≤t):
     P.arrayFine x s n t (flipDose F 3) F=Matrix.gram ℂ (fun Z=> P.postVector x s t n Z F 0):= by
 ext1 i j; let l:=P.prepared t (P.FTest i s n) F; let m:=P.prepared t (P.FTest j s n) F
 obtain ⟨w,h⟩:=L.verify t p i; obtain ⟨v,u⟩:=L.verify t p j
 exact (P.reflector_consult x s n F t i j).trans ((P.single_agrees 3 3 x t _).symm.trans ((P.released_gram 3 (P.otherSpectrum 3 3 x) t w v).symm.trans (congrArg₂ (inner ℂ) h u)))
lemma ReflectMeter.diminished(d:ℝ) (v: (d:ℂ) • (1:CrossRead) ≤ P.arrayReading x s n 0 (flipDose F 3) F) (b:ℝ)(h:b<d) : ∀ᶠ t:ℕ in atTop, (b:ℂ) • (1:CrossRead) ≤ P.arrayFine x s n t (flipDose F 3) F:=by
 let u:= P.otherSpectrum 3 3 x; let F'(t i):=P.postVector x s t n i F 0; let f(i):=P.launchCost x s n i F 0
 have hp:=confidence H F' ((P.enter 3 u) ∘ f) d b (includes_floor _ _ (P.enter 3 u) f d (v.trans_eq (P.reflector_matches x s n F))) h L.inbound
 filter_upwards [eventually_ge_atTop s,hp] with i p t'
 exact (loewnerCharge H _ (F' i) t').trans_eq (L.recorder i p).symm
omit L
end pricing

-- Optional if rectangles specified for the *spacetime experiments* too,
-- not just their center supports. Take any prescribed such rectangles and
-- require even the FULL footprint price of the test contained within them.
-- A corollary of AllOpens once the finite resolution is chosen sufficiently
-- fine for even a smaller such pair. (For preselected densities in the
-- bigger pair only, just use the original AllOpens.)
namespace Doorway
variable (Y:Doorway)
noncomputable def spare: Doorway where
 lower i:= (2*Y.lower i+Y.upper i)/3
 upper i:= (Y.lower i+2*Y.upper i)/3
 clearance i:= by linarith only [Y.clearance i]
lemma sparesL(i:Axis) : Y.lower i < Y.spare.lower i:= by
 unfold spare; dsimp
 linarith only [Y.clearance i]
lemma sparesU(i:Axis) : Y.spare.upper i < Y.upper i:= by
 unfold spare; dsimp
 linarith only [Y.clearance i]
lemma sparesDoor : closure Y.spare.invites ⊆ Y.invites:=by
 intro a p i _; rw [doorSeal] at p
 exact ⟨(Y.sparesL i).trans_le (p.1 i), lt_of_le_of_lt (p.2 i) (Y.sparesU i)⟩
lemma spareLater {Z: Doorway}{σ:Orders}{w:Vantage}(p:Y.Later Z σ w) : Y.spare.Later Z.spare σ w:= by
 intro i; have h:=p i; split at h
 · rename_i t; rw [if_pos t]; linarith only [h,Y.sparesU i,Z.sparesL i]
 rename_i t; rw [if_neg t]; linarith only [h,Y.sparesL i,Z.sparesU i]
lemma spareCosts (w:ℕ→Vantage)(f:∀ j,Tendsto (fun i=>w i j) atTop (𝓝 0)):
    ∀ᶠ i:ℕ in atTop,∀ j:Axis,Y.lower j+(w i j)<Y.spare.lower j∧Y.spare.upper j+(w i j)<Y.upper j:=by
 apply eventually_all.mpr; intro j
 have e:= ((f j).const_add (Y.lower j)).eventually (gt_mem_nhds (show Y.lower j+0<Y.spare.lower j by simpa using Y.sparesL j))
 exact e.and (((f j).const_add (Y.spare.upper j)).eventually (gt_mem_nhds (show Y.spare.upper j+0<Y.upper j by simpa using Y.sparesU j)))
end Doorway
variable {P:Spine}{x:P.Spectrum0 3}{s n:ℕ}{σ:Orders}{X Y: Doorway}{A:Set E4}
lemma bounded_within (M:P.Apron)(U:SampleDose)(p:tsupport U.val ⊆ X.spare.invites)(h:∀ j:Axis,X.lower j+M.realWidth P j<X.spare.lower j∧X.spare.upper j+M.realWidth P j<X.upper j): P.spacePrice M U ⊆ X.invites:=by
 intro a e j _; obtain ⟨b,t,v⟩:=Set.mem_iUnion₂.mp e
 have he:=p t; obtain ⟨y,u⟩:=abs_le.mp (v j); obtain ⟨x,w⟩:=h j
 have hx: X.spare.lower j < b j:= (he j (Set.mem_univ j)).1; have hy: b j< X.spare.upper j:= (he j (Set.mem_univ j)).2
 exact ⟨by linarith only [hx,y,x],by linarith only [hy,u,w]⟩

#print axioms ReflectMeter.diminished
lemma in_price {x p: Vantage}{M:P.Apron} : p∈ P.Aperture M x ↔ p-x∈P.Aperture M 0:= by
  unfold Aperture
  simp
lemma price_isCompact(M:P.Apron): IsCompact (P.Aperture M 0):=by
 let w:Vantage:= M.realWidth P
 have h : P.Aperture M 0 = Set.Icc (-w) w:= by
    ext x
    change (∀ i:Axis, _)↔ (-w≤ x∧x≤w)
    constructor
    · intro p
      constructor
      · intro i; have he:|x i-0|≤w i:=p i; rw [sub_zero] at he; exact (abs_le.mp he).1
      intro i; have he: |x i-0|≤w i:=p i; rw [sub_zero] at he; exact (abs_le.mp he).2
    intro p i; change |x i-0|≤w i; rw [sub_zero]; exact abs_le.mpr ⟨p.1 i,p.2 i⟩
 rw [h]; exact isCompact_Icc
lemma cost_isCompact (M:P.Apron)(U:SampleDose): IsCompact (P.spacePrice M U):=by
 let S:=tsupport U.val
 let X:= S ×ˢ P.Aperture M 0
 have ht:P.spacePrice M U=(fun p:Vantage×Vantage=>p.1+p.2) '' X:= by
   ext x; constructor
   · intro p; obtain ⟨y,e,f⟩:= Set.mem_iUnion₂.mp p; exact ⟨(y,x-y),⟨e,in_price.mp f⟩,(by dsimp; abel)⟩
   rintro ⟨⟨a,b⟩,h,g⟩
   have hg:x-a=b:=by rw [←g]; dsimp; abel
   exact Set.mem_iUnion₂.mpr ⟨a,h.1,in_price.mpr (hg ▸ h.2)⟩
 rw [ht]; exact ((U.budget.prod (price_isCompact M)).image (continuous_fst.add continuous_snd))
-- full PAID spatial supports in ALL projection orders, for the tests in (ii). Can be completely off the origin wall in c; only the pair has ordering.
lemma supports_ordered (p:P.AllOpens x s n X Y σ) (F G:SampleDose)(h:tsupport F.val ⊆ closure X.invites)(u:tsupport G.val ⊆ closure Y.invites) (i j:Lead.Clan): ∀ y∈ P.spacePrice (P.RTest i s n) F,∀ z∈ P.spacePrice (P.FTest j s n) G,z-y∈OrderChamber σ (0:Vantage):= by
 let M:= P.RTest i s n; let L:= P.FTest j s n
 intro y g z v q
 obtain ⟨a,e,v⟩:= Set.mem_iUnion₂.mp v
 obtain ⟨b,i,g⟩:= Set.mem_iUnion₂.mp g
 let w:=P.probeWidth s n
 have hp:a-b∈ OrderChamber σ w:= p.allW (show (b,a)∈ _ from ⟨h i,u e⟩)
 obtain ⟨v,f⟩ := abs_le.mp (show |z q-a q|≤ w q from v q); obtain ⟨k,g⟩:= abs_le.mp (show |y q-b q|≤ w q from g q)
 specialize hp q
 unfold OrderSlab at hp ⊢
 split at hp
 · rename_i t; rw [if_pos t]; change 2*(w q)<a q-b q at hp; change 2*0 < z q-y q; linarith only [hp,v,g]
 rename_i t; rw [if_neg t]; change a q-b q< -(2*w q) at hp; change z q - y q < -(2*0); linarith only [hp,f,k]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
