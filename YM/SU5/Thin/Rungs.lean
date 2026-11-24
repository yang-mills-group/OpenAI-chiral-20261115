import SatinFixedContrastNovember4
import YM.SU5.Thin.NoInflation

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
/-- pinned for the WHOLE static-R campaign at native s. Include geometry to
pass still through the old election gates in calling for those *same* widths. -/
structure StaticPrice (P:Spine)(x:P.Spectrum0 3)(i n s:ℕ) : Prop where
  clearing : inchR P.par s n≤ Twah.keyV i
  labelSupports (L:Twah.Parts i n) : printedHere P.par P.width s L.sites (cabin (Twah.keyV i))
  ready (j:Axis)(U:Twah.Parts i n) : ‖P.singleState j s (P.otherSpectrum 3 j x) (P.tuneK U.song)-U.depiction‖ ≤ Twah.keyV i
variable (P:Spine)(x:P.Spectrum0 3)
private lemma growthCondition (p:ℕ→ℕ→Prop)(g:∀ i:ℕ,∃ᶠ x:ℕ in atTop,p i x) : ∃ f:ℕ→ℕ, StrictMono f ∧ ∀ i,p i (f i) := by
  choose t e b using fun i a:ℕ=> (show ∃ n : ℕ, n>a∧p i n from ((g i).and_eventually (eventually_gt_atTop a)).exists.imp (fun _ h=>h.symm)) -- And.symm not ext?
  let z:ℕ→ℕ:= Nat.rec (t 0 0) (fun i y=>t (i+1) y); exact ⟨z,strictMono_nat_of_lt_succ (fun i=>e (i+1) (z i)),fun i=>by cases i; exact b 0 0; exact b _ _⟩
private lemma aboveSequence (z:ℕ→ℕ) : ∃ c:ℕ→ℕ,StrictMono c ∧ z≤c := growthCondition (fun i k=>z i ≤ k) fun i=>(eventually_ge_atTop _).frequently
/-- credential allowing n, not just smears, to be held fixed in dollars when
sending s→∞ through another deployment on this enrollment. -/
structure Repeater (P:Spine)(K:P.Register)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(r:ℕ→ℕ) :Prop where
  unitSize : ∀ i,0<r i
  eager : StrictMono r
  ground : P.party 3 K x
  realPos : P.LowerDeck x K J
  top : Summit x
  infinity : ∀ i:ℕ, ∃ᶠ s in atTop, P.StaticPrice x i (r i) s
section election
variable {P}{K:P.Register} {U:Supplier}{e v:ℝ}(u:uniform P K U e v)
open Twah
include u
/-- Keep static receipts (at ANY one of these n widths, and on the SAME theory)
even after choosing r,c etc. Cost: old UV tests on THEIR accuracy level; here
at arbitrarily late native heights. Buy all together (countably many).
-/
private lemma repeatAfter (i n:ℕ) (g:∀ x:Parts i n, Clarity (Papal.meanF x.craft x.depiction) 4 (Twah.keyV i/2)) :
    ∀ᵐ x ∂P.pillars 3, ∃ᶠ s in atTop, P.StaticPrice x i n s := by
  let D:= Twah.keyV i /2; let E (d:Parts i n):= d.depiction
  have he:0<Twah.keyV i:=Twah.keyV_positive i
  obtain ⟨p,t⟩:= exhibitionChance u (fun (_:ℕ) (s:Parts i n)=>s.craft) _ (fun _ (s:Parts i n)=> E s) -- args
    (fun _ (i:Parts i n)=>i.song) (ε:=fun _=>D) (fun _ (s:Parts i n)=>g s) (δ:=fun _=>D) (fun _=>half_pos he)
  obtain ⟨f,w,v⟩:=aboveSequence p
  filter_upwards [(t f v).2] with x h
  apply w.tendsto_atTop.frequently ?_
  apply Filter.Eventually.frequently
  filter_upwards [h,w.tendsto_atTop.eventually (Prototype.rent_unit n _ he), w.tendsto_atTop.eventually (Filter.eventually_all.mpr
    (fun (L:Parts i n)=>building P.par P.width L.sites (Twah.keyV i) he))] with j u y w
  exact ⟨y,w,fun k F=>(u k F).trans_eq (add_halves _)⟩
lemma repeats (z:ℕ→ℕ) : ∃ (x:P.Spectrum0 3)(J:P.Ellis 3 x)(r:ℕ→ℕ),z ≤ r ∧ P.Repeater K x J r:= by
  choose f u' using fun i=> (show ∃ r:ℕ,∀ s:ℕ, s ≥ r → _ from eventually_atTop.mp (aroused i (keyV i/2) (half_pos (keyV_positive i))))
  obtain ⟨r,p,h⟩:= aboveSequence fun i=>max (f i) (z i+1)
  let C (x:P.Spectrum0 3):Prop:=∀ i:ℕ,∃ᶠ s in atTop,P.StaticPrice x i (r i) s
  have hu:∀ᵐ x∂P.pillars 3,C x:= ae_all_iff.mpr (fun i=> repeatAfter u i (r i) (u' i _ ((le_max_left ..).trans (h i)))) -- Countable use MeasureTheory.ae_all_iff
  obtain ⟨α,t,t',_,_,R,_hq,g⟩:= violet_simultaneous u (e₀:=1) zero_lt_one
  obtain ⟨i,x,u',b,_⟩:= (g.mono fun i p=> p C hu).exists
  obtain ⟨J⟩:=P.ellisP 3 x K
  have hx(i:ℕ): z i+1≤ r i:= (le_max_right ..).trans (h i)
  exact ⟨x,J,r,fun i=>(hx i).trans' (Nat.le_add_right ..), ⟨fun i=> lt_of_lt_of_le (by omega : 0< z i+1) (hx i)
    ,p,b,final_issues K J b, footway x J K b,u'⟩⟩
end election
namespace Repeater
variable {P}{x}{K:P.Register}{J:P.Ellis 3 x}{r:ℕ→ℕ}(W:P.Repeater K x J r)
local notation "Y" i:max s:max=> P.StaticPrice x i (r i) s
include W
lemma windUp (i:ℕ) : ∃ b:ℕ→ℕ, StrictMono b ∧∀ j, P.StaticPrice x i (r i) (b j):= growthCondition (fun _ s=>P.StaticPrice x i (r i) s) fun _=>W.infinity i
lemma diagonalQualifies {c:ℕ→ℕ}(p:StrictMono c)(u:∀ i:ℕ,Y i (c i)) : P.Experiment K c r x J:=
  ⟨⟨W.eager,p,W.unitSize,fun i=>(u i).clearing,fun i=>(u i).labelSupports⟩,Eventually.of_forall fun i=>(u i).ready,W.ground,W.realPos,W.top⟩
lemma also_old : ∃ c:ℕ→ℕ,P.Experiment K c r x J ∧∀ i,Y i (c i):= by
  obtain ⟨c,p,z⟩:=growthCondition _ W.infinity
  exact ⟨c,W.diagonalQualifies p z,z⟩
/-- Verify stability over ARBITRARY tall static stencil repeats at same tori
assumptions. This can avoid any rate improvements on cost exponents. E.g. on the
true width removal at one of these n lengths, still on this very phase, we earn
the needed upper bound on nonvacuum signal after the external gap and the lower
bound on the interaction. Don't infer limiting nonvacuum value or nonzero rank six.
-/
lemma sweeping (S:ℕ→ℕ→Prop)(g:∀ c:ℕ→ℕ,P.Experiment K c r x J → ∀ᶠ i:ℕ in atTop,S i (c i)) :
    ∀ᶠ i:ℕ in atTop,∀ᶠ s:ℕ in atTop,P.StaticPrice x i (r i) s→ S i s := by
  by_contra h
  have p:∃ᶠ i:ℕ in atTop,∃ᶠ s:ℕ in atTop,Y i s∧¬ S i s:= by
    push Not at h; exact h
  let F (i s:ℕ):= (Y i s)∧ ((∃ᶠ v:ℕ in atTop,Y i v∧¬ S i v) →¬ S i s)
  have he(i:ℕ) :∃ᶠ s:ℕ in atTop,F i s:= by
    unfold F; by_cases u: (∃ᶠ s:ℕ in atTop,Y i s∧¬ S i s)
    · exact u.mono fun _ g=>⟨g.1,fun _=>g.2⟩
    exact (W.infinity i).mono fun _ w=>⟨w,fun p=>False.elim (u p)⟩
  obtain ⟨c,v,z⟩:=growthCondition F he
  obtain ⟨i,u',w⟩:= (p.and_eventually (g c (W.diagonalQualifies v (fun i=>(z i).1)))).exists
  exact (z i).2 u' w
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "κ"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
/-- Key upper bound at this election & neighborhood, ANY after padding (on
static prices). A plume-to-positive-critical-time test. Coupon does NOT require
centered subtraction. -/
lemma horizonStays (a:ℝ≥0) (q:0<a)(ε:ℝ)(e:0<ε) :
    ∀ᶠ i:ℕ in atTop,∀ᶠ s:ℕ in atTop,P.StaticPrice x i (r i) s → ∀ Z:Lead.Clan,
      ∀ b:ℝ≥0, a ≤ b → dist ((P.physicalEnergy 3 ξ).E b (P.shard x Z s (r i))) ((purePrice Z:ℂ) • κ)<ε*purePrice Z := by
  apply W.sweeping; intro c h; exact Filter.eventually_all.mpr fun Z=> thin_uniform_heat Z h a q (ε*purePrice Z) (mul_pos e (purePrice_p Z))
end Repeater
#print axioms repeats
#print axioms Repeater.horizonStays
#print axioms Repeater.also_old
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
