import YM.SU5.Celeste.Kith
import YM.SU5.FiniteGaugeData.Tower.Sight
import YM.SU5.Twilight.Rhapsody
/-! # Flat comparisons BEFORE pruning. tools. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Py Py.Rate Py.Rate.LocalLimit
open Py.Rate.LocalLimit.Papal (Weaver household)
open Signal.Interval (separationCost)
open Buffered.Afterglow
open Buffered.Lifted Ballad Window
open Pannier.Chancel Push.SectorMeasure
variable {N:Side}{S:Finset Cover}{ζ:ℝ}
open Bilinear
variable {R k ℓ d j:ℕ} {B:Side}{s:ℝ}
open Morn
/-!
# Wearable marks. step arithmetic ready to compare at transverse notches,
  while BUYING *before* resolution. Cost purchase after seeing buffer. -/
open Reflect Mir
open Tower MeshClock
namespace Glimpse
-- no coupes
section wearables
def poke (A:Lead R)(i:Axis)(u:ℤ): Lead R := (A.mirror i 0).mirror i u
lemma poke_word (A:Lead R)(i:Axis)(u:ℤ)(x:Lead.Clan): (poke A i u).groundWord x= traction i u (A.groundWord x):=by funext N; change _=reflMark i u (reflMark i 0 (A.groundWord x N)); rw [A.bk_chant_mirror,Lead.bk_chant_mirror]; rfl
lemma poke_slot (A:Lead R)(i:Axis)(u:ℤ): (poke A i u).slot=A.slot:=by simp only [poke,Lead.mirror,Lead.shuffle]; split_ifs <;> simp
lemma poke_wave (A:Lead R)(i:Axis)(u:ℤ): (poke A i u).wave=A.wave:=by simp only [poke,Lead.mirror,axis_val]; split_ifs <;> simp
lemma poke_birth (A:Lead R)(i:Axis)(u:ℤ): (poke A i u).birth=A.birth+ u • step i:=by
 ext p; change (plane i u).flee ((plane i 0).flee A.birth) p= _; rw [flee_pos, flee_pos,SlabMark.moves]; by_cases h:i=p; · simp [h]; ring
 simp [h,Ne.symm h]
-- LENGTH shift words. lists will cross later on this mesh. feet gauge shifts = 2× `pace` in units of gauge. Prepare before many. lane direction intentionally arbitrary ν>= gaugequant. Choose fixed WORD `(rayL)` from cp8 exactly.
end wearables
section tempo
variable (B : Side) (i:Axis)
abbrev pace (t:ℤ):= Heat.gaugeShift B (2*t) -- 8*B*t
variable {α:Axis}
variable (L:List (Trans α))(p:Trans α→ℤ)
abbrev stepCost {B:Side}(i:Trans α)(t:ℤ):Cover:= pace B t • Lattice.step i.val
def promenade (A:Lead R) : Lead R := L.foldr (fun i a=> poke a i.val (pace B (p i))) A
def crownBook (F: Weaver) : Weaver := L.foldr (fun i a=> traction i.val (pace B (p i)) a) F
def trace (V: Finset Cover) : Finset Cover:= L.foldr (fun i a=> address i.val (pace B (p i)) a) V
def total : Cover := (L.map (fun i=> stepCost (B:=B) i (p i))).sum
local notation "J" i:max=> (pace B (p i))
variable (A:Lead R)
lemma crown_step (F:Weaver)(i: Trans α): crownBook B (i::L) p F= traction i.val (pace B (p i)) (crownBook B L p F):= rfl
lemma trace_step (F:Finset Cover)(i: Trans α): trace B (i::L) p F= address i.val (pace B (p i)) (trace B L p F):= rfl
lemma total_step(i:Trans α):total B (i::L) p=stepCost (B:=B) i (p i)+total B L p:= List.sum_cons
lemma assured (x: Lead.Clan): crownBook B L p (A.groundWord x)= (promenade B L p A).groundWord x:=by
 induction L with | nil=> rfl| cons i L ih=>rw [crown_step,ih,← poke_word]; rfl
lemma perslot : (promenade B L p A).slot=A.slot:=by induction L with|nil=>rfl|cons i L ih=>exact (poke_slot (promenade B L p A) i.val (J i)).trans ih
lemma perwave : (promenade B L p A).wave=A.wave:=by induction L with|nil=>rfl|cons i L ih=>exact (poke_wave (promenade B L p A) i.val (J i)).trans ih
lemma perbirth : (promenade B L p A).birth=A.birth+total B L p:=by induction L with
 | nil=>simp [promenade,total]
 | cons i L ih=> rw [show promenade B (i::L) p A=poke (promenade B L p A) i.val (J i) from rfl,poke_birth,ih,total_step,add_right_comm,add_assoc] 
lemma Reading {F:Weaver}{V:Finset Cover}(t: Voice F V): Voice (crownBook B L p F) (Glimpse.trace B L p V):=by induction L with|nil=>exact t|cons i L ih=>exact ih.tract i.val (J i)
lemma shines {F:Weaver}{e:ℝ}(h:1 ≤ j)(t:Clarity F j e):Clarity (crownBook B L p F) j e:=by induction L with|nil=>exact t|cons i L ih=>exact ih.tract h i.val (J i)
end tempo
-- Actual interactions price law. far offset along ANY transverse motion `ρ`, with all other marks already maybe moved. ep.
section marks -- parse shadows
variable (B:Side)(p:ℤ)
abbrev all0(z:ℤ) : Trans 3→ℤ:=fun _=> z
def blazer := crownBook B (look 3) (all0 p)
abbrev balcony := Glimpse.trace B (look 3) (all0 p)
local notation "Θ"=> fluent 3 0
local notation "ζ"=> blazer B p
local notation "m₀"=> look 3
local notation "V"=> (all0 p)
local notation "ν"=> total B m₀ V
def halfBill (k:ℕ)(x:Lead.Clan): Weaver:= (ζ (epic B k x))*(Θ (epic B k x))-(brill x:ℂ) • (1:Weaver)
-- far bill relative to contrast; prepare AFTER choosing R
local notation "G"=> leastOne B
variable (k:ℕ)(q:Lead.Clan)
abbrev Lord := rayL B k
local notation "W"=> Lord B k
local notation "R₁"=> promenade B m₀ V
noncomputable def tilted : Promenade B (separationR B k) (-total B m₀ V) where
 first:=R₁ W
 last:=(verse B k).last
 slot_s:= ((verse B k).slot_s).trans (perslot B m₀ V W).symm
 wave_s:= ((verse B k).wave_s).trans (perwave B m₀ V W).symm
 face:=true
 aligned:=by rw [perbirth,(verse B k).aligned]; change (W).birth+direction (Ballad.sail true _)=_; abel -- parse
lemma currency: (tilted B p k).groundLead q true=halfBill B p k q:=by
 have he:Θ (epic B k q)=(verse B k).last.groundWord q:= funext fun N=> Lead.bk_chant_mirror ..
 have hp:(tilted B p k).first.groundWord q=ζ (epic B k q):=(assured B _ _ W q).symm
 unfold halfBill; rw [he,←hp]; rfl
lemma enough_loans (h:1≤j){e:ℝ}(v:0< e):∀ᶠ k:ℕ in atTop,∀ q:Lead.Clan, Clarity (halfBill B p k q) j e:=by
 filter_upwards [(ray_grows B).eventually (Promenade.eraFlag B (J:=-total B m₀ V) h v)] with i u q; exact currency B p i q ▸ u (tilted B p i) q true

-- even ticks
abbrev foyer(B:Side)(i:Trans 3)(z:ℕ)(F: Weaver):= traction i.val (pace B z) F
-- include displacements for EVERY BASIS k separately so witness nontrivial momentum projection
-- on contributions w≠κ for all k inside selected phase (same vacuum and mark). Each receives its own budget evaluation.
def lastBill (a:Trans 3)(i:ℕ)(q:Lead.Clan):Weaver:= fluent 3 0 (leastOne B k q)*foyer B a i (blazer B p (leastOne B k q))
variable (i:Trans 3)
local notation "B₀"=> halfBill B p k
local notation "C₀"=> balcony B p
local notation "D₀"=> lastBill B p k i
local notation "E₀"=> (rayL B k).patio
lemma finaleX(q:Lead.Clan){e:ℝ}(u:0 < e)(d:e ≤ 1/2)(h:1≤ j)(t:Clarity (leastOne B k q) j e): ∀ᶠ r:ℕ in atTop,Clarity (lastBill B p k i r q) j e:=by
 let A:=leastOne B k q; let X:= blazer B p A; have v:= Clarity.far («V»:=(Tower.reflectedBox 3 0 E₀)) («W»:=C₀ E₀) (F:=fluent 3 0 A) («G»:=X) ((placates_one B k q).turn 3 0) (Reading B m₀ V (placates_one B k q)) (t.turn h 3 0) (shines B m₀ V h t) B i.val u d h
 filter_upwards [show ∀ᶠ n:ℕ in atTop, Clarity (Θ A * takeoff B X i.val (2*n)) j e from (tendsto_atTop_mono (fun i:ℕ=> show i ≤ 2*i from (by omega)) tendsto_id).eventually v] with n hn -- v is for 2*n via .eventually? redo
 suffices hw:(foyer B i n X)= takeoff B X i.val (2*n) by unfold lastBill; change Clarity (Θ A * foyer B i n X) j e; rw [hw]; exact hn
 unfold foyer pace takeoff; rw [Nat.cast_mul,Nat.cast_ofNat] -- tune
abbrev porchA (k:ℕ):= balcony B p (rayL B k).patio ∪ Tower.reflectedBox 3 0 (rayL B k).patio
abbrev porchB(n:ℕ):= Tower.reflectedBox 3 0 E₀ ∪ Tower.address i.val (pace B n) (balcony B p E₀)
lemma pay_A: Voice (B₀ q) (porchA B p k) := ((Reading B m₀ V (Holds B k q)).mul ((Holds B k q).turn 3 0)).sub ((Voice.one _).hushed (brill q))
lemma pay_B (n:ℕ)(q:Lead.Clan) : Voice (D₀ n q) (porchB B p k i n):= ((placates_one B k q).turn 3 0).mul ((Reading B m₀ V (placates_one B k q)).tract i.val (pace B n))
end marks
section tune
variable (B)(ℓ j:ℕ)(t:ℝ)(p:ℤ)
abbrev Company:= (Unit ⊕ Trans 3) × Lead.Clan
def program (k n:ℕ): Company → Weaver:= fun (x,b)=> Sum.elim (fun _=>halfBill B p k b) (fun i=> lastBill B p k i n b) x
structure Voyage extends Gaze B j ℓ t where
 marine: Ladle j B ℓ t Company
 port:ℕ
 portpos:0<port
 concert : marine.label = program B p toGaze.hair port -- unused p binder issue `#check`
#check Voyage
-- hitting dictionary
instance t3 : Nonempty (Trans 3):=⟨⟨0,by decide⟩⟩
lemma arranged (h:1≤j)(g:0<t)(u:t ≤ 1/2): Nonempty (Voyage B ℓ j t p):=by
 obtain ⟨k,⟨k0,t0,tk⟩,v⟩:= ((Qualify B ℓ j h t g).and (enough_loans B p h g)).exists
 let S:=(rayL B k).patio; let U:=Tower.reflectedBox 3 0 S; let r:=S∪U
 obtain ⟨y',fy⟩ := (Filter.eventually_all.mpr fun i:Lead.Clan=> Clarity.far (F:=fluent 3 0 (leastOne B k i)) (G:= leastOne B k i) (V:=U) (W:=S) ((placates_one B k i).turn 3 0) (placates_one B k i) (Clarity.turn h (tk i).1 3 0) (tk i).1 B 3 g u h).exists
 let Y:Gaze B j ℓ t:= {hair:=k,fare:=y',bright:=k0,crown:=t0,label:=hoy B k y',oven:=rfl,area:=fun (x,c)=> match x with
             | .inl true=> S
             | .inl false=>r
             | .inr _=>U∪onFlight B S 3 y'
                        ,price:=by rintro ⟨i,b⟩; have hp:=placates_one B k b; rcases i with (a|_); cases a; apply placates_two; exact hp; exact (hp.turn 3 0).mul (hp.tract 3 _)
                        , clarity:=by rintro ⟨i,b⟩; rcases i with (a|_); cases a; exact (tk b).2; exact (tk b).1; exact fy b }
 obtain ⟨n,hv,hn⟩:= ((Filter.eventually_all.mpr fun i:Lead.Clan=> Filter.eventually_all.mpr fun x: Trans 3=> finaleX B p k x i g u h (tk i).1).and (eventually_gt_atTop 0)).exists
 refine ⟨{ toGaze:= Y,port:=n, portpos:= hn, marine:= { label:=program B p k n, area:=fun (x,c)=> Sum.elim (fun _=>porchA B p k) (fun i=> porchB B p k i n) x, price:= ?_, clarity:= ?_ },concert:= rfl}⟩
 · rintro ⟨(a|i),q⟩; exact pay_A B p k q; exact pay_B B p k i _ q
 rintro ⟨(a|i),q⟩; exact v q; exact hv q i
abbrev menuX (P:Voyage B ℓ j t p): Ladle j B ℓ t (Trinity ⊕ Company):=P.toGaze.toLadle.tack P.marine
end tune
end Glimpse
end YM.CF.Lamour.Bridge.Celeste
