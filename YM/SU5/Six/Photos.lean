import YM.SU5.Six.Elected
import YM.SU5.Six.MSplit
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
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
open Aria Set
open Cheer (Narrow)

/-!
# Bodies in motion

The projected center used in this experiment is in the continuous
spatial-translation sector of the *same* elected axis-3 Hilbert space.
The cost is the actual commonWell on any ordered turnstile, not the
raw grid kernel (we identify with that at Plenum below, or else with
smearing, retaining the projection).
-/
section
variable (H:Hilbert)(x y z:H)
private lemma eq_of_read (h:∀ w∈([x,y,z]:List H),inner ℂ w z=inner ℂ w x - inner ℂ w y): z=x-y:= by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜:=ℂ)).1
  rw [inner_sub_left,inner_sub_left,inner_sub_right,inner_sub_right,inner_sub_right,inner_sub_right, inner_sub_right, inner_sub_right]
  rw [h x (by simp), h y (by simp), h z (by simp)]
  ring
end
section releases
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)(s t:ℕ)
local notation "τ"=>P.singleState j s x
local notation "τ'" => P.singleState j t x
local notation "Φ"=>P.reflectTest j
lemma sixWard_view_sub {f g:P.Test}(p:P.birthF j s f)(q:P.birthF j s g)(h:P.birthF j s (f-g)) : P.viewF j x s h=P.viewF j x s p - P.viewF j x s q := by
  have he {w:P.Test}(v:P.birthF j s w) : inner ℂ (P.viewF j x s v) (P.viewF j x s h)=inner ℂ (P.viewF j x s v) (P.viewF j x s p)-inner ℂ (P.viewF j x s v) (P.viewF j x s q):= by
    rw [P.released_gram,P.released_gram,P.released_gram,mul_sub,map_sub]
  apply eq_of_read
  -- avoid `simp` deep Hilbert
  intro w u; simp only [List.mem_cons,List.not_mem_nil,or_false] at u
  rcases u with u|u|u <;> subst w <;> exact he _
lemma hereAndThere (p:s≤t) (g:P.Test) : τ' (P.conveying s (t-s) g)=τ g:= by
  let n:= t-s
  have he (n':ℕ) : P.singleState j (s+n') x (P.conveying s n' g)=τ g:= congrArg (P.chi j x) (P.carryReads j s n' g)
  simpa only [Nat.add_sub_of_le p] using he (t-s)
lemma chart_price (f:P.Test)(o:Cover) : τ (P.chartAll o f)=τ f:= by
  have hh (k:Axis)(a:ℤ)(f:P.Test): τ (P.shifts k a f)= τ f:= by
    rw [← P.single_agrees j k x _ (P.shifts k a f),P.slide_single,P.single_agrees]
  suffices ht:∀ L,τ (P.cruise L o f)=τ f from ht Vacancy.ordinate
  intro L; induction L with
  | nil=>rfl
  | cons i L h=>change τ (P.shifts i (o i) (P.cruise L o f))=_; rw [hh,h]
lemma issue_price (F:P.Apron)(o:Cover)(p:F.s ≤t): τ' (P.issuing t F o)=P.singleState j F.s x F.F:=by
  unfold issuing; rw [P.chart_price]; exact P.hereAndThere j x F.s t p F.F
end releases
variable (P:Spine)(x:P.Spectrum0 3)(s t n:ℕ)(Z W:Lead.Clan)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "A"=>P.experimentBody Z s n
local notation "B"=>P.experimentBody W s n
local notation "A'"=> (A).kiss P 3
local notation "H"=>P.ManyF 3 ξ
local notation "H'"=>P.ColorHil 3 ξ
local notation "Ψ" => P.seasons 3 ξ
local notation "Ψ'" => P.physicalEnergy 3 ξ
local notation "℧"=>P.heaven 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "V̂"=>P.viewF 3 ξ s
local notation "Π'"=>P.wealth 3 ξ
local notation "U"=>P.cartage 3 ξ
local notation "E"=>(Ψ).E
local notation "τ"=>P.probeWidth s n
local notation "Θ"=>P.reflectTest 3
local notation "μ"=>P.singleState 3 s x

def increment : ℝ≥0:= whenly (timeMesh P.par) s (P.laterPulse n)
lemma increment_pos (p:0<n):0<P.increment s n:= when_pos _ s (P.laterPulse n) (P.pulse_pos n p)
def filterVector : H' := P.viewF 3 (P.otherSpectrum 3 3 x) s (P.body_birth Z s n)
lemma filter_born : P.filterVector x s n Z=P.shard x Z s n-(Ψ').E (P.increment s n) (P.shard x Z s n):= by
  let F:=P.brightC Z s n
  let a:=P.laterPulse n
  let M:=P.passesLater 3 s a F
  exact (P.sixWard_view_sub 3 ξ s F M (P.body_birth Z s n)).trans (congrArg (fun y:H' => P.shard x Z s n-y) (P.releasedLater 3 ξ s a F))
def sixWard_macroVector : H := Π' (P.filterVector x s n Z)
private lemma clear_heat (X:Hilbert)(Q:X.Op)(v e:X)(p:Q e=e)(z:ℂ): v-Q v=(v-z • e)-Q (v-z • e):=by rw [map_sub,map_smul,p]; abel
lemma filtered_explicit : P.sixWard_macroVector x s n Z=P.birthCloud x Z s n-E (P.increment s n) (P.birthCloud x Z s n):= by
  let a:=P.increment s n; let Q:=(Ψ').E a; let w:=P.shard x Z s n
  exact (congrArg (Π') (P.filter_born x s n Z)).trans ((map_sub (Π') w (Q w)).trans ((congrArg (fun y:H=>Π' w-y) (P.bankHeat 3 ξ _ _)).trans (clear_heat (H) (E a) (Π' w) ℧ (P.heaven_hot 3 ξ a) (P.allowance x Z s n))))
-- for both one point symbols zero at EVERY implementing frame
lemma body_central : μ (A).F=0∧ μ (A').F=0:= by
  have h:μ (A).F=0:= by change μ (P.frontMat Z n-P.shifts 3 _ (P.frontMat Z n))=0; rw [map_sub,P.slide_single,sub_self]
  exact ⟨h, ((P.common_reading s x ((A).F) 3).2.2.1).trans ((congrArg star h).trans (star_zero _))⟩
lemma issued_central (o:Cover)(p:s≤t) : P.singleState 3 t x (P.issuing t A o)=0∧P.singleState 3 t x (P.issuing t A' o)=0:= by
  have h:= P.body_central x s n Z
  exact ⟨(P.issue_price 3 x _ _ o p).trans h.1, (P.issue_price 3 x _ _ o p).trans h.2⟩
-- Entry displacement
local notation "T"=> timeMesh P.par
lemma width_here (j:Axis) : 0<τ j:= ((P.experimentBody (0,true) s n).real_width_pos P j)
lemma rawEntry : (A).engine P 3 ξ ω = (Ψ').E ((τ 3).toNNReal) (P.filterVector x s n Z):=by
  let v:=(A).cardB P 3; let a:=(A).u 3; let f:=(A).F
  let p:=P.body_birth Z s n
  have he:whenly T s a=(τ 3).toNNReal:= by change whenly T s a=(bell T s a).toNNReal; rw [natural_time]; exact Real.toNNReal_coe.symm -- cast
  refine (P.engine_view 3 ξ A).trans ((P.identical_F 3 ξ s _ (P.passesLater 3 s a p) ((A).card_price P 3)).trans ?_)
  exact (P.releasedLater 3 ξ s a p).trans (congrArg (fun t:ℝ≥0=> (Ψ').E t (P.filterVector x s n Z)) he)
lemma centerEntry : flashY x A 3 = E ((τ 3).toNNReal) (P.sixWard_macroVector x s n Z):= (congrArg Π' (P.rawEntry x s n Z)).trans (P.bankHeat ..)

section heat
private lemma inside_price (X:Hilbert) (S:OS.Semigroup X (3:Axis))(v:X.Op) (w g b:ℝ≥0)(u y:X)(h:∀ (a:ℝ≥0)(x:X), S.E a (v x)=v (S.E a x))(ht:w+(g+w)=b): inner ℂ (S.E w u) (S.E g (v (S.E w y)))=inner ℂ u (v (S.E b y)):= by
  have hu(a₁ a₂:ℝ≥0)(u:X): S.E a₁ (S.E a₂ u)=S.E (a₁+a₂) u:= by rw [S.time]; rfl
  rw [S.swing,h,h,hu,hu,add_assoc,ht]
end heat
abbrev gridStory (P:Spine)(s n:ℕ)(Z W:Lead.Clan): Bool→P.Apron := usher ((P.experimentBody Z s n).kiss P 3) (P.experimentBody W s n)
variable (q p:Vantage)
open Casting
local notation "η"=> ([false,true]:List Bool)
local notation "D"=> P.gridStory s n Z W
def transmission : ℂ:= P.commonWell 3 x (P.gridStory s n Z W) (usher (0:Vantage) p) η
lemma turnTransmission (u:P.probeWidth s n 3*2<p 3): P.Turnstile 3 D η (usher (0:Vantage) p):= List.pairwise_pair.mpr (show (0:ℝ)+τ 3<p 3-τ 3 by linarith only [u]) -- maybe reorder
variable (J:P.Ellis 3 x)
include J
lemma positive_time_charge (u:2*P.probeWidth s n 3<p 3):
    P.transmission x s n Z W p= inner ℂ (P.sixWard_macroVector x s n Z) (U p (E (p 3).toNNReal (P.sixWard_macroVector x s n W))):=by
  let a:=τ 3
  have he: a+a < p 3:= by linarith only [u]
  have h:=avail_cross x (A') B 3 p J he
  let w:=a.toNNReal; let g:=(p 3-(a+a)).toNNReal
  have hu:w+(g+w)=(p 3).toNNReal:= by
    have hp:=P.width_here s n 3; have ht:0<a:=hp
    ext
    simp only [w,g,NNReal.coe_add, Real.coe_toNNReal, ht.le,sub_nonneg.mpr he.le,(show 0≤p 3 by linarith only [he,ht])]
    ring
  exact h.trans ((congrArg₂ (inner ℂ) ((flashY_glare x A 3).trans (P.centerEntry x s n Z)) (congrArg (fun y:H=> E g (U p y)) (P.centerEntry x s n W))).trans (inside_price (H) (Ψ) ((U) p) w g _ (P.sixWard_macroVector x s n Z) (P.sixWard_macroVector x s n W) (P.warm_drive 3 ξ p) hu))
lemma transmission_shifted (h:2*τ 3 < (p-q) 3):
    P.commonWell 3 x D (usher q p) η=P.transmission x s n Z W (p-q):=by
  let a:=usher (0:Vantage) (p-q)
  have ht: usher q p=settler a q:= by funext i; cases i; exact (add_zero _).symm; exact (show p=q+(p-q) by abel)
  rw [ht]; exact (P.common_shift 3 x D a η J ⟨3,η,List.Perm.refl _, P.turnTransmission s n Z W _ (by linarith only [h])⟩ q).2
omit J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
