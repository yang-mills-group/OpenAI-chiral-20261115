import YM.SU5.Celeste.Brooch
import YM.SU5.Celeste.Stanzas
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
/- anchor at POSITIVE clearance ℓ near actual plane=0 -/
namespace Morn
abbrev separationR (B:Side)(u:ℕ):=4*B.val*u
abbrev birth(B:Side)(u:ℕ): Cover:= 1 + separationR B u • step 3
abbrev death(B:Side)(u:ℕ):= birth B u+ separationR B u • step 3 (S:=ℤ)
abbrev chimney(B:Side)(u:ℕ): Walk:= List.replicate (2*separationR B u) (posDir 3)
variable (B)
def rayL (u:ℕ): Lead (separationR B u):=⟨birth B u,death B u,0,false,chimney B u,by rw [Ballad.sail]; unfold death direction; simp,by rw [chimney,Sods.swifts]; unfold death nodeC; rw [smul_add,mul_smul (2:ℕ)]; unfold birth; abel,List.length_replicate⟩
lemma height_w (k:ℕ): separationR B k / (2*B.val) = 2*k:=by unfold separationR; rw [show 4*B.val*k=(2*k)*(2*B.val) from (by ring),Nat.mul_div_left]; exact Nat.mul_pos two_pos B.property -- tune
lemma aligned_ (k:ℕ): ((rayL B k).mirror 3 0).birth=(rayL B k).birth+direction (Ballad.sail true (Ballad.gap B (separationR B k))):=by
 change (plane 3 0).flee (death B k)=_ + _; funext i; by_cases h:i=3<;> simp only [Ballad.sail,ite_true] <;> simp [rayL,death,birth,direction, flee_pos,h, Ne.symm]; unfold Ballad.gap; rw [height_w]; unfold separationR; push_cast; ring

def verse(k:ℕ): Melody B (separationR B k) := ⟨rayL B k, (rayL B k).mirror 3 0, rfl, by simp [Lead.mirror,axis_val],true,aligned_ B k⟩
def epic(k:ℕ)(x:Lead.Clan): Weaver:= (rayL B k).groundWord x
abbrev cutzero (F: Weaver)(c:ℝ): Weaver:= F- (c:ℂ) • (1:Weaver)
abbrev GoalA (i:Axis)(z:ℤ)(V:Weaver): Weaver:= V*fluent i z V
def leastOne(k:ℕ)(x:Lead.Clan): Weaver:= cutzero (epic B k x) (purePrice x)
def leastTwo(k:ℕ)(x:Lead.Clan): Weaver:= cutzero (GoalA 3 0 (epic B k x)) (brill x)
lemma melWord (k:ℕ)(x:Lead.Clan): (verse B k).groundLead x false= leastOne B k x ∧ (verse B k).groundLead x true= leastTwo B k x:=by
 refine ⟨rfl,?_⟩; change cutzero ((epic B k x)*((rayL B k).mirror 3 0).groundWord x) (brill x)= _; rw [show (((rayL B k).mirror 3 0).groundWord x: Weaver) = fluent 3 0 (epic B k x) from funext fun N=> ((rayL B k).bk_chant_mirror ..).symm]; rfl -- f args

open Signal.Interval
local notation "oS" i:max=> (rayL B i).patio
def Suit (ℓ:ℕ)(i:ℕ):Prop:= Tower.region 3 0 ℓ (rayL B i).patio
lemma grows (ℓ:ℕ) : ∀ᶠ i:ℕ in atTop,Suit B ℓ i :=by
 filter_upwards [eventually_ge_atTop ℓ] with i hv x p; obtain ⟨t,h,rfl⟩:= Cube.range_leg (nodeC (birth B i)) (posDir 3) (2*separationR B i) x (List.mem_toFinset.mp p); have hi: i ≤ separationR B i:= Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) B.property); have he:(i:ℤ) ≤ 4*(B.val:ℤ)*i:=by exact_mod_cast hi;
 simp [birth,nodeC]; omega
lemma ray_grows : Tendsto (separationR B) atTop atTop:=tendsto_atTop_mono (fun i:ℕ=> show i≤ separationR B i from Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) B.property)) tendsto_id
lemma Qualify (ℓ:ℕ)(j:ℕ)(h:1≤j)(e:ℝ)(p:0<e):∀ᶠ k in atTop,0<k∧Suit B ℓ k ∧ ∀ (x:Lead.Clan), Clarity (leastOne B k x) j e ∧ Clarity (leastTwo B k x) j e:=by filter_upwards [grows B ℓ,(ray_grows B).eventually (Melody.eraFlag B h p), eventually_gt_atTop 0] with i u e n; exact ⟨n,u,fun x=> ⟨(melWord B i x).1 ▸ e (verse B i) x false,(melWord B i x).2 ▸ e (verse B i) x true⟩⟩ -- e shadows
lemma Holds (k)(x:Lead.Clan): Voice (epic B k x) (oS k) := flourish ..
lemma placates_one (k)(x:Lead.Clan): Voice (leastOne B k x) (oS k):= (Holds B k x).sub ((Voice.one _).hushed _)
lemma placates_two(k)(x:Lead.Clan): Voice (leastTwo B k x) ((oS k)∪ Tower.reflectedBox 3 0 (oS k)):= ((Holds B k x).mul ((Holds B k x).turn 3 0)).sub ((Voice.one _).hushed _)
lemma stab_hold (q k:ℕ): Heat.gaugeShift B k ≥ k:=by
 let t:ℤ:=↑B.val; change _ ≤ (4*t)*k; have ht:1 ≤ t:=(by have h:1 ≤ B.val:= B.property; unfold t; omega); refine le_mul_of_one_le_left ?_ (by linarith); positivity
variable {T:Finset Cover}
open Buffered.Afterglow.Tower.SlabMark (moves)
open Afterglow.Tower ( reflected_coord support_translation)
abbrev onFlight (B:Side)(S:Finset Cover)(a:Axis)(k:ℕ):= Tower.address a (Heat.gaugeShift B k) S
abbrev takeoff(B:Side)(F:Weaver)(a:Axis)(k:ℕ):= traction a (Heat.gaugeShift B k) F
variable (V W: Finset Cover)(a:Axis)
lemma flown_away (d:ℕ):∀ᶠ k in atTop,∀ x∈ V,∀ y∈ onFlight B W a k,d ≤ separationCost x y:= by
 let Q(k:ℕ):Cover→ Cover:=fun x=> x+(2*Heat.gaugeShift B k) • step a; let D(x:Cover)(y:Cover)(i:Axis):= ((x-y) i).natAbs; have he(x y:Cover):∀ᶠ k in atTop,d≤ D x (Q k y) a:=by
    filter_upwards [eventually_ge_atTop ((x a).natAbs+(y a).natAbs+d)] with k s; have ht:= stab_hold B 0 k; unfold D Q; rw [Pi.sub_apply,moves a a,if_pos rfl]; omega
 have hp:= (Finset.eventually_all V).mpr fun x _=> (Finset.eventually_all W).mpr fun y _=> he x y; filter_upwards [hp] with k h x p z v; obtain ⟨y,l,rfl⟩:= mem_image.mp v; exact (h _ p _ l).trans (le_sup (f:=D x (Q k y)) (mem_univ a))
lemma prepareLaunch (d:ℕ):∀ᶠ k in atTop, Tower.region a 0 d (onFlight B W a k):= by
 have he(x:Cover):∀ᶠ k:ℕ in atTop, (d:ℤ)≤x a+2*Heat.gaugeShift B k:=by filter_upwards [eventually_ge_atTop (d+(x a).natAbs)] with k t; have he:= stab_hold B 0 k; omega
 filter_upwards [(Finset.eventually_all W).mpr fun x _=> he x] with k h x t; obtain ⟨x,g,rfl⟩:=mem_image.mp t; rw [moves a a,if_pos rfl,zero_add]; exact h _ g
variable {B V W}
lemma tower_epoch (B:Side)(S:Finset Cover)(a:Axis)(d:ℕ):∀ᶠ k in atTop,∀ x∈ Tower.reflectedBox a 0 (onFlight B S a k),∀ y∈onFlight B S a k,d ≤ separationCost x y:=by
 filter_upwards [prepareLaunch B S a d] with k h x p y e; obtain ⟨x,q,rfl⟩:=mem_image.mp p; apply (le_sup (f:=fun i=> (((plane a 0).motion x-y) i).natAbs) (mem_univ a)).trans'; simp only [Pi.sub_apply,Tower.reflected_coord,mul_zero]; have ht:= h x q; have hx:=h y e; omega
lemma queue_bound (B:Side)(S:Finset Cover)(k:ℕ): (Tower.reflectedBox a 0 (onFlight B S a k)).card ≤ S.card:=le_trans card_image_le card_image_le
end Morn
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.Morn.tower_epoch
#print axioms YM.CF.Lamour.Bridge.Celeste.Morn.Qualify
