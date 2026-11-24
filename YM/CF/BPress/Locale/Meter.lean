import YM.CF.BPress.Locale.Price
import YM.CF.BPress.Locale.Minty
/-!
Explicit uses. uniform case with chosen covers for family permitting all geometric preconditions. Implement positive weight contingency; map contingent nucleus of ALL reads even if complex argument. Turf map with no condition. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix Push.AbsoluteSums Ledger
open scoped Topology BigOperators Classical Matrix
variable {s:Side}{b:BandWidth}(X:Bands s b) (R:Hangar s){T:Sheet.Atlas}{C C' Lf y:ℝ}{B r:ℕ}(F:Net s T Lf y C C' B) (o:ℕ)
def Lcharge (o B:ℕ)(Lf y:ℝ):= estate o*pacer B Lf y
abbrev Rcharge (o:ℕ) := estate o*baser
def Long (P:Support s)(U:Seal (SiteX X R)) : Prop:=∃ X':Seal (SiteX X R), Floor X R F P X' ∧ U=broad (shape X R) X' o
structure MicroMap {I: Type*}(L:I→Support s)(u:I→Seal (SiteX X R))(p:I→ℝ):Prop where
 en : ∀ i,p i≠0→ Long X R F o (L i) (u i)
 max : FareP X R L p u (fun v=> positions X R v r) (R.L.val^3 * (b.D+2*r+1)) (Rcharge o) (Lcharge o B Lf y)
lemma microReceipt {I: Type*}(L:I→Support s)(p:I→ℝ)(q:∀ i,p i≠0→ Grove (Grid.field 4 s) (L i) ∧ meets X r (L i))(t:Rights R b Lf y r): ∃ u: I→ Seal (SiteX X R), MicroMap X R F o L u p (r:=r) :=by
 choose! U Z W using fun i:I=> (show ∀ k:p i≠0,∃ Z, Floor X R F (L i) Z∧ _ from fun k=> floor_pays X R F (L i) (q i k).1 t (q i k).2); let u(i:I):= broad (shape X R) (U i) o; refine ⟨u,fun i k=>⟨U i,Z i k,rfl⟩,fun i k=>?_,fun i k=>?_,fun i=>pinned_cost X R i (le_trans t.near.le ?_),fun i k=>(b_print X R _ (Z i k|>.base_g) o).1⟩ -- tune
 · refine (Nat.mul_le_mul_left _ (b_print X R _ (Z i k|>.base_g) o).2).trans ?_; rw [mul_left_comm]; exact (Nat.mul_le_mul_left _ (W i k)).trans (Eq.le (by unfold Rcharge Lcharge; ring))
 · obtain ⟨x,k',q⟩:= (q i k).2; refine ⟨plan X R x, (b_blank (shape X R) (U i) o) ((Z i k).shape_at x k'),_, k', mem_filter.mpr ⟨mem_univ _,rfl,q⟩⟩
 unfold umbra cloak; omega
-- Turf (any columns in single gap) statement separate
variable {I:Type*}
structure TurfMap (L:I→Seal X.Hcols)(u:I→Seal (SiteX X R))(p:I→ℝ): Prop where
 pack i : u i=broad (shape X R) ((L i).image (own X R)) o
 height : FareP X R L p u (podium X R) (R.L.val^3) (estate o * estate 2) (estate o*estate 2)
lemma turfReceipt (L:I→Seal X.Hcols)(p:I→ℝ)(q:∀ i,p i≠0→ Turf X (L i)): ∃ u:I→Seal (SiteX X R), TurfMap X R o L u p:=by
 let u(i):=broad (shape X R) ((L i).image (own X R)) o; refine ⟨u,fun i=>rfl,fun i k=>?_ ,fun i k=>?_,fun i=> (podium_cost X R i).le,fun i k=> (b_print X R _ (turf_print X R (L i) (q i k)|>.1) o).1⟩
 · obtain ⟨v,w⟩:= turf_print X R _ (q i k); refine le_trans (Nat.mul_le_mul_left _ (b_print X R _ v o).2) ?_; rw [mul_left_comm]; exact (Nat.mul_le_mul_left _ w).trans (Eq.le (by ring))
 obtain ⟨x,h⟩:= Grid.inhabited_grove (q i k).1; exact ⟨_, (b_blank (shape X R) ((L i).image (own X R)) o (mem_image_of_mem (own X R) h)),_,h,(mem_filter.mpr ⟨mem_univ _,rfl⟩)⟩
end YM.CF.BPress.Locale
