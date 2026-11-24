import YM.CF.BPress.Mosaic.Tag
import YM.CF.BPress.Locale.Purchase
/-! pricing by support-map. Scope.Nonempty automatic where needed. One shared map constant. Allocation uses 40-radius root ball (enough for reading assignment indicator with short terms). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mosaic
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Peel.Spine Ledger Push.AbsoluteSums
variable {R:Hangar (More N)} {H:Crew A}{I:Type}[Fintype I]
-- note Real radius selected; halo40 both. Need mapping credit from Spine & widths
abbrev Fac(H:Crew A)(X:Sugar.Stage N):ℕ:= overhead H X 40
def MicCost(R:Hangar (More N))(X:Sugar.Stage N)(W:BandWidth) (b:ℝ):= expense 4 b (R.L.val^3*(W.D+2*X.W.M+1)) (constant 40)
variable {X:Sugar.Stage N}{T:SlotT A R}{L:I→Support (More N)}{f:Visit A R H→ℂ}{u:I→Visit A R H→ℂ}{w:I→ℝ}{a q:ℝ}
structure RightsC (X:Sugar.Stage N)(R:Hangar (More N))(H:Crew A)(a:ℝ) :Prop where
 era : Rights R B H.L H.y X.W.M
 boss : courant R.L.val (Fac H X) 4 a
 c:0<a
structure FeeT (X:Sugar.Stage N)(S:Support (More N))(F:Visit A R H→ℂ)(v:SlotT A R):Prop where
 stamp: Grove (shape A R) v
 corner: ∀ i∈S,plan A R i∈v
 capacity: R.L.val*v.card≤ constant 40* R.L.val + Fac H X*S.card
 knows:∀ x y:Visit A R H, Peek H v x.val y.val→ F x=F y
namespace FeeT
variable (u0:RightsC X R H a) (p:Host R H)
abbrev readP(x:H.castP) := x.val
variable {S:Support (More N)}
private lemma owns(v:Spine H X S T)(b:Site (More N))(s:b∈S): plan A R b∈T:=v.pay b (halo_subset _ _ s) (stem_home ..)
include u0 p
lemma general (g:Grove (Grid.field 4 (More N)) S)(k:Locale.meets A X.W.M S) (u:∀ t:SlotT A R, Spine H X S t → ∀ x y, Peek H t (Subtype.val (p:=Peel.points A R H) x) (Subtype.val (p:=Peel.points A R H) y) → f x=f y): ∃ t, FeeT X S f t:=by
 obtain ⟨t,H,v,k⟩:=expenseBody u0.era p k g 40 (by omega); exact ⟨_,H,owns v,k,u _ v⟩
lemma smallBody {r:ℕ}(t:ShortP X H R r)(h:S.card≤ r)(g:Grove (Grid.field 4 (More N)) S)(k:Locale.meets A X.W.M S)(b:Site (More N))(s:b∈S)(u:∀ (x y: Visit A R H), Peek H (Peel.stem (plan A R b) 40) x.val y.val → f x=f y) : FeeT X S f (Peel.stem (plan A R b) 40):=by -- tune subtype
 let i:=plan A R b; 
 refine ⟨tree_stem i 40, owns (shortBody k g h t p b s (by norm_num : 7≤40)), ?_,u⟩; refine le_trans ?_ (Nat.le_add_right ..); rw [mul_comm]; apply Nat.mul_le_mul_right; refine le_trans ((card_le_card (stem_bay i 40)).trans (Locale.capacity A R i 40)) ?_; change estate 40≤ estate 40*_ ; exact Nat.le_mul_of_pos_right _ (by norm_num [baser,estate]) -- tune binder `w.rt.roots`
end FeeT
section assistantR
variable (u0:RightsC X R H a)
include u0
lemma mirror (t: Cash L w a q)(p: ∀ i,w i≠0→ Locale.meets A X.W.M (L i)∧∃ s, FeeT X (L i) (u i) s) (h:∀ i x, ‖u i x‖≤ w i)(m:∀ i,Measurable (u i)): Lift (MicCost R X B a *q) (fun x=>∑ i,u i x):=by
 choose! S H' using fun i=> fun k:w i≠0=>(p i k).2; have hp : FareP A R L w S (fun i=>positions A R i X.W.M) (R.L.val^3*(B.D+2*X.W.M+1)) (constant 40) (Fac H X):=by
    refine ⟨fun i h=> (H' i h).capacity,fun i h=> ?_ ,fun i=> pinned_cost A R i (lowP u0.era.near.le),fun i h=> (H' i h).stamp⟩; obtain ⟨x,v,t⟩:=(p i h).1; exact ⟨_,(H' i h).corner _ v, _,v,mem_filter.mpr ⟨mem_univ _,rfl,t⟩⟩
 refine (show Act0 S w (MicCost R X B a * q) u from ⟨ (?_), hp.purse t (by norm_num) t.zero u0.c u0.boss.1 u0.boss.2,h,fun i v=>(H' i v).stamp,m⟩).wallet; intro i x y k; by_cases b:w i=0; exact (norm_le_zero_iff.mp ((h i x).trans b.le)).trans (norm_le_zero_iff.mp ((h i y).trans b.le)).symm; exact (H' i b).knows x y k -- tune
end assistantR
end YM.CF.BPress.Mosaic
