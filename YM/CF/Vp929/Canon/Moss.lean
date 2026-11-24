import YM.CF.Vp929.Stage.API
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
variable (L:ℕ) {P:BudgetPoint} {n:Side} {B m :ℕ}
private lemma root_ex : ∃ k:ℕ,L ≤ k^3 :=by
 refine ⟨L,?_⟩; rcases Nat.eq_zero_or_pos L with e|e; rw [e]; exact Nat.zero_le _; simpa only [pow_one] using (pow_le_pow_right₀ e (show 1 ≤ 3 by decide))
abbrev mstar:=Nat.find (root_ex L)
lemma root_le : mstar L ≤ L:= by
 apply Nat.find_min'; rcases Nat.eq_zero_or_pos L with e|e; rw [e]; exact Nat.zero_le _; simpa only [pow_one] using (pow_le_pow_right₀ e (show 1 ≤ 3 by decide))
lemma highStar {x:ℕ} : L ≤ x^3 ↔ mstar L ≤ x:=⟨fun e=> Nat.find_min' _ e,fun e=>(Nat.find_spec (root_ex L)).trans (by gcongr)⟩
lemma lowStar (x:ℕ): x^3 < L ↔ x < mstar L:= lt_iff_lt_of_le_iff_le (highStar L)
lemma paves (S: Support (More n)) : Pave P L S ↔ coverNumber P.B S < mstar L:= lowStar L _
lemma starEnd : Tendsto mstar atTop atTop:=by
 apply Filter.tendsto_atTop.mpr; intro i; filter_upwards [eventually_gt_atTop (i^3)] with l k; exact ((lowStar l i).mp k).le
local notation "room"=> Support (More n)
structure Vast (D:ℕ)(n:Side):Prop where
 halo : 10*(mstar L*(4*D+2)+2*D)< (More n).val
 full : mstar L*(D+D+1)^4 ≤ (More n).val ^4
namespace Vast
lemma unwrap (x: Scree.Hub n)(h: Pave P L x.val.2) (t:Vast L P.B n):Nonwrapping x.val.2 x.val.1:=by
 intro i hi; have k:= (Corona.extent _ P.B hi x.property); have hg:= (paves L _).mp h; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (k.trans (by gcongr))) t.halo
lemma base (t:Vast L B n): mstar L≤ coverNumber B (univ:room):=by
 apply Nat.le_of_mul_le_mul_right ?_ (by positivity : 0< (B+B+1)^4)
 exact le_trans t.full (by simpa only [← site_card, card_univ] using Corona.pays (univ:room) B)
end Vast
/-- Grow exactly one at a time: support includes existing anchor throughout. -/
private lemma nextSite (X: room)(t:X≠univ)(p:X.Nonempty):∃ i∈X,∃ j∉ X,separation i j ≤1:=by
 have ht: ∃ y:Site (More n), y∉X:=by by_contra! p; exact t (eq_univ_of_forall p)
 obtain ⟨y,h⟩:=ht
 obtain ⟨x,hx⟩:= p
 let g:= Corona.line x y; have hg: ∃ j:ℕ,g j∉X:=⟨separation x y,by simpa [g, Corona.line_end _ _ le_rfl] using h⟩
 let i:=Nat.find hg; have t: g i ∉ X:= Nat.find_spec hg; cases he:i with
 | zero=> rw [he] at t; exact False.elim (t (by simpa [g] using hx))
 | succ j=> exact ⟨g j,by by_contra w; have hu:i≤j:=Nat.find_min' hg w; omega,g (j+1),he ▸ t,(Corona.line_dist x y j (j+1) (by omega)).trans (by omega)⟩
private lemma grows (X : room)(i:Site (More n))(j:Site (More n))(h:0<B)(t:i∈X)(u:separation i j≤1): coverNumber B (insert j X)≤coverNumber B X+1:=by
 let Y:room:=halo B {i}; have ht:i∈Y:=halo_subset B _ (mem_singleton_self _); have h': j∈Y:=halo_spec.mpr ⟨i,mem_singleton_self _,u.trans h⟩; have he:coverNumber B Y ≤ 1:=by
    have q: Corona.Ships ({i}:room) (B+B+1):=by intro a v b w; rw [mem_singleton.mp v, mem_singleton.mp w]
    exact (Corona.list_cost (X:=Y) B (show covers B Y {i} from ⟨Subset.refl _,Corona.ship_halo _ q⟩)).trans_eq (card_singleton _)
 have hg:= Corona.cover_mono (show insert j X⊆ X∪ Y from insert_subset (mem_union_right _ h') (subset_union_left)) B; exact hg.trans ((Corona.meets_sum t ht B).trans (by omega))
def enlarge (x y: Scree.Hub n) :Prop:= x.val.1=y.val.1∧ x.val.2 ⊆ y.val.2
private lemma harvest (h: 0<B)(e:m ≤ coverNumber B (univ:room))(x:Scree.Hub n)(p: coverNumber B x.val.2 ≤ m) :∃ y:Scree.Hub n,enlarge x y ∧coverNumber B y.val.2=m:=by
 by_cases ht:coverNumber B x.val.2=m; · exact ⟨x,⟨rfl,Subset.refl _⟩,ht⟩
 let U:=x.val.2; have hv: U ≠ univ:= fun t=> by unfold U at t; rw [t] at p ht; exact ht (le_antisymm p e)
 obtain ⟨i,hi,j,hj,v⟩:=nextSite U hv ⟨x.val.1,x.property⟩
 let y: Scree.Hub n:= ⟨(x.val.1,insert j U), mem_insert_of_mem x.property⟩
 have he: coverNumber B y.val.2≤ m:= le_trans (grows U _ _ h hi v) (Nat.succ_le.mpr (lt_of_le_of_ne p ht))
 obtain ⟨z,t,e⟩:= harvest h e y he; exact ⟨z, ⟨t.1,Subset.trans (show U⊆ insert j U from subset_insert ..) t.2⟩,e⟩
termination_by Fintype.card (Site (More n))-x.val.2.card
decreasing_by
 have he:y.val.2.card ≤ Fintype.card (Site (More n)):=card_le_univ _
 have hh:y.val.2.card=x.val.2.card+1:=Finset.card_insert_of_notMem hj; exact (show ∀ a b c:ℕ,c ≤ a → c=b+1 → a-c < a-b from fun a b c h₁ h₂=> by omega) _ _ _ he hh
abbrev shortHub (P:BudgetPoint)(L:ℕ)(x:Scree.Hub n):Prop:= Pave P L x.val.2
structure Extension (L:ℕ)(P:BudgetPoint)(n:Side)(T:Scree.Hub n→Scree.Hub n):Prop where
 fill : ∀ x,enlarge x (T x)
 cap : ∀ x, shortHub P L x → coverNumber P.B (T x).val.2=mstar L
 held : ∀ x, ¬shortHub P L x → T x=x
lemma Vast.expands (t:Vast L P.B n): ∃ T:Scree.Hub n→ Scree.Hub n,Extension L P n T:=by
 classical
 have H(x:Scree.Hub n): ∃ y:Scree.Hub n,enlarge x y∧ (shortHub P L x → coverNumber P.B y.val.2=mstar L)∧(¬shortHub P L x → y=x):=by
    by_cases h: shortHub P L x; · obtain ⟨y,p,v⟩:=harvest P.B_pos (t.base L) x ((paves L _).mp h).le; exact ⟨y,p,fun _=>v, fun v=>(v h).elim⟩
    exact ⟨x,⟨rfl,Subset.refl _⟩,fun v=>(h v).elim,fun _=>rfl⟩
 choose T h v t using H; exact ⟨T,h,v,t⟩
namespace Extension
variable {L}{T:Scree.Hub n→ Scree.Hub n}(p:Extension L P n T)
include p
lemma lands (x): ¬shortHub P L (T x):=by
 by_cases t: shortHub P L x; · exact fun u=>Nat.ne_of_lt ((paves L _).mp u) (p.cap x t)
 rw [p.held x t]; exact t
end Extension
/-- pay side assertion with preset knob N given to Request. -/
def perimeter :ℕ:=10000*(L+1)
lemma vastSize {i:ℕ} (t:perimeter L ≤ i)(u:i*B ≤ (More n).val)(h:0 < B): Vast L B n:=by
 let k:ℕ:=mstar L; have e: k ≤ L:=root_le L; have hv:10000*((k+1)*B) ≤ (More n).val:= Nat.le_trans (show _≤ i*B from calc
    _ = (10000*(k+1))*B:=by ring
    _ ≤ perimeter L*B:= by unfold perimeter; gcongr
    _ ≤ _:=by gcongr) u
 constructor
 · apply Nat.lt_of_lt_of_le _ hv; change 10*(k*(4*B+2)+2*B)<_; calc
    _ ≤ 10*(k*(6*B)+2*B):=by gcongr; omega
    _ < _:=by nlinarith
 change k*_ ≤ _; have hp: k ≤ (k+1)^4:= Nat.le_trans (Nat.le_succ _) ((pow_one _).symm.trans_le (pow_le_pow_right₀ (a:=k+1) (by omega) (show 1≤4 by decide))); calc
    _ ≤ (k+1)^4*(10000*B)^4:=by gcongr; omega
    _ = (10000*((k+1)*B))^4:=by rw [←mul_pow]; ring
    _ ≤ _:=by gcongr
end Test
end YM.CF.Py.Rate
