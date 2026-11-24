import Organdy.Brume
import Organdy.Vent
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]


abbrev highLaunch (p:BudgetPoint):ℝ:=p.supportExponent+8*biscuit p
lemma launchPos : 0≤highLaunch p:=
 add_nonneg p.exponent_pos.le (mul_nonneg (by norm_num) biscuit_pos.le)
local notation "l·"=>highLaunch p
variable {σ:I→Seat n}{V:I→Bag n}
variable {A B:I→ Aura n→ℝ}

/-- Billing *per source* after all knocks including the crag. -/
structure Tine (p:BudgetPoint)(q:ℕ)(h:ℝ)(σ:I→Seat n)
    (V:I→Bag n)(A B:I→ Aura n→ℝ)(a b:ℝ):Prop extends Pollen p q h σ V A B where
   weigh : 0≤a ∧ 0≤b
   deep: ∀ i:I,∀ X:Aura n,σ i∉X.val → A i X=0 ∧ B i X=0
   priceA:∀ i:I, voyageB (A i) p.B (highLaunch p) ≤a
   priceB:∀ i:I, voyageB (B i) p.B (highLaunch p) ≤b

lemma ear (i : Tine p q h σ V A B a b) {X:Aura n} (j:I):0≤A j X:=(i.ticket j X).tube.price
lemma earring (i : Tine p q h σ V A B a b) {X:Aura n} (j:I):0≤B j X:=
 voucher (i.ticket j X)

lemma dense (i:Tine p q h σ V A B a b)
    {m:ℕ}(w:breeze σ m):
    (∀ x,tallB (∑ j:I, A j) p.B (highPace p) x ≤ polySight p.B m * a)∧
    (∀ x,tallB (∑ j:I, B j) p.B (highPace p) x ≤ polySight p.B m * b):=
  ⟨dredge A (fun j _=>ear i j) i.priceA i.weigh.1 σ (fun j X y=>(i.deep _ _ y).1) w,
   dredge B (fun j _=>earring i j) i.priceB i.weigh.2 σ (fun j X y=>(i.deep _ _ y).2) w⟩

lemma downsent {Y:I→Support (More n)}
    (r:∀ i,σ i∈Y i)
    (t:∀ i:I, Barrage p q (Y i) h (V i) l· a b)
    (va:0≤a)(vb:0≤b): ∃ A B,Tine p q h σ V A B a b:=by
   choose f g fare far take give using (fun i=>(t i).price)
   exact ⟨f,g,⟨fare,fun i X o=>(far i X (fun z=>o (z (r i)))).1⟩,
    ⟨va,vb⟩,fun i X o=>(far i X (fun z=>o (z (r i)))).2,take,give⟩

/-- Deck accounting, can also be used afterwards with other
kinds of launches. -/
abbrev capstan (p:BudgetPoint) (M:ℕ)(f:ℝ):ℝ:= polySight p.B M*f
abbrev Stalls (p:BudgetPoint)(M:ℕ)(a b γ:ℝ):Prop :=
 Stops p (capstan p M a) (capstan p M b) γ
variable {M:ℕ}{γ:ℝ}{F:ForceBudget n}

lemma safetyK (v:10≤p.B):
    straightPace p ≤ p.supportExponent+1 ∧
    (p.supportExponent=1→l· ≤ 2):=by
  have t : (10:ℝ) ≤ p.B:=by exact_mod_cast v
  have s:biscuit p ≤ 1/10:= le_div_iff₀ (by norm_num:(0:ℝ)<10)|>.mpr (by
     rw [biscuit,inv_mul_le_iff₀ (by linarith)]; linarith)
  exact ⟨by unfold straightPace;linarith,fun h=>by unfold highLaunch; rw [h];linarith⟩

lemma whittle (A:Aura n→ℝ)(r:0≤A)(g:a≤b)(x:Seat n):
    tallB A p.B a x ≤ tallB A p.B b x:=
  sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (tact_para g i) (r i)

lemma rerack (s:Stalls p M a b γ)
    (v:10≤p.B)(w:0≤h) (l:Ledger p h q d F)(t:d < γ)
    (i:Tine p q h σ V A B a b)(e:breeze σ M):
    ∃ r, OrbitRack s.sleigh σ q F h i.toPollen.soar
      (∑ j:I,A j) (∑ j:I,B j) r (trawling V):=by
  obtain ⟨α,β⟩:=dense i e
  have hp:0≤∑ j:I, A j:=sum_nonneg fun j _ X=>ear i j
  have hz:0≤∑ j:I, B j:=sum_nonneg fun j _ X=>earring i j
  have ht: straightPace p ≤ highPace p:=by unfold straightPace highPace; linarith [biscuit_pos (p:=p)]
  obtain ⟨r,fr,u⟩:=l
  have hv:∀ X,∀ D⊆X.val,0≤r X D:=fun X D g=>(fr X D g).merit.wage w
  have hd : 0 ≤ roofL r 1:=fun X=> sum_nonneg fun i t=>mul_nonneg
    (zero_le_one.trans (duty_i _ le_rfl)) (hv _ _ (mem_powerset.mp t))
  exact ⟨r,i.toPollen.rafter F (Nat.le_trans (by norm_num) v) w fr
    (s.filled hp α hz
    (fun x=> (whittle _ hz ht x).trans (β x)) hv
    (fun x=> ((whittle _ hd (safetyK v).1 x).trans (u x)).trans_lt t))⟩

/-- wide X allows zero shape. -/
def Pavilion (L:ℕ)(p:BudgetPoint)(V:Bag n):Prop:=
 ∀ X:Aura n, L > (coverNumber p.B X.val)^3 → V X=0

abbrev outfit (L:ℕ)(c:ℝ):ℝ:=lashCrag 2 L * |c|
lemma outfit_zero {L:ℕ}(c:ℝ) : 0≤outfit L c:=mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
lemma outfitter {L:ℕ} (s:ℝ)(e:s≤2) (c:ℝ) :
    lashCrag s L *c ≤ outfit L c:=
  (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos ..).le).trans
   (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right e (Nat.cast_nonneg _))) (abs_nonneg _))
open Leaf

variable {L:ℕ}

lemma backed (v:2*(massif L*p.B) ≤ (More n).val)
    (o: Seat n)(f:Bag n): Pavilion L p (expand L p o f):=by
  intro X t
  rw [expand,Finset.sum_apply]
  refine sum_eq_zero fun i _=>if_neg fun g=>?_
  rw [g] at t
  have ht:(rockG L p o).val ⊆ (αK (rockG L p o) i).val:=subset_union_left
  exact t.not_ge ((coverRock v o).trans (Nat.pow_le_pow_left (Corona.cover_mono ht _) _))

abbrev incline (σ:I→Seat n)(L:ℕ)(p:BudgetPoint)(V:I→ Bag n) :=
  fun i=>expand L p (σ i) (V i)

lemma blossom (L:ℕ) {Y:I→Support (More n)}
    (v:l·≤ 2)
    (r:∀ i,σ i∈Y i)
    (t:∀ i:I, Barrage p q (Y i) h (V i) l· a b):
    ∃ A B,Tine p q h σ (incline σ L p V) A B (outfit L a) (outfit L b):=
  downsent (Y:= fun i=>(rockG L p (σ i)).val)
    (fun i=>centreRock L p _) (fun i=>
      (mast launchPos (t i) (r i)).bigR (outfitter _ v _) (outfitter _ v _))
    (outfit_zero a) (outfit_zero b)

end YM.CF.Organdy
