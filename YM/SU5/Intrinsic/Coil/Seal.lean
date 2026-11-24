import YM.SU5.Intrinsic.Coil.Incubus
import YM.CF.Rive.Ora

/-! Certificate header: to be raised from Brol & Pine.
 Authored plan uses two budgets for the same lettering: inflated-heavy
 weighted tape to pay every connected admission, and separately the unflagged
 *singleton* terms. Hence no expanding log on unnecessarily expensive ledgers.
 Admission over all Keys at each root. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil.Chart.Stoke
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[DecidableEq I][Fintype I]{n:Side} {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
variable (C:B.Stoke δ P H V a) (T:Blizzard F P H δ b)(L:Finset (I⊕ Force n))(S:Aura n)(D:Support (More n)) (l:List I)(t:0≤ H)(w: 3≤ P.B)
open Push.AbsoluteSums Push.AbsoluteSums.Trees
local notation "Γ"=> Cipher n
local notation "W"=> B.ledger
local notation "𝒜"=> Aura n
local notation "S*"=> I ⊕ Force n
variable (φ:I→ℂ)
def issueK (F:ForceBudget n)(l:List I)(φ:I→ℂ): Cusp n:=fun S D=>∑ L:Finset (I⊕Force n),cutL φ L • C.lot L F S D l
abbrev clearSet (S:Vow.Aura n):Finset (Finset (I⊕ Force n)):= (univ:Finset I).image (fun i=>( {Sum.inl i} :Finset (I⊕Force n))) -- S unnecessary
local notation "U₀"=> clearSet

def firstAt (F:ForceBudget n)(l:List I)(i:I):Copy n:= C.lot {Sum.inl i} F S ∅ l
-- address-specific notion
include T t w
variable (d:l.Nodup)(z:l.toFinset=univ)
include d z
variable {ψ θ:ℝ}(c: ℝ)(f:I⊕ Force n→ℝ)(m:ℝ)(Q:ℝ) -- m rate, Q **scale** ≤ 1.
omit T t w d z
private lemma crank0 {S:Aura n}{δ:ℕ}{P:BudgetPoint} (D:Support (More n))(H:ℝ)(c:ℝ)(t:0≤c):Fray P H δ S D 0 c:=⟨Medal.zeroT.big t,fun _ p=> (p rfl).elim⟩
-- input physical certificates heavy price economy. Hp reserve factor Q on
-- every non-*unflagged* singleton operation; require only for all components
-- **other than** unflagged mark singleton. pay by simple presence criterion.
def Heavy (B:Chart I (Seat n))(f: (I ⊕ Force n)→ℝ)(a: I→ℝ)(b: Force n→ℝ)(Q:ℝ) : Prop:=∀ (L:Finset (I⊕ Force n))(X:Aura n)(D:Support (More n)), Pun B L X D→ L∉ clearSet X →
     Season.leafCost (Sum.elim a b) L ≤ Q * Season.leafCost f L
variable (hp:Heavy B f a b Q)
include T t w d z
lemma regular_bill (U: Finset (I ⊕ Force n))(X:Aura n)(D:Support (More n)) (fY:∀ i,‖φ i‖≤1) : Fray P H δ X D (cutL φ U • C.lot U F X D l) (Season.bookL (W) (Sum.elim a b) 0 U X D):=by
 let N:= Season.bookL B.ledger (Sum.elim a b) 0 U X D; let p:= C.toll T U X D l t w d z
 let V:= Py.Rate.nextHue p.merit (cutL φ U); refine ⟨V.big (mul_le_of_le_one_left (p.merit.wage t) ?_), fun i t=> p.loaf i fun v=>t (by rw [Pi.smul_apply,v,smul_zero])⟩
 unfold cutL; rw [norm_prod]; exact prod_le_one (fun i _=> norm_nonneg _) (fun i _=>fY i)
include hp
lemma abyss_bill (U: Finset (I⊕ Force n))(X:Aura n)(D:Support (More n))(pX:U ∉ clearSet X)(fY:∀ i,‖φ i‖≤1): Fray P H δ X D (cutL φ U • C.lot U F X D l) (Q * Season.bookL W f 0 U X D):=by
 let V:= C.regular_bill T l t w φ d z U X D fY; apply Fray.mk (V.merit.big ?_) V.loaf; unfold Season.bookL; split; rename_i h; exact hp U X D ⟨h.2.2.1,h.2.2.2,h.2.1⟩ pX -- tune
 rw [mul_zero]

omit T t w d z hp
private lemma exempt(h:D.Nonempty)(U:Finset (I⊕Force n))(q:U∈ clearSet S):C.lot U F S D l=0:=by
 obtain ⟨i,_,rfl⟩:=mem_image.mp q; unfold lot; rw [dif_neg]; intro k; have he:∅=D:= by
    simpa [Album.claim,Chart.ledger] using k.1.2.2
 rw [←he] at h; exact Finset.not_nonempty_empty h
private lemma clear_claim (B:Chart I (Seat n)) {L:Finset (I⊕Force n)}(p:L∈clearSet S): B.ledger.claim L=∅:=by
 obtain ⟨a,_,rfl⟩:=mem_image.mp p; simp [Album.claim,Chart.ledger]

include T t w d z hp
lemma flags_bill (X:Aura n)(D:Support (More n))(q:D.Nonempty)(fY:∀ i,‖φ i‖≤1):Fray P H δ X D (issueK (C:=C) F l φ X D) (Q*Season.incubate W f 0 X D):=by
 unfold issueK Season.incubate; rw [mul_sum]; refine Fray.sumP _ _ _ fun i _=>?_ ; by_cases p:i∈ clearSet X; swap; · exact C.abyss_bill T _ t w φ d z _ _ hp i X D p fY
 rw [exempt C X D l q i p, smul_zero, Season.bookL,if_neg,mul_zero]; exact crank0 D _ 0 le_rfl
 intro h; apply @Finset.not_nonempty_empty (Seat n); rw [(show ∅=D from ?_ )]; exact q
 exact (clear_claim X B p).symm.trans h.2.1

lemma no_flags_bill (X:Aura n)(fY:∀ i,‖φ i‖≤1) (g:I→ℝ)(v:∀ i: I,Medal P X.val ∅ (C.firstAt X F l i) H (g i))(hq:0≤Q)(hf:0≤f) : Medal P X.val ∅ (C.issueK F l φ X ∅) H (Q*Season.incubate W f 0 X ∅+∑ i:I, g i):=by
 let T0:Finset (Finset (I⊕ Force n)):=clearSet X; let G(L:Finset (I⊕ Force n)):=cutL φ L • C.lot L F X ∅ l
 rw [issueK, ←Finset.sum_sdiff (s₁:=T0) (subset_univ _)]; let A(T:Finset (Finset (I⊕ Force n))): Copy n:=∑ i∈T,G i
 have he:A T0=∑ i:I,φ i • C.firstAt X F l i:=by
    unfold A T0 clearSet; rw [sum_image]; apply sum_congr rfl; intro i _; unfold G; rw [cutL,show ({Sum.inl i}:Finset (I⊕Force n)).toLeft={i} from (by ext; simp),prod_singleton]; rfl
    intro i _ j _ h; exact Sum.inl.inj (Finset.singleton_injective h)
 change Medal P X.val ∅ (A (univ\T0)+ A T0) H _; rw [he]; apply Medal.plus; swap
 · exact Medal.sumP _ _ _ (fun i _=> (Py.Rate.nextHue (v i) _).big (mul_le_of_le_one_left ((v i).wage t) (fY i)))
 unfold Season.incubate; rw [mul_sum]; apply (Medal.sumP (univ\T0) _ _ (fun i u=> (C.abyss_bill T l t w φ d z f Q hp i _ ∅ (mem_sdiff.mp u).2 fY).merit)).big; refine sum_le_sum_of_subset_of_nonneg (sdiff_subset) ?_; intro i _ h; apply mul_nonneg hq; unfold Season.bookL; split; exact prod_nonneg fun i _=>hf i; exact le_rfl

omit T t w d z hp
#print axioms flags_bill
#print axioms regular_bill
#print axioms exempt
#print axioms no_flags_bill
end YM.CF.Coil.Chart.Stoke
