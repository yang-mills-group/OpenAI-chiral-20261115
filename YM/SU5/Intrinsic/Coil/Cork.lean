import YM.SU5.Intrinsic.Coil.Seal
import YM.CF.Song.Pads

/-! Economies.
 * Place the **unflag scale** without using a small total number of actors,
   and even for Letters with large market price such as (129).
 * First-pins incl Frame alignment to be requested separately. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
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
variable (φ:I→ℂ)
variable (d:l.Nodup)(z:l.toFinset=univ)
variable {ψ θ γ μ s:ℝ}{c: ℝ}(f:I⊕ Force n→ℝ)(m:ℝ)(Q:ℝ)
variable (hp:Heavy B f a b Q)
include T t w d z hp
variable (q:Ready B.ledger.seats P.B f m ψ θ γ) (g: I→ Aura n → ℝ) (hv:∀ i S,Medal P S.val ∅ (C.firstAt S F l i) H (g i S))
include q
variable (h:0 ≤ Q)(h0:0 ≤ m)
include h h0
local notation "W"=> B.ledger
local notation "𝒜"=> Aura n
abbrev pack (B:Chart I (Seat n))(Q:ℝ)(f: I⊕ Force n→ℝ) := fun (X:Aura n)(D:Support (More n))=> Q * Season.incubate B.ledger f 0 X D
local notation "τ"=> pack B Q f
local notation "∆"=>Q*(ψ*(1-γ)⁻¹)
omit T t w d z hp h0 in
lemma pack_nn : 0 ≤ pack B Q f:=by
 intro i a; apply mul_nonneg h; refine sum_nonneg fun l _=>?_ ; unfold Season.bookL; split; exact prod_nonneg fun i _=> q.2.2.2.2.1 i; exact le_rfl
include q
omit T t w d z hp in
lemma degree_sums (o:Seat n) : tallB (Vow.hymn τ) P.B m o ≤ ∆ ∧ tallB (fun i:Aura n=> τ i ∅) P.B m o ≤ ∆:=by
 let A:= pack B Q f; have ht: (∑ i:𝒜 with o∈i.val,(∑ D:Support (More n), A i D)*currency P.B m i.val) ≤ Q*(ψ*γ^0*(1-γ)⁻¹):=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (Season.budget_tape W m P.B f q 0 h0 o) h); unfold A pack; simp_rw [←mul_sum,mul_assoc,←mul_sum]; exact le_rfl
 let v(X:𝒜):= ∑ D:Support (More n), A X D; let f'(t:𝒜→ℝ)(a:∀ X:𝒜,t X ≤ v X):tallB t P.B m o ≤ _ := (sum_le_sum (fun X _=> mul_le_mul_of_nonneg_right (a X) (Real.exp_pos _).le)).trans ht
 have hx:0≤A:= pack_nn f m Q q h -- check arity
 constructor
 · simpa only [pow_zero,mul_one] using f' (Vow.hymn A) (fun i=>sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>hx i j))
 simpa only [pow_zero,mul_one] using f' (fun i=>A i ∅) (fun i=>single_le_sum (fun j _=>hx i j) (mem_univ ∅))

abbrev kiosk (K:Cusp n):Pax n:=fun i=> K i ∅
omit q h0 h
lemma full_arms (fY:∀ i,‖φ i‖≤1)(t0:12≤ δ) : ArmsK P (C.issueK F l φ) τ H:=by
 have he(X:𝒜)(D:Support (More n))(h:D.Nonempty):Fray P H δ X D _ _:= C.flags_bill T l t w φ d z f Q hp X D h fY
 refine ⟨fun X D hX t=> (he X D hX).merit,fun X D hX t=> ?_⟩; let p:= he X D hX; refine ⟨?_,fun i v=> (p.loaf i v).2⟩
 intro x; funext i; by_contra u; exact x (Subset.trans (Yaw.touchK D) (Subset.trans (Corona.halo_mono t0 le_rfl) (p.loaf i u).1))
abbrev glow (B:Chart I (Seat n))(f: (I⊕ Force n)→ℝ)(Q:ℝ)(g:I→Aura n→ℝ)(X:Aura n):= (pack B Q f) X ∅+∑ i,g i X
local notation "σ"=>glow B f Q g
include q h h0 hv
variable (p1:∀ o:Seat n,tallB (fun S:Aura n=>∑ i,g i S) P.B m o ≤ c) (d':m=μ+s)(pu:0<s)
lemma first_all (fY:∀ i,‖φ i‖≤1) :∀ X,Medal P X.val ∅ (kiosk (C.issueK F l φ) X) H (σ X):=by
 exact fun i=> C.no_flags_bill T l t w φ d z f Q hp i fY _ (fun j=>hv j i) h q.2.2.2.2.1
include p1 d' pu
lemma running (u':0<∆+c)(v': degreePrice P.B (∆+c) s<1) : Ready Palot.stern P.B σ μ (∆+c) s (degreePrice P.B (∆+c) s):=by
 have hx:0≤σ:=fun i=> (first_all C T l t w 0 d z f m Q hp q g hv h h0 (fun i=>by simp) i).wage t -- signature tune
 apply Sour.ready_T u' pu v' hx; intro k
 rw [←d', show σ= (fun i:Aura n=>τ i ∅)+(fun S:Aura n=> ∑ i,g i S) from rfl, Larch.tall_add]; exact add_le_add (degree_sums f m Q q h h0 k).2 (p1 k)

end YM.CF.Coil.Chart.Stoke
