import YM.CF.Vp929.Match.Outcrop
import YM.CF.Vp929.Pre.Fee
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
open Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
variable {N:Side} {p:BudgetPoint} {B:ℕ} {W:ℝ}(w0:1≤W)
variable (K:Rinse (Seat N) (Copy N)){M:Bag N}(P₀:Aura N→ℝ)(F:Vow.Cusp N)(I:Aura N→Support (More N)→ℝ)(pK: Tint p W (cipherK B) K P₀ M)
variable (f:∀ X:Aura N,∀ D⊆ X.val, Fray p W (cipherK B) X D (F X D) (I X D))
local notation "τx"=> P₀
variable {z u μ ℓ α β ε K0 M1 J:ℝ}{l:ℕ} (op:Timer (Cadre.chip (cribR (P₀)) I) (P₀) z u μ (widthK N p.B) (spanV p.B) M1 J ε K0 1 (P₀))(ht:0 ≤ ℓ)(hp:0 < α)(pf:ℓ+α≤ u-μ*1)
local notation "νL"=> (Stax.lamp (P:=p) F K)
local notation "N'"=> Cadre.chip (cribR τx) I
local notation "N₁"=> nutL (cribR τx) I
local notation "φW"=> (ε*M1+spanV p.B*α⁻¹*M1*J)
open Push.AbsoluteSums Haro Glyph Trees
local notation "G0"=> fun X:Aura N=>F X ∅
local notation "P'"=> (p.supportExponent+1+1)
variable (δ σ s φ' :ℝ)(d0:0<δ)(vφ:p.supportExponent+1+1+δ≤ℓ)(hv_:∀ i:Seat N,tallB (urnL I) p.B (p.supportExponent+1+1+δ) i ≤ σ)
variable (hx_:0<s)(hQ:0 < φ')(hu:degreePrice p.B φ' δ<1)(pt:σ+M1+s*(K0+(ε*M1+spanV p.B*α⁻¹*M1*J)) ≤ φ')
open Ursell
local notation "Vx"=> (Sco I (P₀))
local notation "Vℓ"=> (ScoL I (P₀))
local notation "A0"=> (urnL I+urnL (Sco I (P₀))+s • ((P₀) +urnL (ScoL I (P₀))))
local notation "qB"=> degreePrice p.B φ' δ
local notation "F'" => (fun X:Aura N=>νL X ∅)
local notation "RΨ"=> (fun X:Aura N=>rem_X (P:=p) F K X ∅)
include w0 pK op ht hp pf f d0 vφ hv_ hx_ hQ hu pt
/-! Generalize Cupo to a projection-independent kernel and Timer -/
lemma glyph_c : Ready stern p.B A0 (p.supportExponent+1+1) φ' δ (degreePrice p.B φ' δ) ∧ (∀ X:Aura N, Medal p X.val ∅ ((F') X) W (A0 X)) ∧(∀ X:Aura N,Medal p X.val ∅ ((G0) X) W (A0 X)) ∧(∀ X:Aura N,Medal p X.val ∅ ((F') X-(G0) X) W (s⁻¹*A0 X)) ∧ (∀ X:Aura N, Medal p X.val ∅ (RΨ X) W (Vℓ X ∅))∧(∀ i:Seat N,tallB (Vow.hymn Vx) p.B P' i ≤ z⁻¹*M1)∧∀ i:Seat N,tallB (urnL Vℓ) p.B P' i≤ φW:=by
 obtain ⟨x,w',u'⟩:=Stax.rentK F I f K τx pK _ _ _ _ _ _ _ _ _ _ _ op hp ht pf w0; let H:=zero_le_one.trans w0; have hu(x): 0≤ (P₀) x:=op.mid x
 have hf(i:Aura N)(D:Support (More N))(r:D⊆i.val):0≤ Vx i D:= (x i D r).1.merit.wage H
 have hv₁(i:Aura N)(D:Support (More N))(r:D⊆i.val):0≤ Vℓ i D:= (x i D r).2.merit.wage H
 have h2(i):0 ≤ (P₀) i+ urnL Vℓ i:= add_nonneg (hu i) (hv₁ i _ (empty_subset _)); have h3(i):0 ≤ I i ∅:= (f i _ (empty_subset _)).merit.wage H; have h4(i):0 ≤ s*((P₀) i+urnL Vℓ i):= mul_nonneg hx_.le (h2 i); have ht(i): Vx i ∅≤ A0 i:= le_trans (le_add_of_nonneg_left (a:=Vx i ∅) (h3 i)) (le_add_of_nonneg_right (h4 i))
 have hL: 0 < z:= zero_lt_one.trans_le op.slope
 have h1(o:Seat N):tallB (urnL Vx) p.B (P'+δ) o≤ M1 ∧ tallB (Vow.hymn Vx) p.B P' o≤ z⁻¹*M1 ∧ tallB (urnL Vℓ) p.B (P'+δ) o≤φW:=by
    obtain ⟨a,b⟩:=lam_H (b:=M1) Vx o z p.B (u-μ*1) hL hf (by rw [parse]; exact w' o); have hc:tallB (roofL Vℓ z) p.B ℓ o≤ φW:=by nth_rw 1 [show ℓ=ℓ-0*1 from by ring]; rw [parse]; exact u' o
    have hh':P'+δ≤ u-μ*1:= vφ.trans ((le_add_of_nonneg_right hp.le).trans pf)
    exact ⟨(tall_m _ (fun i=>hf i _ (empty_subset _)) hh' o).trans a,(tall_m _ (fun i=>sum_nonneg (fun j u=>hf _ _ (mem_filter.mp u).2.2)) ((le_add_of_nonneg_right d0.le).trans hh') o).trans b,(tall_m _ (fun i=> hv₁ i _ (empty_subset _)) vφ o).trans (lam_H Vℓ o z p.B _ hL hv₁ hc).1⟩
 refine ⟨ready_T (P:=p) hQ d0 (by assumption) (fun i=> (hf _ _ (empty_subset _)).trans (ht i)) ?_,fun i=> (x _ _ (empty_subset _)).1.merit.big (ht i),fun i=>(f _ _ (empty_subset _)).merit.big ((le_add_of_nonneg_right (hf i _ (empty_subset _))).trans (le_add_of_nonneg_right (h4 i))), ?_,fun i=> (x _ _ (empty_subset _)).2.merit,fun i=> (h1 i).2.1,fun i=> (tall_m _ (fun j=> hv₁ j _ (empty_subset _)) (le_add_of_nonneg_right d0.le) i).trans (h1 i).2.2⟩
 · intro i; rw [tall_add,tall_add,tall_s,tall_add]; refine le_trans (add_le_add (add_le_add (hv_ i) (h1 i).1) (mul_le_mul_of_nonneg_left (add_le_add (show tallB (P₀) p.B (P'+δ) i ≤ K0 from ?_) (h1 i).2.2) hx_.le)) pt
   exact (tall_m _ op.mid (show P'+δ ≤ u-μ*0 by have he:=op.hop; linarith only [pf,hp,vφ,he]) _).trans (by rw [parse]; exact op.birth _)
 intro X; have hz:νL X ∅-F X ∅=Stax.birthL K X ∅+ RΨ X:= by unfold Stax.lamp; change F X ∅+_+RΨ X-F X ∅=_; abel
 rw [hz]; have hv'':=Stax.aptL F I f (K) τx pK w0 X _ (empty_subset _); refine (hv''.merit.plus (x X _ (empty_subset _)).2.merit).big ?_; unfold δWeight; rw [if_pos rfl, le_inv_mul_iff₀ hx_]; exact le_add_of_nonneg_left (add_nonneg (h3 X) (hf X _ (empty_subset _)))
open Py.Rate
lemma sellΦ (E:RegBudget N)(x:∀ X V, Stax.birthL K X ∅ V = orbV E X V): MonoQ p W P' (Nu p F' G0 E) (uk_b φW s φ' qB)∧ MonoQ p W (P'+δ) F' φ'∧(∃ C':Vow.blazeK N,ArmsK p νL C' W ∧ ∀ i:Seat N, tallB (Vow.hymn C') p.B P' i ≤ z⁻¹*M1):=by
 obtain ⟨q,m,q',r,rm,zs,zq⟩:= glyph_c w0 K P₀ F I pK f op ht hp pf δ σ s φ' d0 vφ hv_ hx_ hQ hu pt
 have hw(X:Aura N)(V:Orbit N):F' X V=G0 X V+orbV E X V+ RΨ X V:=by rw [←x]; rfl
 have hx':= Stax.rentK F I f K τx pK _ _ _ _ _ _ _ _ _ _ _ op hp ht pf w0
 exact ⟨⟨_,Larch.α_G E s hx_ q w0 m q' r rm hw, fun i=> Larch.cost_p E s hx_ q w0 m q' r rm hw i (zq i)⟩,⟨_,m,dutyK q⟩,⟨_,frame_v (fun i D p=> (hx'.1 i D p).1),zs⟩⟩
end YM.CF.Sour
