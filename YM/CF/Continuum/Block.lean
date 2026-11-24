import YM.CF.Mint.Bier
import YM.CF.Mint.Key
import YM.CF.Continuum.Billhead
/-!
# Blocked estimate report: relative size of whole-box complements

Take level zero at a pivot β0=x. Reference integral used in `Roe.costR`
is `Graph.start`; the relative bills in all terms going through `shot`
for the very SAME normalization, **including the vacuum Opt**, scale with
`Graph.drip`. Beam gets no volume-uniform normalized short-distance estimates
from these. This file shows where they fail. A statement about the BILL in
that estimate (including its improved version), NOT a divergence proof for actual
correlations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function NormedSpace Filter Finset Lattice Laurent Wilson Analysis Pressure MeasureTheory Mint Graph Tulip Lat Cube SU Emu Rush Scree RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 8192
variable {a b c w η r e K b' v C' l s' D μ y H L':ℝ}{J B m:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
local notation "Λ" => CSide m B
lemma angel_upper (X:GramM Λ) (p:P.roundZ ≤ (CSide m B).val) (hp:0<e) : Kea.angel m P X.J.M ≤ 1 := by
  have hw := sea_g p (Kea.tax emptyC) (tax_guard _ (More Λ) e hp.le) X.J.M
  exact (norm_inner_le_norm (𝕜:=ℂ) ..).trans_eq (by rw [(Dial.tickB Λ).2,hw.2,one_mul])
-- Suppression outside cap is at most β*c*threshold² in the old estimate,
-- not proportional to volume. Keep tax term exactly since it *cancels* a
-- universal upper bound on our dividing factor.
lemma drip_max (Z:Pic.Span hP K b' v C' l s' k) (X:GramM Λ) (t:Girt.Ward X) (a:0≤X.beta)
    (p:X.path.Bounds X.funds μ D L') (hn:k ≤ (CSide m B).val) (h:0≤D) :
    0 < drip X P ∧ drip X P ≤ Real.exp (taxY (More Λ) X.beta X.p.threshold D L') := by
  let r := X.p.threshold; let T := taxY (More Λ) X.beta X.p.threshold D L'
  have hr : 0<r:= X.p.threshold_pos
  have hu : 0< Graph.angle X:= by
    have hx : 0 < gainS (More Λ) (r/4):=by unfold gainS; positivity
    have hw:= glow t p (u:=r/4) (by positivity) (show r/4≤1 by linarith only [show r≤1 from X.p.threshold_le]) (by unfold r; ring_nf; rfl) (le_refl X.funds.direct) h a
    exact lt_of_lt_of_le (mul_pos hx (Real.exp_pos _)) hw
  refine ⟨mul_pos hu (Kea.angel_p hP Z.stmt (Z.plan m hn).1 Z.p Z.eP X.J.M (Z.plan m hn).2),?_⟩
  have he : Graph.angle X ≤ Real.exp T := by
    have hp : ∀ i:Orbit Λ, Graph.dim X i≤Real.exp T:=by
      intro i; by_cases h:i∈Lace X
      · rw [Graph.dim, Set.indicator_of_mem h]; exact Real.exp_le_exp.mpr (neg_le.mp (energy_low X.p X.path _ p a i.1))
      rw [Graph.dim,Set.indicator_of_notMem h]; exact (Real.exp_pos _).le
    exact (integral_mono ((Graph.worth t).integrable _) (integrable_const _) hp).trans_eq (by simp)
  exact le_trans (mul_le_of_le_one_right hu.le (angel_upper X (Z.plan m hn).1 Z.eP)) he

local notation "I" => GramM Λ
lemma flagBill_eq (n:Side)(v η C:ℝ) : flagBill n v η C=(4*C+(v+v+η)*2^4+180*45*6*C)*n.val^4 := by unfold flagBill Graph.pittance Graph.doorF lark; simp only [More]; push_cast; ring
lemma improves_flagBill(n:Side)(v η C:ℝ)(h : 0 ≤ C) : flagBill n v η C≤ flagT n v η C:=by
  have hn : 1≤ (n.val:ℝ):= Nat.one_le_cast.mpr n.property; have hv : 1 ≤ lark n:=by unfold lark; nlinarith [show 1 ≤ (n.val:ℝ)^4 from one_le_pow₀ hn]
  unfold flagBill flagT; gcongr; exact le_mul_of_one_le_left (by unfold doorF lark; positivity) (one_le_pow₀ hv)

def outsideRatio (D L' v η C w : ℝ) (X:I)(P:Grasp Y B e) := Real.exp (flagBill Λ v η C - kinetic (More Λ) X.p D L' X.beta w)/drip X P
-- uniforms: same q requirements in the effective lemma; no volume upper
lemma breaks_shot {M : ℕ→Side}(X:∀ i,GramM (CSide (M i) B)) (p : Tendsto (eur (fun i=>CSide (M i) B)) atTop atTop)
    (Z:Pic.Span hP K b' v C' l s' k) (u:∀ᶠ i in atTop,Girt.Ward (X i) ∧ (X i).path.Bounds (X i).funds μ D L')
    (x r0 C v' η w : ℝ)(h : ∀ i,(X i).beta=x ∧ (X i).p.threshold=r0)
    (ht:0 ≤ x)(hC:0 < C)(hv:0≤v')(hg:0≤η)(hp:0≤D) :
    Tendsto (fun i=> outsideRatio D L' v' η C w (X i) P) atTop atTop := by
  let Q(i:ℕ):= CSide (M i) B; let N:=eur Q; let y:=4*C+(v'+v'+η)*2^4+180*45*6*C
  have hy:0<y:=by unfold y; positivity
  have hb : Tendsto (fun i=> Real.exp (y*N i^4 - x*(w*r0^2))) atTop atTop := Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ (-(x*(w*r0^2))) (((tendsto_pow_atTop (n:=4) (by omega)).comp p).const_mul_atTop hy))
  refine tendsto_atTop_mono' _ ?_ hb
  filter_upwards [p.eventually_ge_atTop (k:ℝ),u] with i e wK
  let A:=drip (X i) P; obtain ⟨ha,he⟩:=drip_max Z (X i) wK.1 (le_trans ht (h i).1.symm.le) wK.2 (Nat.cast_le.mp e) hp
  unfold outsideRatio; apply (le_div_iff₀ ha).2; refine le_trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le) ?_
  apply le_of_eq; unfold kinetic; rw [←Real.exp_add,flagBill_eq,(h i).1,(h i).2]; congr 1; unfold N y Q eur; ring
lemma breaks_pittance {M : ℕ→Side}(h : Tendsto (eur M) atTop atTop){vA C : ℝ}(t : 0<vA)(a : 0<C) : Tendsto (fun i=> pittance (M i) vA C) atTop atTop := ((tendsto_pow_atTop (n:=4) (by decide)).comp h).const_mul_atTop (show 0<vA^2*C by positivity)
end YM.CF.Window
