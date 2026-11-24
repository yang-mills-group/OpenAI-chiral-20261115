import YM.CF.Vp929.Contour.Hues
import YM.CF.Song.Pads
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Bake Gas Wray Larch Nor
variable {a s d δ γ:ℝ}{G H:Pax n}
variable (p:0<d)(vx:0≤a)(h':1≤h)

abbrev ticket_f (B:ℕ)(x d:ℝ) := x * (1-degreePrice B x d)⁻¹
local notation "qψ"=> degreePrice P.B γ d
structure FeeBook(B:ℕ)(γ d:ℝ):Prop where
 coal :0<γ
 beats :0<d
 rate :degreePrice B γ d<1
 nominal: 0≤degreePrice B γ d
namespace FeeBook
variable (q: FeeBook P.B γ d)
include q h'
lemma seats (R:MonoQ P h (a+d) G γ):∃ T:Aura n→ℝ,(∀ i,Vow.Medal P i.val ∅ (G i) h (T i))∧ Trees.Ready Palot.stern P.B T a γ d qψ:=by
 obtain ⟨T,H,V⟩:=R; exact ⟨T,H, Sour.ready_T q.coal q.beats q.rate (fun i=>(H i).wage (zero_le_one.trans h')) V⟩
include vx q
lemma regular(R:MonoQ P h (a+d) G γ)(k:ℕ): MonoQ P h a (fun i=> spinD P i G k) (γ*qψ^k*(1-qψ)⁻¹):= by obtain ⟨T,H,V⟩:= q.seats h' R; exact ⟨_,fun i=> glenP i h' H V vx k, fun i=> thinX V vx i k⟩
lemma fee (R:MonoQ P h (a+d) G γ) : MonoQ P h a (FeeD P G) (ticket_f P.B γ d) := by simpa [ticket_f,FeeD] using q.regular vx h' R 0
local notation "LD"=> FeeD P
private lemma spinV (R:MonoQ P h (a+d) G γ)(X:Aura n)(V':Orbit n)(u: Vow.visible P X.val ∅ V'.1)(b:ℕ): FeeD P G X V'= (∑ j∈range b, funge X G 0 j V')+spinD P X G b V':=by
 obtain ⟨T,H,V⟩:= q.seats h' R
 unfold FeeD spinD lasting zenS; rw [if_pos u,if_pos u]; let I(m j:ℕ):= funge X G m j V'
 let he:= raid_r X V' V h' H vx 0 u; let hx:= raid_r X V' V h' H vx b u
 have hv(j:ℕ): funge X G b (j+b) = funge X G 0 (j+b):=by simp [funge,sta]
 have hp(j:ℕ)(h:j<b):funge X G b j=0:=by simp [funge,sta,h.not_ge]
 dsimp only; rw [←he.sum_add_tsum_nat_add b, ←hx.sum_add_tsum_nat_add b, sum_eq_zero (s:=range b) (f:=fun j=>funge X G b j V') (fun i p=>by rw [hp i (mem_range.mp p)]; rfl),zero_add]; simp_rw [hv]
lemma analytic{L:Set ℂ}(H:IsOpen L)(F:ℂ→ Pax n)(hQ:∀ z∈L,MonoQ P h (a+d) (F z) γ)(u:∀ j V,DifferentiableOn ℂ (fun z=>F z j V) L)(X:Aura n)(V:Orbit n): DifferentiableOn ℂ (fun z=> FeeD P (F z) X V) L:= by
 by_cases hs: Vow.visible P X.val ∅ V.1; swap; · exact (differentiableOn_const (𝕜:=ℂ) (0:Cipher n)).congr (fun _ _=>if_neg hs)
 let W(i:ℕ):= γ*qψ^i*(1-qψ)⁻¹; have hb: Tendsto W atTop (𝓝 0):= by simpa only [zero_mul,mul_zero] using (tendsto_const_nhds (x:=γ)|>.mul (tendsto_pow_atTop_nhds_zero_of_lt_one q.nominal q.rate)).mul_const ((1-qψ)⁻¹)
 let G(k:ℕ)(z:ℂ):= ∑ j∈range k,funge X (F z) 0 j V
 have hg:TendstoUniformlyOn G (fun z=> FeeD P (F z) X V) atTop L:= Metric.tendstoUniformlyOn_iff.mpr (fun b hb' => by
    filter_upwards [hb.eventually (gt_mem_nhds hb')] with i p z hz
    change _ <b; rw [q.spinV vx h' (hQ z hz) _ _ hs i]; unfold G; rw [dist_eq_norm,(by abel : (∑ j∈range i,funge X (F z) 0 j V)+spinD P X (F z) i V-(∑ j∈range i,funge X (F z) 0 j V)=spinD P X (F z) i V)]; apply lt_of_le_of_lt _ (show W i<b from p); obtain ⟨u,p,v⟩:= hs; let t:= (q.regular vx h' (hQ z hz) i).part h' vx X; change ‖spinD P X (F z) i V‖≤ W i; rw [t.same V (u,V.2) v (fun _ _=>rfl)]; exact t.capF h' (u,V.2) p)
 apply hg.tendstoLocallyUniformlyOn.differentiableOn _ H
 refine Eventually.of_forall fun i=> DifferentiableOn.fun_sum fun j v=>?_
 unfold funge; simp_rw [Finset.sum_apply]; apply DifferentiableOn.fun_sum; intro x _; unfold sta; split_ifs with k; swap; · exact differentiableOn_const _
 unfold guava; simp only [Pi.smul_apply,Finset.prod_apply]; exact (DifferentiableOn.fun_finsetProd (u:=univ) fun k _=> u (x k) V).const_smul (coefficient Palot.gRule x/(j+1).factorial:ℝ)
end FeeBook
end YM.CF.Py.Rate
