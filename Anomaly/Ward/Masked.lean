import Anomaly.Ward.Raw
/-!
Use literal aperture Points for the (130) powers under the pressure buys.
No Holder on moving across a failed consultation. For using at Loom openings
for Fock, see Mark economics qualifications later.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Rank.Spindle LampP Exterior Precision Wilson
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000

variable {b k:ℕ}{n:Side}{m:ℕ}{K: Loom n}{B: BudgetPoint}{X:SOp n}{a s d α C M D w q:ℝ}{o:Site n}
variable {T:tableQ SU.group (More n) ℂ} (R:Knit X (node o) b d α M C w m T)(L:mintQ α C d m)
variable (H:Roof n s d k K)(hb: b+k+10≤ B.B)(hs:B.threshold ≤ s)
local notation "Πp" => tangD n
local notation "Y" => fieldDir SU.group (More n) 1
local notation "μ" => 2*C*M
local notation "Ωx" => halo B.B {node o}
local notation "Σx" => halo b {node o}
local notation "Ψ" => traceMeter B K o X

include R L
lemma debit0 :0≤μ:=(R.circle 0 (norm_zero.trans_lt L.1)).nonneg -- include
omit L
include H hb hs R
lemma brightEq {u:Pane n}(p:pingS B.threshold (halo B.B {node o}) u){V:Pane n}(t: Agrees (halo b {node o}) u V) (g:Guard V d): traceMeter B K o X u= rawQ X V:=by
 unfold traceMeter pinMatrix; rw [Set.indicator_of_mem (show u ∈ {z:Pane n|pingS B.threshold _ z} from p)]
 let x:Orbit n:=(u,Classical.arbitrary _); let W:fenceP n d:=⟨K x,H.paid x⟩
 refine R.landsQ W ⟨V,g⟩ (fun i he l=> (?_ : K x i=V i))
 let D:Vow.Aura n:=⟨Ωx,⟨node o, halo_subset _ _ (mem_singleton_self _)⟩⟩
 have hv:= fern (X:=D) H hs (halo b {node o}) ?_ u (show u ∈ σX B D ∅ from ⟨by rw [sdiff_empty]; exact p,empty_subset _⟩) i he rfl x.2
 · exact hv.trans (t i he l)
 intro i hi; obtain ⟨y,p,F⟩:=halo_spec.mp hi; obtain ⟨_,w,u⟩:=halo_spec.mp p; refine halo_spec.mpr ⟨_,w,(separation_triangle _ y _).trans (by omega)⟩
lemma template_pass {u:Pane n} (p:pingS B.threshold (halo B.B {node o}) u)(f:Seat n→ SU.group.El){V:Pane n}(t: Agrees (halo b {node o}) (gauge f u) V) (g:Guard V d): traceMeter B K o X u= rawQ X V:=by
 let U:=gauge f⁻¹ V
 have he:Agrees Σx u U:=by
    intro i v l; unfold U Lattice.gauge; rw [← t i v l]; unfold Lattice.gauge; simp only [Pi.inv_apply,inv_inv]; group
 have hv:Guard U d:=g.cov _; rw [brightEq R H hb hs p he hv]; exact R.engage ⟨V,g⟩ _
include L
abbrev maskBudget (B: BudgetPoint)(b:ℕ)(C M:ℝ):=8*C*M*(8*b*B.threshold)^2
lemma maskScale (u:Pane n)(r: Rules SU.group)(hp:3 ≤ m)(hv: 4*(b:ℝ)*B.threshold≤r.c)(ht:2*(b+1)<(More n).val)(g:8*b*B.threshold<α) : ‖traceMeter B K o X u‖ ≤ ‖rawQ X 1‖+ maskBudget B b C M:=by
 let z:=node o; let p:=halo B.B {z}; have hx:0≤μ:=(R.circle 0 (norm_zero.trans_lt L.1)).nonneg
 by_cases w:pingS B.threshold p u
 · have hf:Healthy B.threshold Σx u:= ping_le (Vow.grow_b (Corona.halo_mono (by omega : b≤B.B) le_rfl) w)
   obtain ⟨y,hi,p'⟩:= treeCost z r B.threshold_pos hv ht hf
   let A:fenceP n d:=⟨increment 1 y,L.2.2.2.1 y (hi.trans_lt g)⟩
   rw [template_pass R H hb hs w (fingers u z) (fun i h x=>(p' i h x).symm) (show Guard A.val d from A.property)]; let G:=stepQ X
   rw [show rawQ X A.val= G y + rawQ X 1 from (sub_add_cancel ..).symm]; refine ((norm_add_le ..).trans_eq (add_comm ..)).trans (add_le_add_right ?_ _)
   have he:= gaugeTaylor (norm_zero.trans_lt L.1) (f:=G) (fun x h=> (R.circle x h).order hp) (step_idle _) R.roles (hi.trans_lt g)
   have hv: ‖trim 2 G y‖ ≤ μ * ‖y‖^2:=by
      unfold trim cake Tensor.diagonal; simp only [_root_.smul_apply,norm_smul,norm_inv]
      have ht:= R.circle 0 (norm_zero.trans_lt L.1); apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [Nat.factorial])) ; refine ((iteratedFDeriv ℝ 2 G _).le_opNorm _).trans ?_; simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (ht.2 2 (by omega)) (sq_nonneg _)
   apply (norm_le_norm_sub_add ..).trans ((add_le_add he hv).trans (?_)); have ha:= pow_le_pow_left₀ (norm_nonneg _) hi 2; have hr: ‖y‖^3 ≤ ‖y‖^2:= pow_le_pow_of_le_one (norm_nonneg _) ((hi.trans g.le).trans L.2.1) (by omega); unfold maskBudget; nlinarith only [mul_le_mul_of_nonneg_left ha hx, mul_le_mul_of_nonneg_left hr hx, mul_nonneg hx (sq_nonneg ‖y‖)]
 unfold traceMeter pinMatrix; rw [Set.indicator_of_notMem (show u∉{z:Pane n|pingS B.threshold p z} from w),Matrix.trace_zero,norm_zero]
 exact add_nonneg (norm_nonneg _) (by unfold maskBudget; nlinarith only [mul_nonneg hx (sq_nonneg (8*(b:ℝ)*B.threshold))])

lemma evaluation (V:Pane n)(p: pingS B.threshold Ωx V)(W:Y){η:ℝ} (f: Agrees Σx V (represent W)) (v:‖collect SU.group W‖≤η)(g:η<α)(u:3 ≤ m) : ‖traceMeter B K o X V-rawQ X 1- tariff T (receipt W)‖ ≤ μ * η^3:=by
 let G:=collect SU.group W; let U:=represent W
 have hw:= gaugeTaylor (norm_zero.trans_lt L.1) (f:=stepQ X) (fun x h=> (R.circle x h).order u) (step_idle _) R.roles (v.trans_lt g)
 rw [R.poses,brightEq R H hb hs p f (L.2.2.2.1 G (v.trans_lt g))]
 exact hw.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) v _) (debit0 R L))
end YM.CF.Swell.Sonar
