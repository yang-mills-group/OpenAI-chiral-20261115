import YM.CF.BProof.Counter.Jet
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi.Denn
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D' Y Z:Support (More n)}{U:Pane n}
open AnalyticBridge.VerifiedReset Next.Foundations Push.Local PhysicalNext.JointLoad Heir
open Vow Rue Ione Larch Beau Floral
structure Cart (n:Side)(m:ℕ) where
 w:Skye.Seat n→ Skye.Seat n→ ℝ
 nn(x y:Skye.Seat n):0≤w x y
 day (x:Skye.Seat n):∑ y:Skye.Seat n,w x y=1
 far(x y:Skye.Seat n) (t:w x y≠0):separation x y≤ m
namespace Cart
variable (C:Cart n m)
abbrev Turns(C:Cart n m)(s:Sweep n):Prop:=∀ x y,C.w ((boxA s).symm x) ((boxA s).symm y)= C.w x y
def stay(n:Side)(m:ℕ) : Cart n m where
 w x y:=if x=y then 1 else 0
 nn x y:=by split_ifs<;>simp
 day x:=by simp
 far x y p:=by by_contra h; simp [show x ≠ y from fun v=> h (by simp [v])] at p
lemma stays (s:Sweep n):Turns (stay n m) s:=fun x y=>by simp [stay]
end Cart
def Er(n:Side)(a:ℝ):RegBudget n:= sunY univ block (fun x=>W x a)
lemma first(i:Scree.Hub n) : Er n a i=if block i.val.1=i then W i.val.1 a else 0:=by
 unfold Er sunY; rw [sum_filter]; split_ifs with t
 · rw [sum_eq_single i.val.1]; rw [if_pos t]; intro b _ v; rw [if_neg (fun w=>v (congrArg (fun i:Scree.Hub n=>i.val.1) w))]; simp
 exact sum_eq_zero fun j _=> if_neg (fun h=> t (by rw [←h]))
lemma Er_1(i:Scree.Hub n): Er n a i 1=0:=by rw [first]; split; exact W_1 ..; rfl
lemma mass_small (i: Support (More n))(p:coverNumber P.B i ≤ 1)(t:0 ≤ a): P.mass i a≤ Real.exp P.supportExponent*a:=by unfold BudgetPoint.mass; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_of_le_one_right P.exponent_pos.le (by exact_mod_cast p))) t
lemma jet_nn(m:ℕ)(P:BudgetPoint){Γ:ℝ}(k:0≤Γ)(a:ℝ):0 ≤ jet P m Γ a:=by unfold jet TC; have := Compass.compass_cost_nn SU.group P; positivity
lemma turn_sun {ι:Type*}[Fintype ι](s:Sweep n)(U:Pane n)(i:Scree.Hub n)(f:ι→ Scree.Hub n)(G:ι→InkD n)(H:Equiv.Perm ι)(u:∀ j,f (H j)=moveHub s (f j))(C:Cipher n→ₐ[ℝ] Cipher n)(p:∀ j,G (H j) (flashA s U)=C (G j U)): (sunY univ f G) (moveHub s i) (flashA s U)= C (sunY univ f G i U):=by
 classical
 unfold sunY; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; symm; apply Finset.sum_equiv H; · intro j; simp only [mem_filter,mem_univ,true_and,u,(Haro.pure_s s).eq_iff]
 exact fun j _=>(p j).symm
lemma Er_full (m:ℕ)(P:BudgetPoint)(k:6≤P.B)(a:ℝ){Γ:ℝ}(g:0≤Γ)(t:DayT P.order Γ): IncX Utrue (Er n a) P h (Real.exp P.supportExponent*jet P m Γ a):=by
 let v:=jet P m Γ a; let F(x:Skye.Seat n):=W x a; have he:= feat_v (h:=h) (R:=univ) block F (fun _=>v) P (Real.exp P.supportExponent*v) (fun i _=>W_paid _ _ _ le_rfl (by change separation i i ≤ m; simp) t) fun i=> ?_
 refine ⟨he.weight,fun s _ V _ i x=>turn_sun s x i block F (boxA s).symm (block_map s) _ fun y=> W_turn s y _⟩
 change (∑ y: Skye.Seat n with y=i,P.mass _ _) ≤ (Real.exp P.supportExponent*(jet P m Γ a)); simpa [v,sum_filter] using mass_small (P:=P) (block i).val.2 (cover_c P i k) (jet_nn m P g a) -- tactic order
lemma mot_all (x:Site n): ∑ i:Site n,motto i x=1:=by
 unfold motto; rw [←Finset.mul_sum,sum_comm,sum_congr rfl (fun i _=> ?_),sum_const,card_univ,nsmul_eq_mul,mul_one]; exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
 have hp(i':Site n): x=i'+boot i ↔ i'= x-boot i:=⟨fun h=>by rw [h]; abel, fun h=>by rw [h]; abel⟩; simp [hp]
private lemma hess_zero(x:Scree.Hub n)(a b):fluxP x 0 a b=0:=by unfold fluxP; split; exact hessian_zero ..; rfl
private lemma is_pave(P:BudgetPoint)(k:6 ≤ P.B){L:ℕ}(t:1<L)(x:Scree.Hub n)(h:block x.val.1=x): chute P L x:=by unfold chute Pave; have p:= (cover_c P x.val.1 k); rw [h] at p; refine lt_of_le_of_lt (le_trans (pow_le_pow_left' p 3) ?_) t; norm_num
lemma alpha_δ(P:BudgetPoint)(a:ℝ){L:ℕ}(k:6≤ P.B)(t:1<L)(hn:60<(More n).val): aora P L (Er n a)=a:=by
 let Q:= caw P L (cry_H (Er n a)); let Y:= realH Q
 have h(x:Scree.Hub n)(V:Pane n):Y x V=if block x.val.1=x then a * (wish x.val.1 V) else 0:=by
    change Complex.reCLM (pot (∅:Finset (Dwell n)) (caw P L (cry_H (Er n a)) x V)) = _; unfold caw; split
    next v=> change Complex.reCLM (pot ∅ (sage_L _ V))= _; rw [no_p, first]; split
             next t=> unfold W; rw [Function.comp_apply,mold_l]; rfl
             next t=> change Complex.reCLM (pot (∅:Finset (Dwell n)) 0)=0; rw [map_zero,map_zero]
    next g=> rw [if_neg (fun h=>g (is_pave P k t x h))]; rw [Pi.zero_apply,map_zero,map_zero]
 let b:= Averaging.axes01
 have hl(x:Skye.Seat n): fluxP (block x) (Y (block x)) b b=a:=by
    rw [show Y (block x)= a • (Compass.W x) from funext fun i=>(h _ i).trans (if_pos rfl)]; unfold fluxP; rw [if_pos]; exact Compass.W_proj P Thera.yet_one x (by omega) b a
    intro y p; have hx: Lattice.halo 2 {x}⊆ Lattice.halo 6 {x}:=Corona.halo_mono (by norm_num) le_rfl; have hu:y∈Lattice.halo 6 {x}:= Finset.union_subset hx le_rfl p; simp only [halo_spec,mem_singleton,exists_eq_left] at hu; change 10*separation y x<(More n).val; rw [separation_comm y]; omega
 have hy (x:Skye.Seat n): (∑ i:Scree.Hub n with i.val.1=x, motto i.val.1 0 * fluxP i (Y i) b b)= motto x 0 * a:=by
    rw [sum_eq_single (block x)]; rw [hl]; intro j p v; have hv:= (mem_filter.mp p).2; rw [show Y j=0 from funext fun i=>(h j i).trans (if_neg (show block j.val.1 ≠ j from (by rw [hv]; exact Ne.symm v))), hess_zero,mul_zero]; exact fun z=> False.elim (z (mem_filter.mpr ⟨mem_univ _,rfl⟩)) -- rw hl maybe rfl
 unfold aora lureC payoutF; rw [←sum_fiberwise (univ:Finset (Scree.Hub n)) (fun i=>i.val.1),sum_congr rfl (fun i _=> hy i),← sum_mul,mot_all,one_mul]
end YM.CF.Taxi.Denn
