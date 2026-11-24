import YM.CF.DPress.Rise.Nu
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay DPress.Fees.Moral
open PowerSeries DPress DPress.Analytic Docket
open scoped YM.CF.Mew
namespace QHol
variable {N:Side}{P:BudgetPoint}{h:ℝ}{D:Docket P}(F:ℂ→ Cusp N)(K:ℂ→ Rinse (Seat N) (Copy N))
-- holomorphic at all visited inputs on THAT plane.All D for coefficient travel.Stax copies are opaque at invisible; later can only propagate on D⊆i.val.
abbrev Bright (L:ℝ)(F:ℂ→ Copy N):=∀ i:Orbit N,Holo (ank L) (fun z=> F z i)
abbrev HaloL (L:ℝ)(U:ℂ→ Cusp N) := ∀ i:Aura N,∀ j,Bright L fun k=> U k i j
abbrev HaloS(L:ℝ)(U:ℂ→ Cusp N) := ∀ i:Aura N,∀ j⊆i.val,Bright L fun k=> U k i j
-- pointwise PHP for Kernel readings
abbrev Render (L:ℝ) :Prop:=∀ i:Aura N,∀ r:Support (More N),∀ j:Aura N,∀ F:ℂ→ Copy N,∀ x:Orbit N,Holo (ank L) (fun z=> F z x)→Holo (ank L) (fun z=> K z i r j (F z) x)
variable {L:ℝ} (p:HaloL L F)(v:Render K L) (x:Orbit N) (X:Aura N)(r:Support (More N))
include p v
-- real formal coefficient series. real scalar reducing footprint joins across complexes.Pasta.
local notation "U" i:max=> Cadre.chip (K i) (F i)
lemma rod_h (j:ℕ): Holo (ank L) fun i:ℂ=> coeff j (Cadre.chip (K i) (F i) X r) x:=by
 induction j using Nat.strong_induction_on generalizing X r with
 | h j ih=>
    cases j with
    | zero=>simp_rw [Cadre.peg]; exact p _ _ _
    | succ j=>
       have h(i:ℂ): coeff (j+1) ((U i) X r)=((j:ℝ)+1)⁻¹ • coeff j (Cadre.stepL (K i) (U i) X r):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [h,Pi.smul_apply,Cadre.ore,Finset.sum_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; apply DifferentiableOn.fun_const_smul; refine DifferentiableOn.fun_sum fun i _=> DifferentiableOn.fun_sum fun G _=>?_ ; apply v _ _ _ _ x; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; refine DifferentiableOn.fun_sum fun z t=>DifferentiableOn.fun_finsetProd fun x d=>?_ ; exact ih (z x) (Nat.lt_succ_of_le ((single_le_sum (fun i _=> Nat.zero_le (z i)) d).trans_eq (mem_finsuppAntidiag.mp t).1)) _ _
lemma earn_χ (j:ℕ) : Holo (ank L) fun i:ℂ=> coeff j (Cadre.nutL (K i) (F i) X r) x:=by
 cases j; · simp_rw [show ∀ i:ℂ,(coeff 0 (Cadre.nutL (K i) (F i) X r)) x=(0:Cipher N) from fun _=> by rw [tick_r]; rfl]; exact differentiableOn_const _
 rename_i j; unfold Cadre.nutL; simp_rw [sprig,Pi.smul_apply,Cadre.front,Cadre.rill,map_sum,grate,coeff_mk,Finset.sum_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; apply DifferentiableOn.fun_const_smul; refine DifferentiableOn.fun_sum fun i _=> DifferentiableOn.fun_sum fun G _=>?_ ; apply v _ _ _ _ x; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; exact DifferentiableOn.fun_sum fun a _=>DifferentiableOn.fun_finsetProd fun j _=>rod_h F K p v x _ _ _
variable {μ:ℂ→ Aura N→ℝ}{I:ℂ→blazeK N}{B:ℂ → Orbit N→ Aura N→FC (Dwell N)}{q:ℕ}
variable (t:∀ i:ℂ,Account D (I i))(u:∀ i:ℂ,D.Chip (μ i))(w:1≤h)(f:∀ i:ℂ,bill P q h (I i) (F i))(Ψ:∀ i:ℂ,Stax.Pitch P h q (K i) (μ i) (B i))
omit p v in
private lemma zeroL: 0+wΨ ≤ wu P-wΨ*2:=by unfold wu wΨ; linarith [P.exponent_pos]
-- majorant timer two. Phase comp copies. at each support can use common const.
include t u f w Ψ
lemma inkV (g:r⊆ X.val): Holo (ank L) fun i:ℂ=>rem_X (P:=P) (F i) (K i) X r x:=by
 let Y:= (fun i=> D.earnB (μ i) (I i) (u i) (t i) |> D.sustain (μ i) (I i)); unfold rem_X lasting Vow.zenS; split; swap; exact differentiableOn_const _
 next hx=>
    let g':= loom_v 0 0 (widthK N P.B) 2 X; let η:=2* D.Week; let A:=η/g'; obtain ⟨Q,hd,σ⟩:=hx; apply Complex.differentiableOn_tsum_of_summable_norm ((summable_geometric_of_lt_one (show (0:ℝ) ≤ 2⁻¹ by norm_num) (by norm_num)).mul_left A) (earn_χ F K p v x X r) isOpen_ball; intro k i p; let V:=nutL (cribR (μ i)) (I i); let W':= deck (F i) (I i) (f i) _ (μ i) (Ψ i) (zero_le_one.trans w) X r g k; let e:= W'.merit.same x (Q,x.2) σ (fun _ _=>rfl); rw [e]; exact (W'.merit.capF w (Q,x.2) hd).trans (Cadre.palm_ V (fun i' R f'=> Cadre.heatR (μ i) (I i) (t i).nn (Ψ i).dice _ _) D.κ D.unitK 0 0 (widthK N P.B) η (fun z m=> (Y i).worth uΨ (show (0:ℝ)≤0 from le_rfl) (zeroL (P:=P)) _ (fun _ _ _=>tick_r _ _) (oreL0 _ _) z m) X r g k) -- tune
lemma halos : HaloS L (fun i=>RiseB P (F i) (K i)):=by
 intro X r g x; unfold RiseB Stax.lamp birthL; dsimp only; split; · simp only [Pi.add_apply]; exact ((p X r x).add (v X ∅ X (fun _=>1) x (differentiableOn_const _))).add (inkV F K p v x X r t u w f Ψ g)
 simp only [add_zero, Pi.add_apply]; exact (p X r x).add (inkV F K p v x X r t u w f Ψ g) -- tune birth. pattern
lemma logLp (Z:ℂ→ RegBudget N) (fZ:∀ (j:Scree.Hub N) (U':Pane N), Holo (ank L) (fun v=> Z v j U')) : DPress.Hues.Prosper L (fun v=> Colony P (F v) (K v) (Z v)):=by
 intro i h; let F'(v):= EmptyD (RiseB P (F v) (K v)); let Y(z):=EmptyD (F z); let μA(i):= Xhat D (I i) (μ i); have ht(i):=things (t i) (u i) w (f i) (Ψ i); have hV(i):= cloud (t i) (u i) w (f i) (Ψ i); have hA:0≤ P.supportExponent+1+1:= Kay.Penny.levZero _
 have hb:= glowing (Analytic.ank L) isOpen_ball F' i h μA ht hA w (fun i p=>(hV i p).2.1) (fun i j=> halos F K p v t u w f Ψ i ∅ (empty_subset _) j); have he:= glowing (Analytic.ank L) isOpen_ball Y i h μA ht hA w (fun i p=>(hV i p).1) (fun i j=> p i ∅ j); unfold Colony Nu Vow.zenS; dsimp only; split; next s=> exact (hb.sub he).sub (DifferentiableOn.fun_sum fun i _=>fZ i _)
 next s=> exact differentiableOn_const _
end QHol
end YM.CF.Sour.Heath
