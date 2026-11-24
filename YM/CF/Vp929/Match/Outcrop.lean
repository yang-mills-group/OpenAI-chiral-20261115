import YM.CF.Vp929.Match.Radical
import YM.CF.Pso.Ferd
import YM.CF.Vp929.Contour.Hues
import YM.CF.Vp929.Kinematic.Vise
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
variable {K U R:Rinse (Seat n) (Copy n)}
variable (p:BudgetPoint)(W:ℝ)(δ:ℕ)
variable {a₀ a₁:Aura n→ℝ}{M N:Bag n}
open PowerSeries
abbrev Tint (p:BudgetPoint)(W:ℝ)(δ:ℕ)(K:Rinse (Seat n) (Copy n))(a₀:Aura n→ℝ)(M:Bag n):=Pitch p W δ K a₀ (fun i Y=>M Y i)
structure PictureT (p:BudgetPoint)(δ:ℕ)(K:Rinse (Seat n) (Copy n))(M:Bag n):Prop where
 actsF :∀ X D Y F i, (K X D Y F i).val = if Bias.αt Y X D δ then Sault.rind (coll_T p X D (M Y) i*(F i).val) else 0
lemma bias_pic (g:Bias δ M p W a₀):PictureT p δ g.payX M := by
 constructor; intro X D Y F i; split; rename_i h; exact g.truth X D Y F h i
 rename_i h; rw [Bias.payX,dif_neg h]; rfl
variable {p W δ}
open scoped Mew
open Py.Rate
lemma moveFr (t:ℂ){F:Copy n}{D:SO}{X:Aura n}(g:Fray p W δ X D F a):Fray p W δ X D (t • F) (‖t‖*a):=⟨nextHue g.merit t,fun i h=>g.loaf i fun u=> h (by rw [Pi.smul_apply,u,smul_zero])⟩
lemma tray_add {F G:Copy n}{D:SO}{X:Aura n}(g:Fray p W δ X D F a)(t:Fray p W δ X D G b):Fray p W δ X D (F+G) (a+b):=⟨g.merit.plus t.merit,fun i h=>by
 by_cases f:F i=0; · refine t.loaf i fun u=>h (by rw [Pi.add_apply,f,u,zero_add])
 exact g.loaf i f⟩
lemma joint (t:ℂ)(pA:Tint p W δ K a₀ M)(pB:Tint p W δ R a₀ N)(h:‖t‖=1)(pC:PictureT p δ K M)(pD:PictureT p δ R N):Tint p W δ (K+t • R) (a₀+a₀) (M+t • N)∧ PictureT p δ (K+t • R) (M+t • N):=by
 have htW (A B C: FC (Dwell n)): Sault.rind (A*C)+ t • Sault.rind (B*C)= Sault.rind ((A+t • B)*C):=by simp only [add_mul, smul_mul_assoc,Sault.rind,map_add,map_smul]
 constructor
 · refine ⟨add_nonneg pA.dice pB.dice, fun X D Y=>?_, fun X D q Y s v F f=> ?_, fun i Y=> (pA.edge i Y).add (pB.edge i Y|>.scale t), ?_⟩
   · simp only [Pi.add_apply, Pi.smul_apply,pA.start,pB.start,smul_zero,add_zero]
   · simp only [Pi.add_apply,Pi.smul_apply,add_mul]; convert tray_add (pA.plays X D q Y s v F f) (moveFr t (pB.plays X D q Y s v F f)) using 1; rw [h,one_mul]
   intro X Y i m e c F D f; dsimp [D] at f; change (K X D Y F i).val+t • (R X D Y F i).val= _; dsimp only [D]; rw [pA.body X Y i m e c F f,pB.body X Y i m e c F f]; exact htW _ _ _
 constructor; intro X D Y F i; change (K X D Y F i).val+t • (R X D Y F i).val=_; rw [pC.actsF,pD.actsF]; split; swap; · rw [smul_zero,add_zero]
 have hx: coll_T p X D ((M+t • N) Y) i=coll_T p X D (M Y) i+t • coll_T p X D (N Y) i:=by unfold coll_T; split; rfl; rw [smul_zero,add_zero]
 rw [hx]; exact htW _ _ _
open Set
variable {J:Set ℂ}{κ:ℂ→Rinse (Seat n) (Copy n)} {M₀:ℂ→Bag n}
variable (F:ℂ→Vow.Cusp n)(i:Orbit n)(hF:∀ (X:Aura n),∀ D⊆ X.val,DifferentiableOn ℂ (fun z=>F z X D i) J)(hM:∀ (X:Aura n)(V:Orbit n),DifferentiableOn ℂ (fun z=> M₀ z X V) J)
variable (q:∀ z∈J,PictureT p δ (κ z) (M₀ z))
include q hM
lemma musicV(X:Aura n)(D:SO)(Y:Aura n)(P:ℂ→ Copy n)(hx:DifferentiableOn ℂ (fun z=>P z i) J):DifferentiableOn ℂ (fun z=>κ z X D Y (P z) i) J:=by
 apply Mew.lift_holo; by_cases f: Bias.αt Y X D δ
 · let B:= (Pastry.cane (Dwell n)).eval.toContinuousLinearMap; let H(z):= coll_T p X D (M₀ z Y) i; have hv:DifferentiableOn ℂ H J:= by unfold H coll_T; split; exact hM _ _; exact differentiableOn_const _
   exact (B.differentiable.comp_differentiableOn (hv.mul (Mew.sheen.differentiable.comp_differentiableOn hx))).congr fun z k=>by exact ((q z k).actsF ..).trans (if_pos f)
 exact (differentiableOn_const (𝕜:=ℂ) (c:=(0:FC (Dwell n))) (s:=J)).congr fun z t=> (q z t|>.actsF ..).trans (if_neg f)

lemma vocal (X:Aura n):DifferentiableOn ℂ (fun z=>birthL (κ z) X ∅ i) J:= musicV i hM q X ∅ X (fun _=>1) (differentiableOn_const _)
omit hM q
private lemma scale_r {H:ℂ→ Cipher n}(p:DifferentiableOn ℂ H J)(z:ℝ):DifferentiableOn ℂ (fun v=>z • H v) J:=by
 simp_rw [←Complex.coe_smul]; exact p.const_smul (z:ℂ)
private lemma sing_prod {ι:Type*}(A:Finset ι)(F:ι→ℂ→ Cipher n)(h:∀ i∈A,DifferentiableOn ℂ (F i) J):DifferentiableOn ℂ (fun z=>∏ i∈A,F i z) J:=by
 induction A using Finset.induction_on with
 | empty=>simp_rw [Finset.prod_empty]; exact differentiableOn_const _
 | insert i A p ih=>simp_rw [Finset.prod_insert p]; exact (h i (mem_insert_self ..)).mul (ih fun i p=>h i (mem_insert_of_mem p))
local notation "M1" i:max=> Cadre.chip (κ i) (F i)
include hF hM q
lemma syllable (X:Aura n)(D:SO)(pD:D⊆X.val) (j:ℕ) : DifferentiableOn ℂ (fun z=> coeff j ((M1 z) X D) i) J:=by
 induction j using Nat.strong_induction_on generalizing X D with |h j ih=>
    cases j with
    |zero=>simp_rw [Cadre.peg]; exact hF _ _ pD
    |succ j=>
       have hv(z:ℂ): coeff (j+1) ((M1 z) X D)=((j:ℝ)+1)⁻¹ • coeff j (Cadre.stepL (κ z) (M1 z) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [hv,Pi.smul_apply, Cadre.ore,Finset.sum_apply]; refine scale_r ?_ ((j:ℝ)+1)⁻¹; apply DifferentiableOn.fun_sum; intro y _; apply DifferentiableOn.fun_sum; intro G v; apply musicV i hM q X D; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; refine DifferentiableOn.fun_sum fun a y=> sing_prod _ _ fun m w=>?_ ; exact ih (a m) (Nat.lt_succ_of_le (le_trans (single_le_sum (fun i _=>Nat.zero_le (a i)) w) ((mem_finsuppAntidiag.mp y).1.le))) m _ inter_subset_right
lemma syllable_e (X:Aura n)(D:SO)(j:ℕ):DifferentiableOn ℂ (fun z=> coeff j (nutL (κ z) (F z) X D) i) J:=by
 cases j; · simp_rw [show ∀ s:ℂ,(coeff 0 (Cadre.nutL (κ s) (F s) X D)) i=(0:Cipher n) from fun _=> by rw [tick_r]; rfl]; exact differentiableOn_const _
 rename_i j; unfold nutL; simp_rw [sprig,Pi.smul_apply,Cadre.front,Cadre.rill,map_sum,grate, coeff_mk,Finset.sum_apply]; refine scale_r ?_ ((j:ℝ)+1)⁻¹; apply DifferentiableOn.fun_sum; intro y _; apply DifferentiableOn.fun_sum; intro G v; apply musicV i hM q X D; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; exact DifferentiableOn.fun_sum fun y _=> sing_prod _ _ (fun m t=>syllable F i hF hM q m _ inter_subset_right _)

variable {P₀:ℂ→ Aura n→ Support (More n)→ℝ}
local notation "I'" z:max=> P₀ z
variable (hK:∀ i∈J,∀ X:Aura n,∀ D⊆ X.val,Fray p W δ X D (F i X D) (P₀ i X D))(hP:∀ i∈J,Tint p W δ (κ i) a₀ (M₀ i))
variable {S L t μ w s γ α Hb:ℝ}{b': Palot.leaf (Seat n)→ℝ} (Tt:∀ i∈J,Timer (Cadre.chip (cribR a₀) (P₀ i)) a₀ S L μ b' s γ α Hb w 2 a₀)(ht:0<t)(hv:t ≤ L-μ*2)(pW:1 ≤ W)
local notation "dp"=> (2*(Hb*γ+s*t⁻¹*γ*α))
include pW hF hM hK ht hv hP Tt
/-! Uniform summability here using Timer's time-two reserve (cf. equivalent accounts for twice the kernel payment at time one; see VOLUME_ANALYTIC, Lemma matchw, and Pso/Azure `light_M`). -/
lemma growing (X:Aura n)(D:SO)(pD:D⊆X.val)(pJ:IsOpen J):DifferentiableOn ℂ (fun z=> Stax.lamp (P:=p) (F z) (κ z) X D i) J:=by
 let T (z):= Stax.rem_X (P:=p) (F z) (κ z) X D i
 have U:DifferentiableOn ℂ T J:=by
    unfold T rem_X Vow.lasting zenS; split; swap; exact differentiableOn_const _
    next hx=>
      let g:= loom_v 0 0 b' 2 X; let k:= dp; let A:=k/g
      obtain ⟨Y,hp',hx'⟩:=hx; refine Complex.differentiableOn_tsum_of_summable_norm ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)).mul_left A) (syllable_e F i hF hM q X D) pJ fun j z y=>?_
      let Mm:= nutL (cribR a₀) (P₀ z); have hp:= zero_le_one.trans pW; have a':= deck (F z) (P₀ z) (hK z y) _ a₀ (hP z y) hp X D pD j; have hu:= a'.merit.same i (Y,i.2) hx' (fun _ _=>rfl); change ‖coeff j (nutL (κ z) (F z) X D) i‖ ≤ _; rw [hu]; apply le_trans (a'.merit.capF pW (Y,i.2) hp'); apply Cadre.palm_ Mm _ S (Tt z y).slope 0 0 b' k _ X D pD j
      · exact fun o R p=> Cadre.heatR a₀ (P₀ z) (fun Y D t=> ((hK z y Y D t).merit.wage hp)) (hP z y).dice _ _
      exact fun b m=>(Tt z y).worth ht le_rfl (le_trans (zero_add t).le hv) _ (fun _ _ _=>tick_r _ _) (oreL0 _ _) b m
 have w:DifferentiableOn ℂ (fun z=>birthL (κ z) X D i) J:=by
    unfold birthL; split; exact musicV i hM q X ∅ X (fun _=>1) (differentiableOn_const _); exact differentiableOn_const _
 exact ((hF X D pD).add w).add U
end YM.CF.Sour
