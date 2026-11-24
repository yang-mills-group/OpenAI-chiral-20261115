import YM.CF.Moto.Peke
import YM.CF.Chaff.Hub
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione Beau
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Hope Taxi
local notation "Rp"=> Rink -- tune junk
variable {X₀:Scree.Hub n}{F G:InkD n}
local notation "X"=> X₀.val.2
local notation "o"=> X₀.val.1
local notation "Ew"=> (increment (1:Pane n))
local notation "θ"=> P.threshold
local notation "Hq"=> Haro.orbitPH
variable(q:PressB P X₀ F h a)(u:PressB P X₀ G h b)(v:0 ≤ h)
local notation "Ω"=> NormedSpace.exp
local notation "PZ"=> Pastry.pane
local notation "gϵ" f:max=> lifeH f ∘ increment (1:Pane n)
local notation "gη" a:max=> tooth o P a
include q v
lemma hutC : fderiv ℝ (gϵ F) 0=0:=by
 let f:=gϵ F; have hp:ContDiffAt ℝ (P.order: WithTop ℕ∞) f 0:=(eraF _ _ q v _ (ping_f P X)).paid -- tune type
 have he:DifferentiableAt ℝ f 0:= hp.differentiableAt (by exact_mod_cast (show P.order≠0 by have ht:= P.order_ge; omega))
 apply ContinuousLinearMap.ext; intro i
 have hz(L:ℂ→L[ℝ]ℝ): L (fderiv ℝ f 0 i)=0:=by
    have e:=L.iteratedFDeriv_comp_left hp (i:=1) (Nat.cast_le.mpr ((by decide:1≤6).trans P.order_ge)); let Q:=cashR F X₀ q v L ‖L‖ le_rfl; have hv:fderiv ℝ (L ∘ f) 0= L ∘L fderiv ℝ f 0:=by rw [fderiv_comp 0 L.differentiableAt he,L.fderiv] -- tune
    rw [show L (fderiv ℝ f 0 i) = fderiv ℝ (L ∘ f) 0 i from (by rw [hv]; rfl), show fderiv ℝ (L∘f) 0=0 from flat_critical Thera.yet_one Q.regular]; rfl
 exact Complex.ext (hz Complex.reCLM) (hz Complex.imCLM) -- tune
lemma heatP: ContDiffAt ℝ ((↑(2:ℕ): WithTop ℕ∞)) (gϵ F) 0:= (eraF _ _ q v 1 (ping_f P _)).paid.of_le (Nat.cast_le.mpr ((by norm_num: 2≤6).trans P.order_ge))
omit q v
lemma θn' (Xᵤ:ℂ) (p:‖Xᵤ‖≤1) (s:Complex.exp Xᵤ=1): Xᵤ=0:=by
 obtain ⟨n,h⟩:=Complex.exp_eq_one_iff.mp s; by_cases g:n=0; · rw [h,g]; simp
 have hz:1 ≤ ‖(n:ℂ)‖:=by rw [Complex.norm_intCast]; exact_mod_cast (show 1≤|n| from (by have h:0 < |n| :=abs_pos.mpr g; omega))
 exfalso; rw [h,norm_mul,norm_mul,norm_mul] at p; have hv:=Real.pi_gt_three; have he:0<(Real.pi):=by linarith
 norm_num [abs_of_nonneg he.le] at p hz; nlinarith [mul_le_mul_of_nonneg_right hz he.le]
section
variable {E T:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {f g:E→ℂ}{y:E}(i j:E)
lemma terse(p:ContDiffAt ℝ 2 f y)(u:fderiv ℝ f y=0)(v:f y=0) : iteratedFDeriv ℝ 2 (Complex.exp∘f) y ![i,j]= iteratedFDeriv ℝ 2 f y ![i,j]:=by
 rw [Tale.audit_2 Complex.exp _ _ _ Complex.contDiff_exp.contDiffAt p, v, u, show fderiv ℝ Complex.exp 0=ContinuousLinearMap.id ℝ ℂ from (by rw [Complex.exp_eq_exp_ℂ]; exact hasFDerivAt_exp_zero.fderiv)]
 simp [iteratedFDeriv_two_apply]
lemma lyfe(p:ContDiffAt ℝ 2 f y)(u:ContDiffAt ℝ 2 g y)(hv:fderiv ℝ f y=0)(x:f y=0): iteratedFDeriv ℝ 2 (f*g) y ![i,j]=g y* iteratedFDeriv ℝ 2 f y ![i,j]:=by
 let F:=f*g; let W(h:E→L[ℝ]ℂ):= h j; let Xz(v:E):=W (fderiv ℝ F v); let Q: (E→L[ℝ]ℂ)→L[ℝ]ℂ:= ContinuousLinearMap.apply ℝ ℂ j
 let G(v):= f v* fderiv ℝ g v j; let Y(v):= g v* fderiv ℝ f v j
 have he: Xz=ᶠ[𝓝 y] G+ Y:=by filter_upwards [p.eventually (by simp),u.eventually (by simp)] with v p q; unfold Xz W F; rw [fderiv_mul (p.differentiableAt (by simp)) (q.differentiableAt (by simp))]; simp [G,Y] -- syntax
 have hf:=(p.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num); have hh:=(u.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num); have hz:= ((p.mul u).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num);
 have hp:=((p.differentiableAt (by simp)).hasFDerivAt.mul (Q.hasFDerivAt.comp y hh.hasFDerivAt)); have hu:=((u.differentiableAt (by simp)).hasFDerivAt.mul (Q.hasFDerivAt.comp y hf.hasFDerivAt)); have hv':fderiv ℝ Xz y=Q ∘L fderiv ℝ (fderiv ℝ F) y:= (Q.hasFDerivAt.comp y hz.hasFDerivAt).fderiv
 rw [he.fderiv_eq,show fderiv ℝ (G+Y) y=_ from (hp.add hu).fderiv] at hv'; have h:= (DFunLike.congr_fun hv' i).symm
 simp_rw [iteratedFDeriv_two_apply]; refine h.trans ?_; rw [x,hv]; simp [Q,hv]
end
include q v
lemma true_K (v':1 ≤ h)(p:a ≤ 1)(hf:∀ U:Pane n,pingS θ X U→ exp (F U)-1=G U)(p':lifeH G 1=0):lifeH F 1=0∧ gη F=gη G∧ Hq (F 1)=Hq (G 1):=by
 let f:=gϵ F; let g:=gϵ G
 have hs(U:Pane n)(p:pingS θ X U): Complex.exp (lifeH F U)=lifeH G U+1:=by
    unfold lifeH; rw [← Pastry.paneExp,←hf U p]; change _=panHom _ (_-1)+1; rw [map_sub,map_one,sub_add_cancel]; rfl
 have hz:=hs _ (ping_f P X); rw [p',zero_add] at hz; let D:=lifeH F 1; have hx:‖D‖≤1:=by
    have he:=(eraF _ _ q v 1 (ping_f P X)).token 0 (by omega) 0 (fun i=> Fin.elim0 i); rw [iteratedFDeriv_zero_apply,Function.comp_apply,AnalyticBridge.VerifiedReset.at_zero] at he; exact he.trans p
 have ht:D=0:= θn' D hx hz
 have hg:ContDiffAt ℝ (↑(2:ℕ): WithTop ℕ∞) f 0:= heatP q v; have hu: f 0=0:=by unfold f; rw [Function.comp_apply,AnalyticBridge.VerifiedReset.at_zero]; exact ht
 have hX:Complex.exp ∘ f-(fun _:tangD n=>1)=ᶠ[𝓝 0] g:=by filter_upwards [Chaff.wind_p (1:Pane n) (ContinuousLinearMap.id ℝ (tangD n)) (ping_f P X)] with i p; change Complex.exp (lifeH F _)-1=_; rw [hs (increment 1 i) p]; unfold g; rw [add_sub_cancel_right]; rfl
 refine ⟨ht,funext (fun i=>funext fun j=>?_),?_ ⟩
 · let A:= Tale.clipT P o i; let B:=Tale.clipT P o j; change iteratedFDeriv ℝ 2 f 0 ![A,B]=iteratedFDeriv ℝ 2 g 0 _; rw [← (hX.iteratedFDeriv ℝ 2).self_of_nhds, iteratedFDeriv_sub_apply (Complex.contDiff_exp.contDiffAt.comp _ hg) contDiffAt_const]; change _=iteratedFDeriv ℝ 2 _ _ _- iteratedFDeriv ℝ 2 (fun _:tangD n=>(1:ℂ)) 0 _; rw [terse A B (by simpa using hg) (hutC q v) hu,iteratedFDeriv_const_of_ne (by decide:(2:ℕ)≠0),Pi.zero_apply,ContinuousMultilinearMap.zero_apply,sub_zero] -- lemmas
 exact ((peak_l _ ht).symm.trans (congrArg Hq (hf _ (ping_f P X))))
end YM.CF.Moto
