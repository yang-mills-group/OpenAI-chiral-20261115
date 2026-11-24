import SatinThinScript
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
local notation "TF"=> mid P B
local notation "Tc"=>mid N B
variable (U:Solid G X.p)(F:Topic (mid P B))(o:Site (mid N B))
variable (σ:ℝ → Cusp (mid N B))
local notation "ST"=> Sweep Tc
-- Ask about current. Single-key only (not returning Ψ yet); u,A not properties of entry here, can select repr and empty-case.
variable (q1:Odd G.count.val)(a1:∀ s∈cycleSweep (mid P B), passingR (mid P B) s Y.F Y.F)(b1:∀ s∈cycleSweep (mid P B), passingF (mid P B) s Y.K Y.K)
variable (KΦ:Cusp (mid N B))(kZ:ZealQ KΦ)(K': Site (mid N B)→ Cusp (mid N B))(D: Site (mid N B)→ RegBudget (mid N B))(uK:Bent Kρ K') (uD:Bent Eρ D)
local notation "Pe"=> X.p
structure Thermograph (Fv:ForceBudget (mid N B)): Prop where
 cost : Tidecard G X Y U F o σ
 speaks : ∀ i:Force (mid N B),∀ V:Orbit (mid N B),Function.Injective (priorP V.2)→HasDerivAt (fun t:ℝ=>rust_L X.p (σ t) (KΦ+t • K' o) i V) (Fv i V) 0
include uK uD kZ q1 a1 b1
noncomputable def princess : Topic Tc where
 face x E Fv:=(E=D x ∧ ∃ σ, Thermograph G X Y U F x σ KΦ K' Fv)
 color:=by
    rintro s p x y _ _ Fu Fv h ⟨rfl,w,t⟩ ⟨rfl,u,z⟩
    have g:=uD s p x y h; refine ⟨Eρ_pass s _ _ (by rw [map_smul,g,smul_smul,tax_sq,one_smul]),?_⟩
    intro i v hx; let L:= (suit_Y s).toLinearMap.toContinuousLinearMap; let M:=bandSign s; let a(r:ℝ):=r*M; have e:HasDerivAt a M 0:=by simpa using (hasDerivAt_id' (0:ℝ)).mul_const M
    let f:=fun r:ℝ=> rust_L X.p (w r) (KΦ+r • K' x) i v; let g:=fun r:ℝ=> rust_L X.p (u r) (KΦ+r • K' y) (moveForce s i) (yellA s v)
    have he:a 0=0:=zero_mul _; have hw: g ∘ a =ᶠ[𝓝 0] L ∘ f:=by
       filter_upwards [ball_mem_nhds (0:ℝ) one_pos] with t' k; apply (readCost G X Y U F x w p t.cost y u z.cost q1 a1 b1 h t' (mem_ball_zero_iff.mp k).le).lamp _ _ _ _ v hx
       unfold a; rw [mul_smul]; apply passingU_n.add _ (fun i x p X v l=> kZ _ x p i X v l); apply passingU_n.smul; refine no_pr _ _ _ _ (Kρ_pass _ _ _ ?_); rw [map_smul,uK s p x y h,smul_smul,tax_sq,one_smul]
    let Yv:=yellA s v; have hp:Injective (priorP (Yv).2):=by
       intro i j h; apply (boxA s).injective; exact hx h -- prior of bun tusk?
    exact (((show HasDerivAt g _ (a 0) from he.symm ▸ (z.speaks _ _ hp)).scomp 0 e).congr_of_eventuallyEq hw.symm).unique (L.hasFDerivAt.comp_hasDerivAt 0 (t.speaks i v hx))

omit kZ uK uD q1 a1 b1
lemma stack_axis (f:J→Cusp (mid N B))(t:ℝ)(i:J): Φstack f (realKey i t) = t • f i:=by
 unfold Φstack; rw [sum_eq_single i]; unfold realKey; rw [update_self,Complex.coe_smul]; intro j _ h; unfold realKey; rw [update_of_ne h]; exact zero_smul _ _; simp

variable (J0:ℕ)(Ca:ℝ→ℝ→ℝ)(T0:Counsel V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp U KΦ Ca J0)
variable (κ:ℝ)(vκ:∀ x: Site (mid P B), nun_ω Y.F x=κ)(hs:0≤h)(v:HavenL (mid N B) X.p l.L.val)
include T0 v q1 a1 b1 vκ hs
lemma wreath_C : ∃ v:TopicScheme (mid P B) (mid N B),∀ {J:Type} [LinearOrder J][Fintype J] (r:J→Site (mid N B))(E0:Key J→ RegBudget (mid P B))(Y0: Key J→ ForceBudget (mid P B))(T_:J→ Topic (mid P B))(u A:J→ℝ), Tripulse G X Y h b g l.L r E0 Y0 T_ u A J0 →∃ (R':Key J→RegBudget (mid N B))(Kν:Key J→ ForceBudget (mid N B)), Cause_P V P_ G S G₀ G₁ X Y E0 0 Y0 Xp q d h Vp Vf r A (PointSk ∘ u) R' Kν (fun i=>PointSk (rated v (T_ i) (u i) (A i))) 0 T (duty_Q X.p.order X.p.power*W) C BQ Rt Zt κp ∧∀ i,(surname v (T_ i) (u i) (A i)).face (r i) (νTip R' i) (emberTip Kν i):=by
 choose u' e' k' R₁ R₂ R₃ using fun F μ A=> sell_all G X Y h T W C BQ Rt Zt U F Ca μ A q1 a1 b1 κ vκ hs v
 let f(F:Topic TF)(μ A):= princess G X Y U F q1 a1 b1 KΦ T0.light (k' F μ A) (e' F μ A) (R₂ F μ A) (R₁ F μ A)
 let ψ:TopicScheme TF Tc := fun F μ A=> (u' F μ A,f F μ A); refine ⟨ψ,?_⟩
 intro J _ _ r E0 Y0 T_ u A Q; obtain ⟨Fv,v',hξ,uK,p⟩:= T0.heat r E0 Y0 T_ u A Q
 let F(b):=T_ b; let Eᵪ(i:J):=e' (F i) (u i) (A i) (r i); let Rᵪ(i:J):= k' (F i) (u i) (A i) (r i); let Wᵪ(i:J):=u' (F i) (u i) (A i)
 have ht(i:J): Tidecard G X Y U (F i) (r i) (Fv ∘ realKey i):=by
    refine ⟨νTip E0 i,emberTip Y0 i,Q.faces i,fun t k=>?_⟩; rw [←Q.buy.rail.1,←Q.buy.rail.2.2,←Q.north i t k,←Q.south i t k]; exact v' _ (realKey_mem _ _ k)
 obtain ⟨H,K,T⟩:= p Eᵪ Rᵪ Wᵪ (fun i=> by
    let τ:=Fv ∘ realKey i; let A0:=opTip (heat_P X.p Fv) i
    have hg:=R₃ (F i) (u i) (A i) (r i) τ A0 ⟨ht i,tip_now Fv X.p hξ i,uK i⟩; exact hg)
 let Kν(k):= rust_L X.p (Fv k) (KΦ+Φstack Rᵪ k); refine ⟨H,Kν,K,fun i=>?_⟩
 refine ⟨T i,Fv ∘ realKey i,ht i,?_ ⟩
 intro Z x p; let f(t:Mew.Key J):=Kν t Z x; have hv:= tip_real f i ((K.tape Z).2 x); exact hv.congr_of_eventuallyEq (Eventually.of_forall fun t'=>congrArg (fun V:Cusp (mid N B)=> rust_L X.p (Fv _) (KΦ+V) Z x) (stack_axis Rᵪ t' i).symm)
end YM.CF.QuadClock
