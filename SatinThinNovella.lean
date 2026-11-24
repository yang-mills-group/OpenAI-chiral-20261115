import SatinThinRegister
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
structure Tidecard : Prop where
 bill:∃ E1 K1,F.face (Hove.heel G o) E1 K1∧∀ t:ℝ, |t|≤1→U.source (Y.F+t • E1) (Y.K+t • K1) (σ t)
-- critical `Earlier` torus. hue only along axis.
variable {φ:Sweep (mid N B)}(p:φ∈cycleSweep (mid N B))
variable(t:Tidecard (G:=G) X Y U F o σ)
variable (ω₀:Site (mid N B))(τ:ℝ → Cusp (mid N B))(tt:Tidecard (G:=G) X Y U F ω₀ τ)
variable (q1:Odd G.count.val)(a1:∀ s∈cycleSweep (mid P B), passingR (mid P B) s Y.F Y.F)(b1:∀ s∈cycleSweep (mid P B), passingF (mid P B) s Y.K Y.K)(e1:Earlier φ o ω₀)
-- G explicit binder in Tidecard? dependencies through V? print
#check Tidecard
include q1 a1 b1 e1 p t tt
lemma readCost (k:ℝ)(hk:|k|≤1): MirrorBill Tc X.p φ (σ k) (τ (k*bandSign φ)):=by
 obtain ⟨E0,K0,g0,f0⟩:=t.bill; obtain ⟨E1,K1,g1,f1⟩:= tt.bill
 let z:=reSweep G φ; let r:= cycle_re p G; obtain ⟨u,v⟩:= F.color z r _ _ _ _ _ _ (Earlier.goes G q1 e1) g0 g1; refine U.stays φ p _ _ _ _ _ _ (f0 k hk) (f1 _ (limit_abs φ k hk)) ?_ ?_ <;> rw [mul_smul]
 · exact (a1 _ r).add z (u.smul z k)
 exact (b1 _ r).add z (v.smul z k)
omit t tt -- prep derivative
abbrev shortDose (P:BudgetPoint)(σ:ℝ → Cusp n)(x:ℝ):=rust_P P (σ x)-rust_P P (σ 0)
def adorns (p:BudgetPoint)(σ:ℝ → Cusp n)(W:Pax n):Prop:=∀ i:Aura n,∀ U:Orbit n,HasDerivAt (fun x:ℝ=>shortDose p σ x i U) (W i U) 0
omit q1 a1 b1 e1 p
lemma tip_now (Fv:Key J→Cusp n)(P:BudgetPoint)(h:∀ i v,River (fun k=>heat_P P Fv k i v))(i:J): adorns P (Fv ∘ realKey i) (opTip (heat_P P Fv) i):=by
 intro x u; have hx:=tip_real _ i (h x u); refine hx.congr_of_eventuallyEq (Eventually.of_forall fun z=>?_); simp only [shortDose,Function.comp_apply,heat_P,realKey,Complex.ofReal_zero,Mew.centre] -- comp
variable (K0:Pax (mid N B))(q0: adorns X.p σ K0)(K1:Pax (mid N B))(u1:adorns X.p τ K1)
include q1 a1 b1 e1 t tt u1 p q0
lemma dormant : Fρ φ (bandSign φ • coldE X.p K1) = coldE X.p K0:=by
 apply turnG φ; intro i U; let Y:= bandSign φ; let z(r:ℝ):=r*Y; let C: Cipher (mid N B)→L[ℝ]Cipher (mid N B):=(suit_Y φ).toLinearMap.toContinuousLinearMap; have he: HasDerivAt z Y 0:=by simpa using (hasDerivAt_id' (0:ℝ)).mul_const Y
 let f:=fun x=> shortDose X.p σ x i U; let a:=(moldA φ i); let g:=fun x=> shortDose X.p τ x a (yellA φ U)
 have hu: g ∘ z=ᶠ[𝓝 0] C ∘ f:=by
    filter_upwards [ball_mem_nhds (0:ℝ) one_pos] with x hx
    have hh:= readCost G X ‹GramM (mid P B)› ‹Solid G X.p› F o σ p t ω₀ τ tt q1 a1 b1 e1 -- notation U shadow actual X? U shadow
    unfold f g z; simp only [Function.comp_apply,shortDose,Pi.sub_apply,map_sub]
    refine congrArg₂ (· - ·) ((hh x (mem_ball_zero_iff.mp hx).le).wax i U) ?_; have ht:=(hh 0 (by norm_num)).wax i U; rwa [zero_mul] at ht
 change Y • _ = C _; have hk:z 0=0:=zero_mul _; exact (((show HasDerivAt g (K1 a (yellA φ U)) (z 0) from hk.symm ▸ u1 a (yellA φ U)).scomp 0 he).congr_of_eventuallyEq hu.symm).unique (C.hasFDerivAt.comp_hasDerivAt 0 (q0 i U))
end YM.CF.QuadClock
