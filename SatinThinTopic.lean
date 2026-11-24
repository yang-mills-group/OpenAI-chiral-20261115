import SatinThinFrost
import SatinThinQuality
/-! relative coherence where the sector is formed. Includes across varying layouts. -/
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
open Waxy Mew

structure Topic(n:Side) where
 face: Site n → RegBudget n → ForceBudget n → Prop
 color: ∀ (s:Sweep n),s∈cycleSweep n→∀ x y E V F W, Earlier s x y→face x E F→ face y V W→ passingR n s E (bandSign s • V) ∧ passingF n s F (bandSign s • W)

variable (s:Sweep n)
lemma Eρ_pass (u v:RegBudget n)(t:Eρ s v=u): passingR n s u v:=by
 intro i x; have he:=congrFun (congrFun t i) x; rw [←he]; change _=suit_Y s (suit_Y s⁻¹ _); rw [moon_Y,inv_mul_cancel,toon_Q]; rfl
lemma Fρ_pass (u v: Copy n)(h:∀ x:Orbit n,v (yellA s x)=suit_Y s (u x)): Fρ s v=u:=by
 funext x; change suit_Y s⁻¹ (v (yellA s x))=u x; rw [h,moon_Y,mul_inv_cancel,toon_Q]
lemma Kρ_pass (u v: Cusp n)(t:Kρ s v=u): passingU n s u v:=by
 intro i x p D h; have he:=congrFun (congrFun (congrFun t i) D) x; rw [←he]; change _=suit_Y s (suit_Y s⁻¹ _); rw [moon_Y,inv_mul_cancel,toon_Q]; rfl
lemma passingR.add {u v A B:RegBudget n}(l:passingR n s u v)(t:passingR n s A B) : passingR n s (u+A) (v+B):=fun i x=> (congrArg₂ (·+·) (l i x) (t i x)).trans (map_add ..).symm
lemma passingR.smul {u v:RegBudget n}(l:passingR n s u v)(r:ℝ) : passingR n s (r • u) (r • v):= fun i x=> (congrArg (fun k:Cipher n=>r • k) (l i x)).trans (map_smul (suit_Y s) r _).symm
lemma passingF.add {u v A B:ForceBudget n} (l:passingF n s u v)(t:passingF n s A B) : passingF n s (u+A) (v+B):=fun i x p=> (congrArg₂ (·+·) (l i x p) (t i x p)).trans (map_add ..).symm
lemma passingF.smul {u v:ForceBudget n}(l:passingF n s u v)(r:ℝ) : passingF n s (r • u) (r • v):= fun i x p=> (congrArg (fun k:Cipher n=>r • k) (l i x p)).trans (map_smul (suit_Y s) r _).symm
lemma passingU_n.add {u v A B:Cusp n}(l:passingU_n n s u v) (t: passingU_n n s A B) : passingU_n n s (u+A) (v+B) :=fun i x p D h k =>(congrArg₂ (·+·) (l i x p D h k) (t i x p D h k)).trans (map_add ..).symm
lemma passingU_n.smul {u v:Cusp n}(l:passingU_n n s u v)(r:ℝ) : passingU_n n s (r • u) (r • v):= fun i x p D h g=> (congrArg (fun k:Cipher n=> r • k) (l i x p D h g)).trans (map_smul (suit_Y s) r _).symm
variable {I J:Type*}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]
abbrev realKey (i:I)(r:ℝ):Key I:=update 0 i (r:ℂ)
lemma realKey_mem (i:I)(r:ℝ)(l:|r| ≤1): realKey i r ∈ hill I := fill_I roots i (mem_closedBall_zero_iff.mpr (by rw [Complex.norm_real,Real.norm_eq_abs]; exact l))
abbrev emberTip (v:Key I→ ForceBudget n)(i:I): ForceBudget n:=fun X T=> tipI (fun z=> v z X T) [i]
abbrev opTip (v:Key I→ Pax n)(i:I):Pax n:=fun X T=> tipI (fun z=>v z X T) [i]
abbrev heat_P (P:BudgetPoint)(A:Key I→ Cusp n)(z:Key I): Pax n:= rust_P P (A z)-rust_P P (A 0)
abbrev feeTip (P:BudgetPoint)(A:Key I→ Cusp n)(i:I) : Copy n:= coldE P (opTip (heat_P P A) i)
lemma tip_real {V:Type*}[NormedAddCommGroup V][NormedSpace ℂ V][NormedSpace ℝ V]
 [IsScalarTower ℝ ℂ V][CompleteSpace V](u:Key I→V)(i:I)(h:River u): HasDerivAt (fun x:ℝ=>u (realKey i x)) (tipI u [i]) 0:=by
 let f(t:ℂ):= u (update 0 i t)
 have hx:HasDerivAt f (tipI u [i]) ((0:ℝ):ℂ):=by rw [Complex.ofReal_zero]; exact mitt h roots i
 have hK:=hx.scomp 0 (show HasDerivAt (fun x:ℝ=>(x:ℂ)) 1 (0:ℝ) from Complex.ofRealCLM.hasFDerivAt.hasDerivAt); exact hK.congr_deriv (one_smul ..)
lemma turnAxis (i:I)(j:J)(u:Key I→ Cipher n)(v:Key J→ Cipher n)(h:River u)(k:River v)(c:ℝ)(t:∀ x:ℝ,|x|≤ 1→v (realKey j (x*c))=suit_Y s (u (realKey i x))): c • tipI v [j]=suit_Y s (tipI u [i]):=by
 let f (x:ℝ):ℝ:= x*c; have hv:HasDerivAt f c 0:= by simpa using (hasDerivAt_id' (0:ℝ)).mul_const c
 let a:=fun x:ℝ=> v (realKey j x); let G: Cipher n→L[ℝ] Cipher n:=(suit_Y s).toLinearMap.toContinuousLinearMap; let Y:ℝ→ Cipher n:= G ∘ fun x=> u (realKey i x)
 have he : a ∘ f=ᶠ[𝓝 0] Y:=by
    filter_upwards [ball_mem_nhds (0:ℝ) one_pos] with x hx using t x (abs_le.mpr ((abs_le.mp (by exact (show ‖x‖ ≤ 1 from (mem_ball_zero_iff.mp hx).le))))) -- tune real norm
 have hz: f 0=0:=zero_mul _
 exact (((show HasDerivAt a _ (f 0) from hz.symm ▸ (tip_real v j k)).scomp 0 hv).congr_of_eventuallyEq he.symm).unique (G.hasFDerivAt.comp_hasDerivAt 0 (tip_real u i h)) -- dependent ▸ careful

lemma turnCost (i:I)(j:J)(u:Key I→ Pax n)(v:Key J→ Pax n)(h:∀ i x,River (fun z=> u z i x))(k:∀ i x,River (fun z=> v z i x))(t:∀ x:ℝ,|x|≤1→ passingFee n s (u (realKey i x)) (v (realKey j (x*bandSign s)))) : passingFee n s (opTip u i) (bandSign s • opTip v j) :=fun a z=> turnAxis s i j (fun g=> u g a z) (fun g=> v g (moldA s a) (yellA s z)) (h a z) (k _ _) _ fun x p=>t x p a z
lemma turnG (P:BudgetPoint)(E F:Pax n)(c:ℝ)(p:passingFee n s E (c • F)): Fρ s (c • coldE P F)=coldE P E:=by
 apply Fρ_pass; intro i; change c • (coldE P F (yellA s i))=_; unfold coldE; rw [smul_sum,map_sum]; symm; refine sum_equiv (moldA s) (fun a=> ?_) (fun a _=> ?_)
 · simp only [mem_filter,mem_univ,true_and]; exact (Salt.glowA ..).symm -- tune
 exact (p ..).symm
lemma turnForce (i:I)(j:J)(u:Key I→ForceBudget n)(v:Key J→ForceBudget n)(h:∀ i x,River (fun z=> u z i x))(k:∀ i x,River (fun z=> v z i x))(t:∀ x:ℝ,|x|≤1→ passingF n s (u (realKey i x)) (v (realKey j (x*bandSign s)))) : passingF n s (emberTip u i) (bandSign s • emberTip v j) := fun a z p=> turnAxis s i j (fun g=> u g a z) (fun g=> v g (moveForce s a) (yellA s z)) (h a z) (k _ _) _ fun x l=> t x l a z p
lemma limit_abs (x:ℝ)(p:|x|≤1): |x*bandSign s| ≤1 := by unfold bandSign; rcases tax_cases s.s with h|h<;> rw [h]<;> simpa
end YM.CF.QuadClock
