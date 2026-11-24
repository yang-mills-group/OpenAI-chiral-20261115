import YM.SU5.Exchange.Force.Jets
import Anomaly.Apert.Spindle
import SatinThinScroll
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.QuadClock
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax Rill Ione Clock Salt Mew PowerSeries Sour
attribute [local instance] opCStarAlgebra
open scoped Mew
variable {n N K B:Side}
local notation "Ω"=> mid N B
open Vow.TreasuryFog Larch Roots Py Swell Analysis Pressure Oath Moto Neon Hove
variable {q l t:ℕ}{h w μ c d x v f a b:ℝ}
variable (P:GramM (mid N B))(X:GramM (mid K B))(G:Ratio (mid N B) (mid K B))
local notation "Θ"=>mid K B
lemma axonPrice {A:RegBudget (mid N B)}{y:ArcΦ}{i:Site (mid N B)}(H:Axon q i P.p A h f y)(p:HavenL (mid N B) P.p q)(u:1≤h) (v:f≥0) : ‖y.1‖≤ f ∧ ‖y.2‖*h^2 ≤ (2*peka_H P.p.power)*f:=by
  obtain ⟨x,t',s⟩:=H.vest.weight; let j:=Φrap (mid N B) i 10; have hw:= (H.flair j (atRim p i)).2
  rw [if_pos rfl] at hw; rw [←hw]
  have hv:P.p.mass j.val.2 (x j)≤ f:=by
    refine le_trans ?_ (s j.val.1); rw [←Finset.sum_filter]; refine single_le_sum (f:=fun i:Scree.Hub Ω=>P.p.mass i.val.2 (x i)) (s:= univ.filter (fun i:Scree.Hub Ω=>j.val.1=i.val.1)) (fun i _=>?_) (Finset.mem_filter.mpr ⟨mem_univ _,rfl⟩)
    exact mul_nonneg (Real.exp_pos _).le ((Taxi.eraF _ _ (t' _) (zero_le_one.trans u) _ (ping_f P.p _)).grade)
  let hζ:=quest_B i P.p h {j} id A x f (fun i _=>t' i) (fun i h=> by rw [mem_singleton.mp h]; rfl) u (by rw [sum_singleton]; exact hv) {j} (Subset.refl _)
  simpa only [sum_singleton,Neon.pillar] using hζ

variable {I:Type}[Fintype I][LinearOrder I](E:Key I→RegBudget (mid K B))(F:Key I→ForceBudget (mid K B))(p:I→ ArcΦ)(σ:I→Site (mid N B))
    (t₂:Notice (Hove.heel G∘ σ) E F) (aC:∀ z:Key I,(∀ i,‖z i‖≤1)→ IncX primeU (E z) X.p h v ∧ Dark primeU (F z) X.p h c)
local notation "Y"=> Key I
local notation "Aφ" z:max=> X.F + dampE E z
local notation "Fφ" z:max=> X.K + dampE F z

include t₂
lemma covTips : (∀ i,νTip (fun z:Key I=>Aφ z) i=νTip E i)∧ ∀ i,emberTip (fun z:Key I=> Fφ z) i= emberTip F i:=by
 constructor
 · intro i; funext x y; refine (lace_C [i] (f:=fun z=> (Aφ z) x y) (g:=fun z=>X.F x y+ E z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>E z x y) (t₂.varE _ _)) [i]).trans ?_); · exact fun z v=> by dsimp only; rw [show dampE E z=E z from if_pos v]; rfl
   rw [proper,zero_add]
 intro i; funext x y; refine (lace_C [i] (f:=fun z=> (Fφ z) x y) (g:=fun z=>X.K x y+ F z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>F z x y) (t₂.varF _ _)) [i]).trans ?_); · exact fun z v=> by dsimp only; rw [show dampE F z= F z from if_pos v]; rfl
 rw [proper,zero_add]
include aC

lemma passCotton (L:Side)(z:HavenL (mid K B) X.p L.val)
    (u:1≤ h)(D:Arc_r X h μ μ μ)(η: X.slip=0)(p₀:μ≤ 1)
    (g: μ≤d)(t₀: μ+v≤d)(t₁:μ+c≤d)(H:∀ i,Axon L.val (Hove.heel G (σ i)) X.p (νTip E i) h b (p i))
    (r0: 0≤ b)(r:b≤w)(tZ:Real.exp 1 * b ≤ w)(sZ:Real.exp 1 *((2*peka_H X.p.power)*b)≤w)(t':GapN σ P.p.B L.val q) :
    OrbitPulse G P X h d w L σ (fun z=> Aφ z) (fun z=> Fφ z) p (fun _=> b) q :=by
 obtain ⟨kx,vx⟩:=covTips X G E F σ t₂ -- implicit P
 let A'(z:Y):=Aφ z; let V'(z:Y):= Fφ z; have v0:A' 0=X.F ∧ V' 0=X.K:=by unfold A' V'; rw [show dampE E 0=E 0 from if_pos roots,show dampE F 0= F 0 from if_pos roots,t₂.roll.1,t₂.roll.2]; simp
 refine ⟨?_,t',?_,fun j=>(kx j).symm ▸ H j,?_,?_⟩
 · constructor
   · exact ⟨v0.1,η.symm,v0.2⟩
   · intro i; refine ⟨fun c e b t x=>?_,fun c a b t x=>rfl,fun x=> ⟨(dub_V (zeroR (X.F i x)) (river_all (fun z=>E z i x) (t₂.varE _ _))).cong (fun c h=>?_), zeroR _⟩⟩
     · change (Aφ c) _=(Aφ b) _; rw [show dampE E c= _ from (show dampE E c = E c from if_pos e),show dampE E b= E b from if_pos t,Pi.add_apply,Pi.add_apply]; exact congrArg (X.F i + ·) (t₂.col i c b x)
     change (Aφ c) i x=_; rw [show dampE E c= E c from if_pos h]; rfl
   · intro i; refine ⟨fun c e b t x=>?_,fun x=> (dub_V (zeroR (X.K i x)) (river_all (fun z=> F z i x) (t₂.varF _ _))).cong (fun c h=>?_)⟩
     · change (Fφ c) _=(Fφ b) _; rw [show dampE F c= F c from if_pos e,show dampE F b= F b from if_pos t,Pi.add_apply,Pi.add_apply]; exact congrArg (X.K i + ·) (t₂.joinF i c b x)
     change (Fφ c) i x=_; rw [show dampE F c= F c from if_pos h]; rfl
   intro z; constructor
   · by_cases t:z∈hill I; · change IncX primeU (Aφ z) X.p h d; rw [show dampE E z=E z from if_pos t]; exact Provides.liftE h X _ _ (Larch.add_v _ _ _ D.1 (aC z (hill_i.mp t)).1) t₀
     change IncX _ (Aφ z) _ _ _; rw [show dampE E z=0 from if_neg t,add_zero]; exact Provides.liftE h X _ _ D.1 g
   · change IncX primeU 0 X.p h d; rw [←η]; exact Provides.liftE h X _ _ D.2 g
   by_cases t:z∈hill I; · change Dark primeU (Fφ z) X.p h d; rw [show dampE F z= F z from if_pos t]; exact Provides.liftQ h X _ _ (union_F _ D.3 (aC z (hill_i.mp t)).2) t₁
   change Dark _ (Fφ z) _ _ _; rw [show dampE F z=0 from if_neg t,add_zero]; exact Provides.liftQ h X _ _ D.3 g
 · intro i
   let ρ:=Hove.heel G (σ i)
   have t:= (κLife ρ X (Provides.liftE _ X _ _ D.1 p₀) u).2 -- abi
   let V:= nun_ω X.F ρ; have hp:=axonPrice X (H i) z u r0
   let U:(ℝ):= ‖(p i).2‖; have Hq(r':ℝ)(a:0≤r')(d:r'≤U): ‖V‖*r'*h^2 ≤ w:=by
      rw [mul_assoc]; exact (mul_le_mul t ((mul_le_mul_of_nonneg_right d (sq_nonneg h)).trans hp.2) (mul_nonneg a (sq_nonneg h)) (Real.exp_pos _).le).trans sZ
   exact ⟨⟨r0,r⟩,(mul_le_mul t hp.1 (norm_nonneg _) (Real.exp_pos _).le).trans tZ, Hq _ (norm_nonneg _) (le_max_left ..), Hq _ (norm_nonneg _) (le_max_right ..)⟩
 · intro i x u; change X.F+dampE E _=A' 0+_ • νTip _ i; rw [show dampE E (realKey i x)= _ from (show dampE E _=E _ from if_pos (realKey_mem i x u)),kx i,v0.1, (t₂.head i (x:ℂ)).1, Complex.coe_smul]
 intro i x u; change X.K+dampE F _=V' 0+_ • emberTip _ i; rw [show dampE F (realKey i x)= _ from (show dampE F _=F _ from if_pos (realKey_mem i x u)),vx i,v0.2,(t₂.head i (x:ℂ)).2,Complex.coe_smul]
end YM.CF.QuadClock
