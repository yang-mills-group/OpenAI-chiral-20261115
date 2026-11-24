import YM.CF.Swell.Beam
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow Py
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
variable {N B m L:Side}
variable {r:ℕ}
variable {I:Type}[Fintype I][LinearOrder I]
variable {P:BudgetPoint}(E':GramM (mid m B))
open Neon Hom Vale Vale.Grace Kea Nova RP RP.Str Spark Wilson Precision Next.Free Gauge Paige Vault Brace Spire Pressure Jade Oise
variable {A:Teller SU.group}{W:ChartRatio SU.group}{Zp:Patch}(D:Grace A Zp W){d e g x b a t u0 K Kt f l α s':ℝ}
variable {X: Grasp D.U B d}{U:Loom (mid m B)}(R: Roof (mid m B) a e r U)(gP:P.threshold ≤ a)(φp:0<e)(hκ:X.roundZ ≤ (mid m B).val)(hp:e ≤ d)
open Larch
variable (V:ArcΦ)(H s ε T₀:ℝ)(Tv:InΦ V)(o:Site (mid m B))(hD:Taxi.DayT P.order T₀)(hT:0≤ T₀) (vP:10 ≤P.B)(Υ:Gala P.power P.order 100 x 3)(uP:1 ≤ radiusB x)(θT:P.threshold=temp x)(pM:20 < (More (mid m B)).val)(hP:3 ≤ (mid m B).val)(hL:1 < L.val)
variable (vH:1 ≤H)(hpV: H^2 * ‖V.2‖ ≤ ε)(hfV: ‖V.1‖ ≤ ε)
include vH hpV hfV hD hT Tv Υ uP θT pM hP vP hL
def seedsY:= (Pi.single (Φrap (mid m B) o 10) (axle_L (P:=P) o V):RegBudget (mid m B))
lemma plantsY: let E:= seedsY (P:=P) V o; Axon L.val o P E H (Yρ P T₀ ε) V∧∀ y:Orbit (mid m B), Rue.FleetS P.threshold y.1→flags P.threshold y.1=∅→ exponentL P E y.1= Hest.boat (muskPΓ (ηact o V) y.1)+hollow (eraΦ P o V y.1):=by -- binder y annotate
 intro EK; let K:= Φrap (mid m B) o 10; let p:=axle_L (P:=P) o V
 let X:=spring_V V.2 o; let U:= scrollY o V.2; let W:=plateZ (node o) P V.1
 have hu:= pose_K X o P 1 _ (beam_l o _ V.2 (Bud_A V Tv)) 100 Υ (by omega) 10 (by omega) uP θT rfl H
 let x':= node o; have he: Lattice.halo 2 {x'}⊆ K.val.2:=Corona.halo_mono (by norm_num) (Subset.refl _); have hh:∀ i j, ‖V.1 i j‖ ≤ ε:= fun i j=> (norm_le_pi_norm ..).trans ((norm_le_pi_norm ..).trans hfV)
 have hv:= Moto.champ P V.1 K (h:=H) hD hT he hh
 let Vt:=κplant P T₀ ε; have hx:p=W+U:=rfl; have ht:PressB P K p H Vt:=by
    refine Hope.hi_p (prop_add _ K hv hu) ?_; unfold Vt κplant; rw [add_comm _ (trotΦ ..)] -- trim nonsense
    let c:=deck_K P.order P.power 10; have hc:0 ≤ c:=by unfold c deck_K Jet.composeCost; positivity
    let k:= stakeH P.order; have hk:0 ≤ k:=by unfold k stakeH flavor γD; have he:= Haro.p0; have hp:= Haro.wheels_p (n:=P.order); positivity
    refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ hc) _; change k*H^2*chipZ P.power ‖V.2‖≤ k*_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hk; rw [show H^2*chipZ P.power ‖V.2‖=chipZ P.power (H^2*‖V.2‖) from by unfold chipZ chal; ring]; unfold chipZ chal; gcongr
 let E:RegBudget (mid m B):= Pi.single K p; change Axon L.val o P E H _ V ∧ ∀ y:Orbit (mid m B), Rue.FleetS P.threshold y.1→flags P.threshold y.1=∅→ exponentL P E y.1= Hest.boat (muskPΓ (ηact o V) y.1)+hollow (eraΦ P o V y.1); have hν:= K.property;  refine ⟨⟨⟨⟨Pi.single K Vt,?_ ,?_ ⟩,fun _ h=>False.elim h⟩, ?_,?_⟩,fun y a t=>?_⟩
 · intro i; by_cases x:i=K; · subst i; simp_rw [E,Pi.single_eq_same]; exact ht
   rw [Pi.single_eq_of_ne x]; unfold E; rw [Pi.single_eq_of_ne x]; exact Vale.rinse ..
 · intro i; rw [sum_eq_single K]; swap; · intro j _ u; split; rw [Pi.single_eq_of_ne u]; simp [BudgetPoint.mass]; rfl
   swap; · simp
   have hκ:= Roots.gradeE _ _ ht (zero_le_one.trans vH); rw [Pi.single_eq_same]; split; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (show P.supportExponent*(coverNumber P.B K.val.2:ℝ) ≤ P.supportExponent from mul_le_of_le_one_right P.exponent_pos.le (by exact_mod_cast (Corona.cover_mono (Corona.halo_mono vP (Subset.refl {node o})) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)))) hκ; exact mul_nonneg (Real.exp_pos ..|>.le) hκ
 · intro i u; exact Pi.single_eq_of_ne (fun h:i=K=>u (h ▸ rfl)) ..
 · intro i t; by_cases u:i=K; swap; · unfold E; rw [Pi.single_eq_of_ne u,if_neg u]; exact ⟨rfl, Pill_0 o P⟩
   subst i; change Taxi.lifeH (E K) 1=0 ∧ pillar o (E K) P= _; unfold E; rw [Pi.single_eq_same,if_pos rfl]; obtain ⟨gΦ,h'⟩:= Moto.suit_l P V.1 K (h:=H) (zero_le_one.trans vH) hD hT he hh pM Tv.1
   have hy:pillar o W P=(V.1,0):=by apply Prod.ext h'; change jetsL _ _=0; rw [show orbitPH (W 1)= _ from hol_l _,pub_eq,map_zero] -- tune hol
   have hf:Taxi.lifeH U=0:=funext fun i=>Moto.bail_m ..
   rw [hx]; refine ⟨?_,?_⟩; · change Pastry.pane _=_; rw [Pi.add_apply]; rw [hull_sum,show Pastry.pane (W 1)=0 from gΦ,show Pastry.pane (U 1)=0 from congrFun hf 1,add_zero]
   have hr:pillar o U P=(0,V.2):=by
      apply Prod.ext; funext i j; unfold Neon.pillar Moto.tooth; rw [hf]; change iteratedFDeriv ℝ 2 (fun _:tangD _=>(0:ℂ)) _ _=0; rw [iteratedFDeriv_const_of_ne (by omega:(2:ℕ)≠0)]; rfl
      change jetsL o (orbitPH (U 1))=_; unfold U scrollY; rw [hail_K,fief_Ψ o V.2 (Bud_A _ Tv).1 hP]
   rw [Pill_F _ _ _ _ _ _ hv hu (zero_le_one.trans vH),hy,hr]; simp
 · unfold exponentL E; rw [sum_eq_single K]; swap; · intro i _ v; rw [Pi.single_eq_of_ne v]; simp [numbE]
   swap; · simp
   rw [Pi.single_eq_same]; unfold numbE; rw [Set.indicator_of_mem (show _ from (show pingS _ K.val.2 _ from Leaf.lush_K y a t _))]; change W y.1+U y.1= boat _+ W y.1; rw [add_comm]; exact congrArg (·+ W y.1) (vision ..).symm
omit vH hpV hfV hD hT Tv Υ uP θT pM hP vP hL
end YM.CF.Swell
