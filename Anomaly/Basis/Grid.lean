import Anomaly.Basis.Brush
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Porticus Tye Bake Neon Pressure
variable {n m N B:Side} {I:Type} [LinearOrder I] [Fintype I] {C:BudgetPoint} {h v u z w s:ℝ} {q k L':ℕ}
local notation "θ" => mid N B
open Prism
lemma unitLoadRaw (L:ℕ) (p:(axleCap k)^3<L) (o:Site (mid N B)) (x:ℂ) (ht:1≤h)(hv:3 ≤C.B)(w:0 ≤ s): Drill C q k L o h s (pozV (node o) C k (x • 1)) 0 (cashPoncho ‖x‖ s k) (cashPoncho ‖x‖ C.supportExponent k) 0:=by
 let Hn:=momHub k C (node o); let V:InkD θ:= fun _=> hollow x; have hp:PressB C Hn V h ‖x‖:=Moto.litho _ _ _ (fun _ _ _=> rfl) (fun _ _=>rfl) measurable_const ‖x‖ (norm_nonneg _) (fun _ _=> Prism.hail le_rfl) -- tune
 have he:pillar o V C=0:=by
    refine Prod.ext ?_ ?_
    · funext i j; unfold pillar Moto.tooth; rw [show Taxi.lifeH V ∘ RG.increment 1=(fun _:tangD θ=> Taxi.lifeH V 1) from rfl, iteratedFDeriv_const_of_ne (by norm_num:(2:ℕ)≠0)]; rfl
    change Hove.jetsL _ (Haro.orbitPH (V 1))=_; rw [show Haro.orbitPH (V 1)=0 from Moto.hol_l _,Moto.pub_eq,map_zero]; rfl
 rw [← he]; apply gain_core (Herb.scalar ..) ht hv w hp _ p; intro i _; change Sault.rind (x • 1)= _; refine Sault.sky (Sault.skit _) ?_ (Sault.tileL _); exact (fineShape (hollow (n:=Dwell θ) x)).allP -- tune names
-- change dilation of weights.Mark.Add etc.
lemma pole_mask {F:Bag n}{G F':Aura n→ℝ} (g:∀ X,Flight C q X h (F X) (G X) (F' X))(S:Sa n)(τ:Ids n)(v:Seat n)
    (u:∀ X:Aura n,F X≠0→S⊆ X.val){Q Q':Aura n→ℝ}(k':∀ X,Flight C q X h (capR C S (F X)) (Q X) (Q' X)): singlePole τ (fun i=>capR C S (F i)) k' v=singlePole τ F g v:=by
 let A:=fun i=>capR C S (F i); funext X V; by_cases p:X.val.1=v; swap; · rw [show singlePole _ _ _ _ X=0 from station _ _ _ (fun (_:Fin 1)i=>k' i) _ _ (0:Fin 1) _ p, show singlePole τ F g v X=0 from station _ _ _ (fun (_:Fin 1)i=>g i) _ _ (0:Fin 1) _ p]
 let L:=lagE X; apply Subtype.ext; rw [pole_value (F:=A) X k' _ _ p,pole_value X g _ _ p]; apply congrArg Sault.rind; unfold coll_T; split; swap; rfl
 rename_i K; let I:=gloss C L ∅ (V,τ); change capR C S (F L) I= F L I; unfold capR; by_cases e:F L=0; · rw [e]; exact congrFun (Set.indicator_zero (FC (Dwell n)) _) I
 have hS:=u L e
 apply Set.indicator_of_mem
 apply grow_b hS
 have ht: I.1∈σX C L ∅:= (Rue.pillar L.val (Rue.open_l C.threshold L.val ∅)).choose_spec.2 V|>.2 K
 simpa only [sdiff_empty] using ht.1
lemma shutter_D {F:Bag (mid N B)}{e f:ℝ}{S: Sa (mid N B)}{o:Site (mid N B)}{Φ:ArcΦ} (H:Drill C q k L' o h s F Φ v e f)(t:S⊆ grooveB k C (node o)) : Drill C q k L' o h s (fun i=>capR C S (F i)) Φ v e f:=by
 obtain ⟨G,A,p,T,v,e⟩:= H.yard.price; refine ⟨H.yard.fresh _ t,fun W Y τ B=>?_⟩; rw [pole_mask p _ _ _ (fun X h=>t.trans (Classical.not_not.mp (fun w=> h (T X w).1))) B]; exact H.stamp _ _ τ p
lemma give_mask (F:Bag n)(i:Sa n)(U:Orbit n): giveB (fun X=> capR C i (F X)) U=(capR C i (giveB F)) U:=by
 unfold capR giveB; rw [Finset.sum_apply]; by_cases v:U∈pingMask C i
 · simp_rw [Set.indicator_of_mem v]; rw [Finset.sum_apply] -- tune
 rw [Set.indicator_of_notMem v]; simp_rw [Set.indicator_of_notMem v]; simp
end YM.CF.Vow.TreasuryFog
