import GaugeFieldConstruction.Loomcost
import YM.Extra.ITERATION_NO_LOSS.Geometry
import GaugeFieldConstruction.Wand
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
namespace Housing
open Work.F03
open Haro Taxi
open scoped ENNReal
variable {S:Support (More n)}
variable {E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
variable {b b' q u w v t:ℝ}{k:ℕ}{Y Z:Pane n→ E}
structure Haw (p: BudgetPoint)(o:Skye.Seat n)(X:Support (More n))(Y:Pane n→ E)(t:ℝ): Prop where
 live: Lattice.LocalOn X Y
 swift: Continuous Y
 rends(U:Pane n) : pingS p.threshold X U→ Signs p o (Y ∘ increment U) t
-- Kernel cost with gap Γ p τ.
lemma shores {u:Pane n}(L:Push.Uniform.Allows p.order (fun x:Directions SU.group (More n)=> Y (increment u x)) 0 b)(v:p.power ≤ 3)
  (m: p.order≤ k)(s:S ⊆ Pax o)(f:Lattice.LocalOn S Y) (j:0≤ w)(t:‖Y u‖≤ w*p.threshold): Signs p o (Y∘ increment u) (max w (b*((25:ℝ)^3)^k) * p.threshold):=by
 let B:=p.threshold; have hp:=p.threshold_pos; let Z:ℝ:=(25:ℝ)^3; let K:=p.order
 have he:=fun (x:tangD n) (h:p.dirBound o x) (e:Edge (Site (More n))) (l:fitsSpan S e)=>show ‖x e‖ ≤ p.threshold*Z from (h e).trans (mul_le_mul_of_nonneg_left (by
    have he: (1:ℝ)+(separation e.1 o:ℝ) ≤ 25 :=by
       obtain ⟨i,p,t⟩:= halo_spec.mp (s l.1); rw [mem_singleton.mp p, separation_comm] at t -- tune
       have hz:(separation e.1 o:ℝ)≤24:=by exact_mod_cast t
       linarith only [hz]
    unfold Z; exact (pow_le_pow_left₀ (by positivity) he _).trans (pow_le_pow_right₀ (by norm_num) v)) hp.le)
 refine ⟨mul_nonneg (j.trans (le_max_left ..)) hp.le,L.analytic.of_le le_top,fun i h y p'=>?_⟩
 let C:= Y ∘ increment u
 rcases i with _|i; · simpa [iteratedFDeriv_zero_apply, Function.comp_apply,at_zero] using (t.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hp.le)) -- reverse goal tactic tune
 apply (hatchC L f h y (fun i=>B*Z) (fun _=>by unfold B Z; positivity) (fun i e p=> he _ (p' i) e p)).trans; rw [Finset.prod_const,card_univ,Fintype.card_fin,mul_pow];
 have hz: B^(i+1)≤B:= (pow_le_pow_of_le_one hp.le p.threshold_le (show 1≤ i+1 from (by omega))).trans_eq (pow_one _)
 change b*_ ≤ max w (b*Z^_) * B; rw [mul_comm _ (Z^_),←mul_assoc]
 exact mul_le_mul ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by unfold Z; norm_num) (h.trans m)) L.nonneg).trans (le_max_right ..)) hz (pow_nonneg hp.le _) (j.trans (le_max_left ..))
lemma trophy {u:Pane n}(L:Push.Uniform.Allows p.order (fun x:Directions SU.group (More n)=> Y (increment u x)) 0 b)(v:p.power≤3)
  (m: p.order ≤ k)(s:S⊆Pax o)(f:Lattice.LocalOn S Y) : Signs p o (Y ∘ increment u) (b*((25:ℝ)^3)^k):=by
 -- use shores with w = scaled b, then max
 have ht:= p.threshold_pos
 have hp:=shores L v m s f (w:=b/p.threshold) (by have h:=L.nonneg; positivity) (by rw [div_mul_cancel₀ _ ht.ne']; nth_rw 1 [←at_zero u]; exact L.value); refine Prism.high hp ?_; rw [max_mul_of_nonneg _ _ ht.le]; refine max_le ?_ ?_; · rw [div_mul_cancel₀ _ ht.ne']; exact le_mul_of_one_le_right L.nonneg (one_le_pow₀ (by norm_num))
 exact mul_le_of_le_one_right (by have f:=L.nonneg; positivity) p.threshold_le
lemma hotB(C:E)(A:ℝ)(u:‖C‖≤A): Haw p o S (fun _=> C) A:= ⟨fun _ _ _=>rfl,continuous_const,fun i _=>Prism.hail u⟩
lemma weld (h:Haw p o S Y b)(v:Haw p o S Z u):Haw p o S (fun i=>Y i+Z i) (b+u):= ⟨fun i j x=> congrArg₂ _ (h.live i j x) (v.live i j x),h.swift.add v.swift,fun i t=>Prism.tack (h.rends i t) (v.rends i t)⟩
lemma svelte (h:Haw p o S Y b)(x:E→L[ℝ] F): Haw p o S (fun i=>x (Y i)) (‖x‖*b):=⟨fun i j p=>congrArg x (h.live i j p),x.continuous.comp h.swift,fun i t=> Prism.skills (Jet.Allows.linear x (Prism.skin (h.rends i t)) le_rfl)⟩
lemma gum (h:Haw p o S Y b)(g:b≤ v): Haw p o S Y v:=⟨h.live,h.swift,fun i t=>Prism.high (h.rends i t) g⟩
lemma sprue (h:Haw p o S Y b)(i:ℝ): Haw p o S (fun x=>i • Y x) (|i| * b):=⟨fun x y q=>congrArg _ (h.live x y q), continuous_const.smul h.swift, fun j t=>Prism.skills (Jet.Allows.smul (Prism.skin (h.rends j t)) _)⟩
lemma witch {Z:Pane n→ F}(L:E→L[ℝ] F→L[ℝ] G)(h:Haw p o S Y b)(e:Haw p o S Z t): Haw p o S (fun i=> L (Y i) (Z i)) (2^p.order * ‖L‖ * b * t):=⟨fun x y p=> congrArg₂ (fun u v=>L u v) (h.live x y p) (e.live x y p), (L.continuous.comp h.swift).clm_apply e.swift,fun i t=> Prism.skills (Jet.Allows.bilinear L (Prism.skin (h.rends i t)) (Prism.skin (e.rends i t)) le_rfl)⟩ -- tune t
lemma pets {I:Type*}(R: Finset I)(Y:I→ Pane n→ E)(C:I→ℝ)(h:∀ i∈R,Haw p o S (Y i) (C i)): Haw p o S (fun x=>∑ i∈R, Y i x) (∑ i∈R,C i):=by
 classical
 induction R using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact hotB _ 0 (norm_zero.le)
 | @insert i R k ih=> simp_rw [sum_insert k]; exact weld (h i (mem_insert_self ..)) (ih fun j q=>h j (mem_insert_of_mem q))
open Work.F03
lemma pearl (v:ℕ): ∃ C:ℝ,1≤C ∧ ∀ (n:Side)(z: Skye.Seat n) (t:RG.Slot)(p:BudgetPoint), t.length ≤10 → p.power≤3 → p.order ≤ v → Haw p z (Pax z) (fun U:Pane n=> t.atSite U z) (C*p.threshold):=by
 obtain ⟨C,h,k⟩:=slotChart SU.group 10 v; let F:= (max 1 (C*((25:ℝ)^3)^v)); refine ⟨F,le_max_left ..,fun n z t p l d h'=>?_⟩
 let X:=fun U:Pane n=> t.atSite U z
 have hp:LocalOn (Pax z) X:=by
    intro U V i; unfold X; rw [Work.F02.atSite_curvature, Work.F02.atSite_curvature]; apply congrArg SU.group.curvature; apply travel_local _ _ U V; apply agrees_mono i; intro x e; apply halo_spec.mpr -- membership coercions tune
    have ht: (Work.F02.slotWalk t).length≤20:=by unfold Work.F02.slotWalk Slot.length Lattice.reverse at *; simp only [List.length_append,List.length_map,List.length_reverse,show (square t.plaq.val.1 t.plaq.val.2).length=4 from rfl]; omega
    exact ⟨z,mem_singleton_self z,(Extra.Iteration.Shapes.visits_dist z x (Work.F02.slotWalk t) e).trans (ht.trans (by decide))⟩ -- orientation
 refine ⟨hp,(by unfold Slot.atSite Lattice.expandAt; fun_prop),fun i q=>shores ((k (More n) i z t l).order h') d h' (subset_refl _) hp zero_le_one ?_⟩ -- n?=More
 let T:=slotFace t z; rw [atSite_path,Gauge.norm_adjoint,one_mul]; apply (SU.group.curvature_norm _).trans
 refine (q T fun a=>?_ ).le; apply Finset.disjoint_left.mp a ?_ (WilsonStartup.anchor_visit T) -- tune imports
 exact halo_spec.mpr ⟨z,mem_singleton_self z,(Work.E04.slot_separation t z).trans (l.trans (by decide))⟩
end Housing
end Lenten
end YM.CF.TableF
end
