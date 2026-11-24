import YM.CF.Rue.Ore
import YM.CF.Forge.Seal
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{n:Side}{t:ℝ}
open Jet Forge
local notation "g₀"=> SU.group
variable {E F A:Type}[NormedAddCommGroup F][NormedSpace ℝ F][TopologicalSpace A]{C:ℝ}{B:Set (Pane n)}{D:Finset (Bond (More n))}{P:BudgetPoint}{k j:ℕ}{o:Seat n}
local notation "Dir"=> tangD n
lemma price_s{G: Dir→F}(h:Signs P o G C):Allows P.order G 0 (composeCost P.order C ‖Prism.silo P o‖):=by
 let L:=Prism.trunk P o; let V:=Prism.silo P o; let f:=G ∘ L; rw [show G=f ∘ V from funext fun i=> congrArg G (Prism.trench i).symm]; exact (show Allows P.order f (V 0) C from (map_zero V).symm ▸ Prism.skin h).comp (allows_linear le_rfl (by rw [V.map_zero,norm_zero]; exact norm_nonneg _))
variable {Sat:Set (Pane n)}(h:IsOpen Sat) (U:A→ Pane n→F)(p:∀ x,x∈ Sat→∀ a, Signs P o (U a ∘ gyrate D x) C)
-- leaf-wise shoots, no Smooth dependence on parameter: compact interiors handle
include p h
lemma tag_b (t:∀ x∈ Sat,Continuous (fun a=> U a x))(a:A)(u:Pane n)(v: Dir)(g:gyrate D u v∈ Sat)(l:k<P.order):Warm (fun a=> U a ∘ gyrate D u) k (a,v):=by
 let Y(x):= gyrate D u x
 let X:= Y ⁻¹' Sat∩ ball 0 (‖v‖+1); have hx:IsOpen X:=(h.preimage (stickU ..)).inter isOpen_ball; have ht:v∈X:=⟨g,mem_ball_zero_iff.mpr (lt_add_one ..)⟩
 have hu := ((p _ g a).grade); let K:=composeCost P.order C ‖Prism.silo P o‖; have hk: 0 ≤ K:= by unfold K composeCost; positivity
 obtain ⟨V,H,q⟩:=Arbor.lime (α:=Unit) (E:=F) g₀ D (k+1) (‖v‖+1) K hk
 have he(a:A)(x)(v:x∈X): Allows (k+1) (U a ∘ gyrate D u) x V:=by
    refine @q Sat (fun _=>U a)  (fun x v a'=>?_) () u x v.1 v.2
    have p':=(price_s (p x v a)).order l; exact ⟨Warm.simple _ p'.smooth,p'⟩
 refine ⟨ (Filter.Eventually.mono (continuousAt_snd (p:=(a,v))|>.tendsto.eventually (hx.mem_nhds ht)) (fun x p=>?_)),fun i l=>?_ ⟩
 · exact ((he x.1 x.2 p).order (Nat.le_add_right k 1)).smooth
 exact priorS (E:=Dir) (F:=F) hx he (fun x (p:x∈X)=> t (gyrate D u x) p.1) i l a ht
omit p
variable [MeasurableSpace E][CompleteSpace F]{f:E→Pane n→F}
lemma rank_pi (p:∀ x,x∈ Sat→∀ a, Signs P o (f a ∘ gyrate D x) C)(t:∀ x∈ Sat,StronglyMeasurable (fun a=> f a x))(g:0≤C)(μ:Measure E)[IsFiniteMeasure μ](u:Pane n)(l:u∈Sat): ContDiffAt ℝ (↑P.order:WithTop ℕ∞) (fun x=>∫ i,f i (gyrate D u x)∂μ) 0 ∧ (∀ j : ℕ,j≤P.order → Integrable (fun i=> iteratedFDeriv ℝ j (f i ∘ gyrate D u) 0) μ ∧ iteratedFDeriv ℝ j (fun x=>∫ i,f i (gyrate D u x)∂μ) 0 =∫ i, iteratedFDeriv ℝ j (f i ∘ gyrate D u) 0∂μ):=by
 let K:= composeCost P.order C ‖Prism.silo P o‖; obtain ⟨T,H⟩:= Arbor.ripple (α:=Unit) h (f:=fun i (_:Unit)=> f i) (C:=K) (fun i U p' _=> ⟨Warm.simple _ (price_s (p U p' i)).smooth, price_s (p _ p' i)⟩) (by unfold K composeCost; positivity) (fun x h _=> t x h) μ; exact ⟨(T u l ()).2.smooth,H u () _ (by rw [born]; exact l)⟩
lemma balance_l (p:∀ x,x∈ Sat→∀ a, Signs P o (f a ∘ gyrate D x) C)(t:∀ x∈ Sat,StronglyMeasurable (fun a=> f a x))(g:0≤C)(μ:Measure E)[IsFiniteMeasure μ](u:Pane n)(l:u∈Sat)(L:E→ ℝ)(q: Integrable L μ)(a:∀ i,Signs P o (f i ∘ gyrate D u) (L i)):Signs P o (fun x=>∫ i,f i (gyrate D u x)∂μ) (∫ i,L i∂μ):=by
 obtain ⟨t,g⟩:= rank_pi h p t g μ u l; refine ⟨integral_nonneg (fun i=>(a i).grade), t,fun j i y v=>?_⟩; rw [(g j i).2]; let C:=ContinuousMultilinearMap.apply ℝ (fun _ : Fin j=> Dir) F y
 let Z(x):=iteratedFDeriv ℝ j (f x∘ gyrate D u) 0
 change ‖C (∫ i,Z i∂μ)‖≤_; rw [←C.integral_comp_comm (g j i).1]
 exact (norm_integral_le_integral_norm _).trans (integral_mono (C.integrable_comp (g j i).1).norm q (fun z=>(a z).token j i y v)) -- tune C type domain n
end YM.CF.Rue
