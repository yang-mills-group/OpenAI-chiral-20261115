import GaugeFieldConstruction.AcrossLands
/-!
# Qualification independent of Election budget; simultaneous perturbation stability at a cutoff
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2800
set_option maxHeartbeats 500000
namespace YM.CF
open Function Filter Metric NormedSpace Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember MeasureTheory Vale Hom Grace Push.SectorMeasure Next.SectorChange Precision Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff BigOperators InnerProductSpace ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Mint Dial
namespace AcrossLands
open VolumeRate
variable {K:Teller group}{P:Patch}{R:ChartRatio group} {W:Grace K P R}{M m B:Side}{e b b':ℝ}{U:Grasp W.U B e}{G:GivenX W U}
variable (L:Robes M W G) (hp:K.top.clip.direct≤1)
include hp
/-- For any such infrastructure. -/
theorem territories : ∃ n, Territory K L n:=by
  obtain ⟨c,b,w,F,r,s,i',⟨S⟩⟩:= Pic.crop0 G.pearl W.note (by have he:=W.L.lobby; have ht:=P.order_cut; omega) G.health; obtain ⟨Xk,Xr,Xp,Y,k,l,X⟩:= Roe.portH S
  exact pre_quit L hp S X (le_max_right 1 _) (le_max_left ..)

-- every top side as large as this fixed threshold (two separate factors!)
variable {L}{n:ℕ}
structure CompleteMask {p:BudgetPoint}(L:Robes M W G) (n:ℕ) (β:ℝ) : Prop where
  cashM (c:Side)(u:n≤c.val): Envelope (sharpHat (c*M) U p β) ∧ sharpWeight (c*M) U p β≠0
-- Use at fixed β. In new bare schedule, not necessarily the exact term at any one volume.
variable (Λ:Territory K L n)
include Λ
lemma complete_frequent (p:BudgetPoint)(u:p.threshold≤L.k) : Set.Countable {b:ℝ | ¬CompleteMask (p:=p) L n b} := by
  let α:Type:= {c:Side//n≤c.val}; let S(c:α):Set ℝ:= {x|sharpWeight (c.val*M) U p x=0}
  have hi : ∀ i:α, (S i).Countable:= by
    intro i; exact Λ.fails i.val i.property p u
  letI:Countable α:= by unfold α; infer_instance
  refine (Set.countable_iUnion hi).mono ?_
  intro i w; by_contra t; exact w ⟨fun c h=> ⟨soars _ (Λ.min_size.trans h) u hp i,fun x=> t (Set.mem_iUnion.mpr ⟨⟨c,h⟩,x⟩)⟩⟩

lemma choose_paying (p:BudgetPoint)(u:p.threshold≤L.k){a c:ℝ}(e:a<c): ∃ x:ℝ, a<x ∧ x<c ∧ CompleteMask (p:=p) L n x:= by
 by_contra! t
 have hv:Set.Ioo a c ⊆ {b|¬CompleteMask (p:=p) L n b}:= fun i x=> t i x.1 x.2
 have hz:= ((complete_frequent hp Λ p u).mono hv).measure_zero volume
 rw [Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hz; linarith
omit Λ hp
-- scale of monitor is absolute (not volume normalized); use at small perturbations with no control
-- claimed on other volumes
local notation "Nm"=> mid m B
variable (m U)(p:BudgetPoint) (b:ℝ)
abbrev normalized (x: Orbit (mid m B)):= (sharpWeight m U p b)⁻¹ • sharpHat m U p b x
-- choose neighborhood, pull operator uniform norm with volume costs (no uniformity in c or k here!)
variable (H:Envelope (sharpHat m U p b))
include H
local notation "Wm" => sharpWeight m U p
lemma weight_cont : ContinuousAt (sharpWeight m U p) b:= by
 have he:Continuous (fun x:ℝ×Pane (mid m B)=>windX (K:=K) m b (x.1:ℂ) x.2):=by unfold windX; exact (((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul (Complex.continuous_ofReal.comp ((Nova.ren_c _).comp continuous_snd)))).cexp
 let F:= fun x:ℝ×Pane (mid m B)=>windX (K:=K) m b (x.1:ℂ) x.2
 obtain ⟨y,u⟩:= ((isCompact_Icc (a:=b-1) (b:=b+1)).prod isCompact_univ).bddAbove_image he.norm.continuousOn
 let W0(x:Skye.Orbit (mid m B)) := Scree.beamZ _ (sharpHat m U p b x)
 let Q:=fun (z:ℝ)(y:Skye.Orbit (mid m B))=> F (z,y.1)*W0 y
 have ht(x:ℝ): Wm x=∫ y, Q x y ∂city _:=by unfold sharpWeight Q F W0; simp_rw [windX_eq m U p b x,Scree.beamZ,inner_smul_right]
 have hW:Envelope W0:= Girt.pole_w (sharpHat m U p b) _ (continuous_const.inner continuous_id) H
 obtain ⟨c,v⟩:= hW.cost; rw [funext ht]
 refine continuousAt_of_dominated (F:=Q) (x₀:=b) ?_ ?_ (integrable_const (max 0 y*c)) ?_
 · refine Eventually.of_forall fun a=> ?_; exact (Measurable.mul (((he.comp (continuous_const.prodMk (continuous_id (X:=Pane (mid m B))))).measurable).comp measurable_fst) hW.meas).aestronglyMeasurable
 · filter_upwards [Icc_mem_nhds (by linarith : b-1<b) (by linarith : b<b+1)] with a (e : a∈Set.Icc _ _)
   refine Eventually.of_forall fun x=>?_ ; unfold Q; rw [norm_mul]; exact mul_le_mul ((u ⟨(a,x.1),⟨e,trivial⟩,rfl⟩).trans (le_max_right ..)) (v x) (norm_nonneg _) (le_max_left ..)
 exact Eventually.of_forall fun x=>(he.comp (continuous_id.prodMk continuous_const) |>.mul continuous_const).continuousAt

local notation "Z"=> (fun b : ℝ => (normalized m U p b : Orbit (mid m B)→_)) -- shadow
lemma stable_price (h:sharpWeight m U p b ≠ 0) (ε:ℝ) (hε:0<ε): ∀ᶠ t:ℝ in 𝓝 b, ∀ x:Orbit (mid m B), ‖normalized m U p t x - normalized m U p b x‖ < ε := by
 let F:= fun x:Pane (mid m B)=> fun t:ℝ=> (sharpWeight m U p t)⁻¹ * windX (K:=K) m b (t:ℂ) x
 have he(x:Pane Nm) : F x b=(Wm b)⁻¹:= by simp [F,windX]
 have hc(x:Pane Nm) : ContinuousAt (fun z:ℝ × Pane (mid m B)=> F z.2 z.1) (b,x):= by
   have q : ContinuousAt (fun z:ℝ × Pane (mid m B)=> Wm z.1) (b,x) := (weight_cont m U p b H).comp (x:=(b,x)) (f:=Prod.fst) continuous_fst.continuousAt
   change ContinuousAt _ (b,x); exact (q.inv₀ (show Wm b≠0 from h)).mul (show Continuous (fun x:ℝ×Pane (mid m B)=>windX (K:=K) m b (x.1:ℂ) x.2) from by unfold windX; exact (((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul (Complex.continuous_ofReal.comp ((Nova.ren_c _).comp continuous_snd)))).cexp).continuousAt
 obtain ⟨C,v⟩:= H.cost; let δ:= ε/(|C|+1); have hD:0<δ:=by unfold δ; positivity
 -- Via tube lemma on compact set
 let S:= {p:ℝ × Pane Nm | ‖F p.2 p.1-(Wm b)⁻¹‖<δ}
 have hv (x: Pane Nm): S∈𝓝 (b,x):= by
   apply Filter.mem_of_superset (Filter.mem_map.mp ((hc x) (Metric.ball_mem_nhds _ hD))); rintro ⟨t,u⟩ w
   exact (show ‖F u t-(Wm b)⁻¹‖<δ by
     rw [←he x,←dist_eq_norm]; exact (show dist (F u t) (F x b) < δ from Metric.mem_ball.mp w))
 obtain ⟨J,A,O,T,w,mT,H⟩:= generalized_tube_lemma (isCompact_singleton (x:=b)) (isCompact_univ (X:=Pane Nm)) (isOpen_interior (s:=S)) (by
   rintro ⟨u,x⟩ ⟨h,-⟩; rcases Set.mem_singleton_iff.mp h with rfl; exact mem_interior_iff_mem_nhds.mpr (hv x))
 filter_upwards [O.mem_nhds (w (Set.mem_singleton _))] with t pt x
 unfold normalized; rw [windX_eq m U _ b t, smul_smul,←sub_smul,norm_smul]
 let ℓ:= ‖F x.1 t-(Wm b)⁻¹‖; change ℓ * _ < _
 have hc : ℓ<δ:= show (t,x.1)∈S from interior_subset (H (show (t,x.1)∈_ from ⟨pt,mT trivial⟩))
 exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((v _).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))) (norm_nonneg _)) (by change ℓ*(|C|+1) < _; exact (lt_div_iff₀ (by positivity)).1 hc)
#print axioms stable_price
end AcrossLands
end YM.CF
