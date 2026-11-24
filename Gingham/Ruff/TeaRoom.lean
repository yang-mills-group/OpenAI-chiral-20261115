import Gingham.Ruff.Embroidery
import YM.SU5.FiniteGaugeData.Tapestry.Precompact
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry

variable (S : Finset Cover)
variable (U : Set PairsC)

structure Steady (C D:ℝ)(f:PairsC→ℂ):Prop where
  bright(x): ‖f x‖ ≤ C
  dims(x): x∉U → f x=0
  writes(x y): x∈U →y∈U →‖f x-f y‖ ≤ D* ‖porcelain S x-porcelain S y‖

variable {X:Type*}{C D:ℝ}

-- at fixed face passage only; not requiring any continuity across
lemma chinaTB (f:X→Pigment S) (c:0≤C)(d:0≤D)(h:∀ i,Steady S U C D (daub S (f i))) :
    TotallyBounded (Set.range f):=by
 let g(i:X):= daub S (f i)
 have hv:TotallyBounded (porcelain S '' U):=by
   have hc:= (isCompact_closedBall (0:TabL S) 1).totallyBounded
   apply hc.subset; rintro z ⟨x,_,rfl⟩; exact mem_closedBall_zero_iff.mpr (TeaSet ..)
 apply capture f; intro ε t
 let δ:=ε/4; have w:0<δ:=by unfold δ;linarith
 let v:=δ/(D+1)
 have a:D*v ≤ δ:=by
   rw [show D*v=(D*δ)/(D+1) from (mul_div_assoc ..).symm]
   apply (div_le_iff₀ (by positivity:D+1>0)).mpr; nlinarith
 obtain ⟨T,p,q,u⟩:=Metric.finite_approx_of_totallyBounded hv v (by unfold v;positivity)
 letI:= q.fintype
 choose y hy l using fun i:↥T=>p i.property
 let E(i:X)(k:↥T):= g i (y k)
 refine ⟨↥T→ℂ,inferInstance,E,δ,w,(isCompact_closedBall (0:↥T→ℂ) C).totallyBounded.subset ?_,?_⟩
 · rintro _ ⟨i,rfl⟩; rw [mem_closedBall_zero_iff]; exact (pi_norm_le_iff_of_nonneg c).2 fun j=> (h i).bright _
 intro i j b
 have hz:0 ≤ 3*δ:=by positivity
 rw [dist_eq_norm]
 apply (pigmentLe S (f i - f j) hz ?_).trans_lt (by unfold δ;linarith)
 intro x
 change ‖g i x-g j x‖ ≤ _
 by_cases L:x∈U
 · obtain ⟨e,k,M⟩:=Set.mem_iUnion₂.mp (u ⟨_,L,rfl⟩)
   let r:T:=⟨e,k⟩
   have N: ‖porcelain S x-porcelain S (y r)‖ ≤v:=by rw [←dist_eq_norm,l]; exact (mem_ball.mp M).le
   have z(i:X): ‖g i x-E i r‖ ≤ δ:=
     ((h i).writes x _ L (hy _)).trans ((mul_le_mul_of_nonneg_left N d).trans a)
   rw [←dist_eq_norm]
   apply (dist_triangle _ (E i r) _).trans
   apply (add_le_add le_rfl (dist_triangle _ (E j r) _)).trans
   rw [dist_eq_norm,dist_comm (E j r) (g j x),dist_eq_norm (g j x)]
   linarith [(dist_pi_lt_iff w).mp b r,z i,z j]
 have hi:g i x=0:=(h i).dims x L
 have hj:g j x=0:=(h j).dims x L
 simpa [hi,hj] using hz


lemma lacelike (f:X→Swatch S) (c:0≤C)(d:0≤D)
   (h:∀ i j,Steady S U C D (daub S (f i j))) : TotallyBounded (Set.range f):=
 captureTuple _ fun j=> chinaTB S U _ c d (fun i=>h i j)

lemma isClosed_steady (C D:ℝ)(j:Evens S) : IsClosed {z:Swatch S| Steady S U C D (daub S (z j))}:=by
  have t(x:PairsC) : Continuous (fun z:Swatch S=>daub S (z j) x):=
     (lp.lipschitzWith_one_eval ∞ x).continuous.comp (continuous_subtype_val.comp (continuous_apply _))
  apply IsSeqClosed.isClosed;intro f g h l
  exact ⟨fun x=>le_of_tendsto ((t x).norm.continuousAt.tendsto.comp l)
      (Eventually.of_forall fun i=>(h i:Steady _ _ _ _ _).bright x),
    fun x a=>(tendsto_nhds_unique_of_eventuallyEq ((t x).continuousAt.tendsto.comp l)
      (tendsto_const_nhds (x:=0)) (Eventually.of_forall fun i=>(h i:Steady _ _ _ _ _).dims x a)),
    fun x y a b=>le_of_tendsto (((t x).sub (t y)).norm.continuousAt.tendsto.comp l)
      (Eventually.of_forall fun i=>(h i:Steady _ _ _ _ _).writes x y a b) ⟩

