import GaugeFieldConstruction.RegaliaRT
/-!
 # Real contour and retarded Ward. *FieldSight Ward option*. No b squared global or time charge shift asserted or used. All relative test data compact, independent of cutoff. `S.operator` on shared domain; real comm W defined by products of ACTUAL fields smeared and extension uniqueness. Relative stamps χ. Ward identity is in all W matrix elements (arbitrary spectator fields), not just norm between states or momentum distribution. Same f.Norm.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
lemma HatchLocalRT (U:Set E4)(w:U∈𝓝 0):∃ b:Test4,∃ h:Axis→Test4,HatchRT b h ∧ tsupport b⊆U ∧ ∀ i:Axis, tsupport (h i) ⊆ U:=by
 obtain ⟨r,t,p⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((show Tendsto Mink.divide.symm (𝓝 0) (𝓝 0) from by simpa using Mink.divide.symm.continuous.tendsto 0).eventually w)
 let f:ContDiffBump (0:Space3):= ⟨r/2,r,half_pos t,half_lt_self t⟩; let B:= acornRt (r/2) (half_pos t)
 let e: B.rOut < f.rIn:= half_lt_self (half_pos t); let L:= Mink.divide ⁻¹' closedBall 0 r
 have hL:IsClosed L:= isClosed_closedBall.preimage Mink.divide.continuous
 have hu:L⊆U:= fun v h=> by rw[← Mink.divide.symm_apply_apply v]; exact p h
 have hv(v:E4)(g:f (spatial v)≠0)(s:time v ∈ closedBall (0:ℝ) B.rOut): v∈L:=by
    have he:spatial v∈closedBall (0:Space3) r:= f.tsupport_eq ▸ subset_tsupport _ g
    change divide v∈ closedBall ((0:Space3),(0:ℝ)) r; rw [← closedBall_prod_same]; exact ⟨he,closedBall_subset_closedBall ((e.trans (half_lt_self t)).le) s⟩
 refine ⟨padRt B f,αWarmRt B f,BornUnderRT B f e, (closure_minimal ?_ hL).trans hu,fun i=> (closure_minimal ?_ hL).trans hu⟩
 · intro v q; change ((B (time (v-0))*f (spatial (v-0)):ℝ):ℂ)≠0 at q; have he:B (time v) * f (spatial v)≠0:=by simpa using q
   exact hv _ (right_ne_zero_of_mul he) (B.tsupport_eq ▸ subset_tsupport _ (left_ne_zero_of_mul he))
 intro v q; by_cases a:i=timeAxis
 · rw [αWarmRt,if_pos a] at q; change ((shutterXRt B (time v) * f (spatial v):ℝ):ℂ) ≠ 0 at q; have he:shutterXRt B (time v)*f (spatial v)≠0:=by simpa using q
   exact hv _ (right_ne_zero_of_mul he) (shutterWidthRt B (subset_tsupport _ (left_ne_zero_of_mul he)))
 rw [αWarmRt,if_neg a] at q; exact (q (SchwartzMap.zero_apply ..)).elim
-- Cf WorkC27
lemma shuttledRt {n:ℕ}(P:NearPair n)(f:Fin n→Test4): Probe.along P.switch.toContinuousLinearEquiv (Joint.materialize n f)=Joint.materialize n (f ∘ P.s):=by
 ext1 x; change Joint.materialize n f (P.switch x)=_; simp only [Joint.material_at,NearPair.switch_at,Function.comp_apply]; exact ((Equiv.prod_comp P.s (fun i=>f i (x (P.s i))))|>.symm.trans (by simp [NearPair.s]))
#print axioms HatchLocalRT
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset Distribution
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
open YM.Boundary (Joint Test4 Distn)
open NSF.LD
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable (Y:NSF.Boundary.Surface (SurfRimL A)) {D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable {R:(SurfRimL A).Rotation}{s:(SurfRimL A).RealSpin}{K:NSF.Boundary.Spins (SurfRimL A)}
variable (U:LoreL F K Y (SurfRimL Z))(Q:K.Descends R s)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable (T:NSF.Boundary.Wightman (SurfRimL A))
variable {n:ℕ}(V:Fin n→ΧiMars)(k:Fin n)(a:Axis)
local notation "ΦH" => H.TinCanL
local notation "Τ"=> CoffΜΛ H p
local notation "D_V"=> RotateCostΛL H Y
noncomputable def WordνRt (i:Axis)(f:Fin (n+1) → Test4) (j:Fin (n+1)): NSF.Boundary.Letter (SurfRimL A):= (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i j,f j)
noncomputable abbrev CostXtRt (c:NSF.Boundary.Sentence (SurfRimL A)):= inner ℂ T.operators.vacuum (T.operators.vector c)
abbrev ReflectionWardRT (i:Axis)(W:Distn (Points (n+1))):Prop:= ∀ f:Fin (n+1)→Test4, W (YM.Boundary.Joint.materialize (n+1) f)= CostXtRt T (List.ofFn (WordνRt p H V k a i f))-CostXtRt T (List.ofFn ((WordνRt p H V k a i f) ∘ (τNearRT k).s))
-- uniquely reads T. operators
variable (t:T.Realizes (W:=Y) R s)
include t
lemma captureRt (i:Axis)(W:Distn (Points (n+1))): ReflectionWardRT p H T V k a i W ↔ W=CommΘRt p H (Y:=Y) V k a i :=by
 let P:=(τNearRT k); let Cₛ:=CommΘRt p H (Y:=Y) V k a i
 have hp:ReflectionWardRT p H T V k a i Cₛ:=by
    intro F; unfold Cₛ CommΘRt CostXtRt; rw [t.meets,t.meets]; simp only [_root_.sub_apply,NearPair.flipW,ContinuousLinearMap.comp_apply, shuttledRt,NSF.Work.C29.expectOfFn]; rfl -- tune
 refine ⟨fun u=>?_,fun v=>v.symm ▸ hp⟩; rw [← sub_eq_zero]
 let T:= W-Cₛ
 have h:Submodule.span ℂ (Set.range (YM.Boundary.Joint.materialize (n+1))) ≤ T.toLinearMap.ker:=by
    apply Submodule.span_le.mpr; rintro _ ⟨a,rfl⟩; exact sub_eq_zero.2 ((u a).trans (hp a).symm)
 have he:= Submodule.topologicalClosure_minimal _ h T.isClosed_ker; rw [NSF.Work.C25.answer (n+1)] at he
 ext1 f; exact he (show f∈ (⊤:Submodule ℂ (Joint (n+1))) from Submodule.mem_top)
-- full standard allocation. Don't burden other facts. Y is W distribution; preserve
omit t
structure LocalWardRT (p:Ticket u C)(H:SurfCheckL A)(Y:NSF.Boundary.Surface (SurfRimL A))(T:NSF.Boundary.Wightman (SurfRimL A)):Prop where
  caps : ∀ (U:Set E4), U∈𝓝 0→∃ b:Test4,∃ h:Axis→Test4, HatchRT b h ∧ tsupport b⊆U ∧ ∀ i:Axis,tsupport (h i)⊆U
  knows (n:ℕ)(V:Fin n→ΧiMars)(k:Fin n)(a i:Axis)(W:Distn (Points (n+1))):ReflectionWardRT p H T V k a i W ↔ W=CommΘRt p H (Y:=Y) V k a i
  endorses (n:ℕ)(V:Fin n→ΧiMars)(k:Fin n)(a:Axis)(b:Test4)(h: Axis→Test4):HatchRT b h→RotateCostΛL H Y V k a= FutureHandRT p H (Y:=Y) V k a h
  generates (n:ℕ)(V:Fin n→ΧiMars)(k:Fin n)(a:Axis)(b:Test4)(h:Axis→Test4)(f:Fin n→ Test4): HatchRT b h → CostXtRt T (List.ofFn fun i=> ((H.TinCanL (V i)), Function.update f k (-(ΦshiftΛ (basis a) (f k))) i))= -(ΛSignXRt a)*∑ i:Axis, CommΘRt p H (Y:=Y) V k a i (χTestRT k (h i) (YM.Boundary.Joint.materialize n f))
include t hv e U Q G
lemma realWardHereRT : LocalWardRT p H Y T:=by
 refine ⟨HatchLocalRT,fun _ V k a i Z=> captureRt p H Y T V k a t i Z,fun _ V k a b h=> REALΛRT p H G U Q hv e V k a h b,?_⟩
 intro n V k a b h f w
 unfold CostXtRt; rw [t.meets]; rw [LeafWHereΛL H]
 change (RotateCostΛL _ _ _ _ _) _ = _; rw [REALΛRT p H G U Q hv e V k a h b w]; exact WorkWatchRT ..
#print axioms realWardHereRT
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
