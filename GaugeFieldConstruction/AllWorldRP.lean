import GaugeFieldConstruction.StokeTowerRP
/-! full spatial family. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex Metric Poincare
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
variable (v:Fin n→ Letter S)(Ωv: d.system.operators.H)(x:Points n)(a:Heights n)
lemma HeightArchRP: ∃ (y z:Heights n), y∈ positiveHeight n ∧ z∈ positiveHeight n ∧ y-z=a:=by
 let q:= Small.profile 1 n; have hp:q∈ positiveHeight _:=Small.imminent zero_lt_one; obtain ⟨p,h⟩:= PadsRP q hp
 have hc:Tendsto (fun r:ℝ=> q+r • a) till (𝓝 q):=by simpa using ((show Continuous (fun r:ℝ=> q+r • a) from continuous_const.add (continuous_id.smul (continuous_const (y:=a)))).continuousWithinAt (s:=Ioi (0:ℝ)) (x:=0)).tendsto -- inference
 obtain ⟨r,t,o⟩:= ((hc.eventually (HeightLateRP h)).and (show ∀ᶠ r:ℝ in till,0<r from self_mem_nhdsWithin)).exists
 refine ⟨r⁻¹ • (q+r • a),r⁻¹ • q,HeightPlusRP (roomPositive (ample_room t)) (inv_pos.mpr o), HeightPlusRP hp (inv_pos.mpr o), ?_⟩
 rw [smul_add,smul_smul,inv_mul_cancel₀ o.ne',one_smul]; abel
lemma DawnAddRP (y:Heights n):dawn (a+y)=dawn a+dawn y:=by
 ext1 i; simp [dawn,place,← Mink.combine_at, ← map_add]
lemma DawnScaleRP (z:ℝ):dawn (z • a)= z • dawn a:=by
 ext1 i; simp [dawn,place,← Mink.combine_at, ← map_smul]
lemma EspaceRP (r:Ray): points (fun i=> position ((a i) • r.val) 0) = ((Real.sinh 1)⁻¹) • togetherL (r.boost 1) n (dawn a)+dawn ((-(Real.cosh 1/Real.sinh 1)) • a):=by
 have h: Real.sinh 1≠0:=(Real.sinh_pos_iff.mpr zero_lt_one).ne'
 ext1 i; apply Mink.ext_by
 · simp [dawn,place,r.newSpace, Ray.along,smul_smul,h]
 simp [dawn,place,r.newClock, Ray.along]
 ring
lemma CornerAbsRP (x:Points n): x=dawn (fun i=>YM.time (x i))+ ∑ i:SpaceAxis, points (fun k=> position (((YM.spatial (x k)) i) • (Ray.fromAxis i).val) 0):=by
 ext1 i; norm_num [Fin.sum_univ_succ, dawn, place]; apply Mink.ext_by
 · ext1 j; fin_cases j <;> simp [Ray.fromAxis]
 simp
include H b
lemma TerraTackRP (h:x∈ loudRP d v Ωv)(p:Lorentz): x+togetherL p n (dawn a)∈ loudRP d v Ωv:=by
 obtain ⟨y,z,t,o,hq⟩:= HeightArchRP a; have hv:= tackBoostRP d H b v Ωv _ o (tackBoostRP d H b v Ωv x t h p 1) p (-1)
 rw [← hq,sub_eq_add_neg,DawnAddRP,show dawn (-z)=-dawn z from ?_,map_add,map_neg]
 simpa only [one_smul,neg_smul,add_assoc] using hv
 simpa using DawnScaleRP z (-1)
lemma GroundTackRP (h:x∈loudRP d v Ωv):x+dawn a∈loudRP d v Ωv:=by
 have he:=TerraTackRP d H b v Ωv x a h 1; rwa [show togetherL 1 n (dawn a)=dawn a from by ext; simp] at he
lemma RoomTackRP(r:Ray)(h:x∈ loudRP d v Ωv):x+(points (fun i=> position ((a i) • r.val) 0))∈loudRP d v Ωv:=by
 rw [EspaceRP, ← map_smul,← DawnScaleRP, ← add_assoc]; exact GroundTackRP d H b v Ωv _ _ (TerraTackRP d H b v Ωv x _ h _)
lemma FullTackRP (h:x∈loudRP d v Ωv)(u:Points n): x+u∈ loudRP d v Ωv:=by
 rw [CornerAbsRP u, ← add_assoc]
 simp only [Fin.sum_univ_succ,Finset.univ_eq_empty, Finset.sum_empty, add_zero,← add_assoc]
 apply RoomTackRP d H b; apply RoomTackRP d H b; apply RoomTackRP d H b; exact GroundTackRP d H b v Ωv x _ h
#print axioms FullTackRP
end YM.NSF.Boundary
end
