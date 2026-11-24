/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.TormentΛL
import YM.SU5.Macro.Across
/-!
 # Joint continuity with moving probe pockets. From finite uniform blanket in Wide (strengthen C12).
 # Edge sweep at Mink local.Box.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Work.C12
open YM.Boundary
open Function Set Filter Boundary Analysis Distribution
open scoped Topology InnerProductSpace BigOperators ContDiff
variable {n:ℕ}
lemma diffuseBΛL (h : Bid.Wide n) (A : NSF.Boundary.Blanket n) (R : ℝ) (hR : 0 ≤ R)
    (i j : ℕ) :
    ∃ X:Joint n→ℝ, Continuous X ∧ X 0=0 ∧ ∀ f,∀ y ∈ NSF.Boundary.shores n, ‖y‖ ≤ R → Probe.size i j (A.diffuser y f) ≤ X f := by
  choose k C hC hA using (attenuate_estimate h A R hR)
  let B (f:Joint n) (l : ℕ) := 2 ^ (k l + i) * (Finset.Iic (k l + i, j - l)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
  let W(f:Joint n):=∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * C l * B f l
  refine ⟨W, ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun l _=> continuous_const.mul (continuous_const.mul ?_)
    apply Seminorm.continuous_finsetSup; exact fun i _=> Probe.cont_size ..
  · simp [W,B]
  intro f y hy hyR
  have hB (l : ℕ) (x : Points n) :
      (1 + ‖x‖) ^ (k l + i) * ‖iteratedFDeriv ℝ (j - l) f x‖ ≤ B f l :=
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k l + i, j - l)) le_rfl le_rfl f x
  have hpos (l : ℕ) : 0 ≤ B f l := (show 0 ≤ _ * ‖_‖ from mul_nonneg (by positivity)
    (norm_nonneg _)).trans (hB l 0)
  unfold W
  refine SchwartzMap.seminorm_le_bound ℂ _ _ _
    (Finset.sum_nonneg (fun l _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC l)) (hpos l)))
    (fun x => ?_)
  rw [diffuser_eq h A hy]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (actual h A hy).1
      (f.smooth ⊤) x (mod_cast le_top)) (by positivity))
  rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun l _ => ?_)
  calc
    _ ≤ (1 + ‖x‖)^i * ((j.choose l : ℝ) * (C l * (1 + ‖x‖)^(k l)) *
        ‖iteratedFDeriv ℝ (j-l) f x‖) := by
      gcongr
      · linarith
      · exact hA _ _ hy hyR x
    _ = (j.choose l : ℝ)*C l*((1 + ‖x‖)^(k l + i) * ‖iteratedFDeriv ℝ (j-l) f x‖) := by
      rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB l x) (by have := hC l; positivity)

end YM.NSF.Work.C12
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis Kernel Complex Metric Distribution
open scoped BigOperators Topology ContDiff InnerProductSpace
open Complex
variable {n:ℕ}
variable (D:Blanket n)
variable {U: Type*}{l:Filter U}(f:U→Joint n)(y:U→Points n)(v:Points n)(p:Joint n)
lemma diffuseJΛL (hv:v∈shores n)(hf:Tendsto f l (𝓝 p))(hy:Tendsto y l (𝓝[shores n] v)): Tendsto (fun x=> D.diffuser (y x) (f x)) l (𝓝 (D.diffuser v p)):=by
 have hz:= (Work.C12.answer n (Work.C10.answer n) D).seen p v hv
 have hp:Tendsto (fun x=>f x-p) l (𝓝 0):=by simpa using hf.sub (tendsto_const_nhds (x:=p))
 have he: Tendsto (fun x=> D.diffuser (y x) (f x-p)) l (𝓝 0):=by
    obtain ⟨R,hR⟩:=exists_gt ‖v‖
    apply (Probe.tendN l _ _).2; intro i j ε e; obtain ⟨B,h,C,H⟩:= Work.C12.diffuseBΛL (Work.C10.answer n) D R ((norm_nonneg _).trans hR.le) i j
    have ht:= (h.tendsto 0).comp hp; rw [C] at ht
    filter_upwards [ht.eventually (gt_mem_nhds e),hy.eventually self_mem_nhdsWithin,(hy.mono_right nhdsWithin_le_nhds).norm.eventually (gt_mem_nhds hR)] with x he hu hz
    rw[sub_zero]; exact lt_of_le_of_lt (H _ _ hu (show ‖y x‖<R from hz).le) (show B _<ε from he)
 have ht:= he.add (hz.tendsto.comp hy); simp only [map_sub, Function.comp_def,sub_add_cancel,zero_add] at ht; exact ht
lemma partialJΛL (X:Distn (Points n))(hv:v∈shores n)(hf:Tendsto f l (𝓝 p))(hy:Tendsto y l (𝓝[shores n] v)): Tendsto (fun x=> D.partialD X (y x) (f x)) l (𝓝 (D.partialD X v p)) := (Distn.fourier X).continuous.continuousAt.tendsto.comp (diffuseJΛL D (fun i=> Probe.port (f i)) _ _ _ hv (Probe.port.continuous.continuousAt.tendsto.comp hf) hy)
variable {v:Points n}(hv:v∈fields n)
include hv
lemma upStretchΛL (q:ℝ)(p:0<q): q • v∈fields n:= by
 apply mem_iInter.mpr; intro i; apply mem_iInter.mpr; intro j; apply mem_iInter.mpr; intro t; change q • v j - q • v i∈inside
 rw [← smul_sub]; have he: v j - v i∈inside:= mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hv i) j) t; change ‖_‖ < _; rw [rest_mul,clock_mul,norm_smul,Real.norm_of_nonneg p.le]; exact mul_lt_mul_of_pos_left he p
local notation3 "CUPΛ"=> ({z:ℂ|0≤z.im}: Set ℂ)
local notation3 "HUPΛ"=> ({z:ℂ|0<z.im}: Set ℂ)
omit hv
lemma SweepΛL {F:ℂ→ℂ}(h:ContinuousOn F CUPΛ)(hg:AnalyticOnNhd ℂ F HUPΛ)(e:F ∘ ofReal =ᶠ[𝓝 0] 0):EqOn F 0 CUPΛ:=by
 let J:=fun z:ℂ=> F (-z)
 have he(x:ℂ)(p:x∈HUPΛ): F x=0:=by
    let r:= -x.im-1; have ht:0<x.im:=p
    obtain ⟨a,ha,hA⟩:= Metric.mem_nhds_iff.mp e; have i: -x∈ {z:ℂ| r<z.im}∩{z|z.im<0}:=by simp only[mem_inter_iff, mem_setOf, neg_im]; dsimp only[r]; constructor<;> linarith -- name tune
    have hJ:AnalyticOnNhd ℂ J {z|z.im<0}:= fun z u=> (hg (-z) (show 0<(-z).im by rw [neg_im]; exact neg_pos.mpr u)).comp analyticAt_id.neg
    have hx:ContinuousOn J {z|z.im≤0}:= h.comp continuous_neg.continuousOn (fun z q=> show 0≤(-z).im from by rw[neg_im]; exact neg_nonneg.mpr q)
    have hd : (0:ℂ)=J (-x):= (SatinMacro.Glue.overlap_of_edge (show -a<a by linarith) (show r<0 by dsimp [r]; linarith) (f:=fun _=> (0:ℂ)) analyticOnNhd_const hJ hx (fun i v=> by
       change (0:ℂ)=F _; rw [← ofReal_neg]; exact (show F _=0 from hA (show -i ∈ Metric.ball (0:ℝ) a from by simp [Real.dist_eq,abs_lt]; exact v)).symm)) i
    simpa [J] using hd.symm
 rw [← closure_setOf_lt_im] at h ⊢ -- tune name
 exact EqOn.of_subset_closure (fun x hx=> he x hx) h continuousOn_const subset_closure Set.Subset.rfl
#print axioms diffuseJΛL
#print axioms SweepΛL
end YM.NSF.Boundary
end
