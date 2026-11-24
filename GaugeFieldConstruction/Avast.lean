import GaugeFieldConstruction.Aplomb
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys
open scoped Topology ContDiff BigOperators
variable {α β:Type*}(D: Axis→ Module.End ℂ (J α)){L: Axis→ Module.End ℂ (J β)}(p:Bil α β)(a:J α)(b:J β)
-- continuity in weak norm tests
variable {X:Type*}[TopologicalSpace X]{s:Set X}(f:X→ J α→ₗ[ℂ]ℂ){u:X→E4}{t:X→ℝ}
lemma outerS (g:ContinuousOn u s)(h:∀ x:J α,ContinuousOn (fun i=> f i x) s)(n:ℕ): ContinuousOn (fun i=> f i (gust D a n (u i))) s:=by
 unfold gust; simp_rw [map_sum,map_smul,smul_eq_mul]; refine continuousOn_finsetSum _ fun x _=> ContinuousOn.mul ?_ (h _); refine continuous_ofReal.comp_continuousOn ?_; unfold dock; apply continuousOn_finsetProd _; intro j _; exact Continuous.comp_continuousOn (show Continuous (fun i:E4=>i (x j)) from by fun_prop) g
lemma stalag (g:ContinuousOn u s)(h:∀ x:J α,ContinuousOn (fun i=> f i x) s)(q:ContinuousOn t s)(n:ℕ): ContinuousOn (fun i=> f i (Tapper D a n (t i) (u i))) s:=by
 unfold Tapper; simp_rw [map_sum,map_smul,smul_eq_mul]; refine continuousOn_finsetSum _ fun j _=> (continuous_ofReal.comp_continuousOn ((q.pow j).mul_const _)).mul (outerS D a f g h j) -- tune
-- tariff remainder stripped: port(Tilt ability)
variable (m:ℕ)
namespace Fundsν
variable {K U V:Set E4}
lemma TarrS {d v:X→E4}(he:∀ a b,ContinuousOn (fun x=>port p (d x) a b) s)(L:Axis→Module.End ℂ (J β))(hU:ContinuousOn u s)(hv:ContinuousOn v s)(hT:ContinuousOn t s): ContinuousOn (fun x=> port p (d x) (gust D a (m+1) (u x)) (Tapper L b m (t x) (v x))+port p (d x) (Tapper D a m (t x) (u x)) (gust L b (m+1) (v x))) s:=by
 have hw(q):ContinuousOn (fun x=>port p (d x) q (Tapper L b m (t x) (v x))) s:= by refine stalag L b (fun x=>port p (d x) q) hv ?_ hT m; exact fun x=>he q x
 have hx(q):ContinuousOn (fun x=>port p (d x) q (gust L b (m+1) (v x))) s:= by refine outerS L b (fun x=>port p (d x) q) hv ?_ (m+1); exact he q  -- tune
 exact (outerS D a (fun x=>(port p (d x)).flip (Tapper L b m (t x) (v x))) hU hw (m+1)).add (stalag D a (fun x=>(port p (d x)).flip (gust L b (m+1) (v x))) hU hx hT m)

lemma upperS {E X Y W: Type*} [TopologicalSpace E][TopologicalSpace X][TopologicalSpace Y][TopologicalSpace W]{K:Set E}{V:Set X}{T:Set Y}{H:Set W}(p:E× X×Y×W→ℂ)(c:ContinuousOn p (K ×ˢ V ×ˢ T ×ˢ H))(k:IsCompact K)(v:IsCompact V)(t:IsCompact T)(h:IsCompact H): ∃ C>0,∀ i∈K,∀ j∈V,∀ u∈T,∀ x∈H,‖p (i,j,u,x)‖ ≤ C:=by
 obtain ⟨C,e⟩:= (k.prod (v.prod (t.prod h))).bddAbove_image c.norm; refine ⟨max C 1,lt_max_of_lt_right (by norm_num),fun i a' z t u v' x p'=> le_trans (e (Set.mem_image_of_mem (fun i=>‖p i‖) (show (i,z,u,x)∈ K ×ˢ V ×ˢ T ×ˢ H from ⟨a',t,v',p'⟩))) (le_max_left ..)⟩
set_option maxHeartbeats 90000 in
lemma sale (L:Axis→ Module.End ℂ (J β))(k:IsCompact K)(v:IsCompact V)(hI:IsCompact U)(g:0∉K): ∃ C>0,∀ z∈K,∀ u∈U,∀ l∈V,∀ t:ℝ, t∈ Set.Icc 0 1 → ‖ port p z (gust D a (m+1) u) (Tapper L b m t l)+port p z (Tapper D a m t u) (gust L b (m+1) l)‖≤ C:=by
 let S:=K ×ˢ U ×ˢ V ×ˢ Set.Icc (0:ℝ) 1; let P(x:E4×E4×E4×ℝ):=port p x.1 (gust D a (m+1) x.2.1) (Tapper L b m x.2.2.2 x.2.2.1)+port p x.1 (Tapper D a m x.2.2.2 x.2.1) (gust L b (m+1) x.2.2.1)
 have he(a b):ContinuousOn (fun x:E4×E4×E4×ℝ=>port p x.1 a b) S:=by
    intro x y
    exact ((healthy (p a b) (x:=x.1) (fun h=>g (h▸y.1))).continuousAt.comp (x:=x) continuousAt_fst).continuousWithinAt -- tune
 have hp: ContinuousOn P S:=by
    refine TarrS D p a b m (d:=fun x:E4×E4×E4×ℝ=>x.1) (v:=fun x:E4×E4×E4×ℝ=>x.2.2.1) (u:= fun x:E4×E4×E4×ℝ=>x.2.1) (t:=fun x:E4×E4×E4×ℝ=>x.2.2.2) ?_ L ?_ ?_ ?_ <;> first|exact he|fun_prop
 exact upperS P hp k hI v isCompact_Icc
lemma veto {t r:ℝ}(g:Set.Icc 0 t r) : ‖(tariff (t-r) m:ℂ)‖≤ t^m:=by
 let e:ℝ:=(m.factorial:ℝ); have ht:1≤e:=Nat.one_le_cast.mpr m.factorial_pos; have v:t-r≤ t:=sub_le_self _ g.1; have he:0≤ t-r:=sub_nonneg.mpr g.2
 unfold tariff; rw [norm_real,Real.norm_of_nonneg]; · apply le_trans _ (pow_le_pow_left₀ he v _); exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ ht) -- tune
 positivity
variable (H:Lefty p D)(g:Rorky p L)
include H g
lemma borne (k:IsCompact K)(v:IsCompact V)(hI:IsCompact U)(J:0∉K): ∃ C>0, ∀ (d u l:E4),u∈U→ l∈V→ ∀ t:ℝ,0 ≤ t→ t≤1→ (∀ r ∈ Set.Icc 0 t,d+r • (l-u) ∈ K) → ‖port p (d+t • (l-u)) a b - port p d (Tapper D a m t u) (Tapper L b m t l)‖ ≤ C*t^(m+1):=by
 obtain ⟨C,Q,T⟩:=sale D p a b m L k v hI J; refine ⟨C,Q,?_⟩; intro d u l hu hl t ht ht' path; let X(r:ℝ):=port p (d+r • (l-u)); let q(r:ℝ):=Tapper D a m (t-r) u; let Rw(r:ℝ):= Tapper L b m (t-r) l
 let F (r:ℝ):= X r (q r) (Rw r); let f' (r:ℝ):=(tariff (t-r) m:ℂ)*(X r (gust D a (m+1) u) (Rw r)+X r (q r) (gust L b (m+1) l))
 have hp:∀ x ∈ Set.Icc 0 t, HasDerivWithinAt F (f' x) (Set.Icc 0 t) x :=fun x p=>HasDerivAt.hasDerivWithinAt (sprint a H g u x t b l d (fun h=> J (h ▸ path x p)) m) -- tune arg order
 have hx:∀ x∈ Set.Ico 0 t, ‖f' x‖≤ t^m*C:=by
    intro x p'; have q:Set.Icc 0 t x:= Set.Ico_subset_Icc_self p'; unfold f'; rw [norm_mul]; exact mul_le_mul (veto m q) (T _ (path x q) _ hu _ hl _ ⟨sub_nonneg.mpr q.2,(sub_le_self _ p'.1).trans ht'⟩) (norm_nonneg _) (pow_nonneg ht _)
 have W:=norm_image_sub_le_of_norm_deriv_le_segment' hp hx t (Set.right_mem_Icc.mpr ht); simp only [F,X,q,Rw,sub_self, sub_zero,zero_smul,add_zero,T0,pow_succ] at W ⊢; convert W using 1 <;> ring -- tune
end Fundsν
end YM.GaugeFieldConstruction.Wick.Yacht
end
