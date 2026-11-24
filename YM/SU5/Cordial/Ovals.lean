import YM.SU5.FiniteGaugeData.Tower.Alliance
/-! # with small mesh-norm deficit detected off coincidence in a scaling family, arrive on maximum continuous part in the limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ
open Function Filter Set Metric ContinuousLinearMap
open scoped Topology InnerProductSpace Classical
variable {G:AddSubgroup ℝ}{H:Hilbert} (P:Players G H)
namespace OrbitTools
variable (v:H)(u:G)
private def Δ := ‖v‖^2-(inner ℂ v (P.play u v)).re
def front (t:ℕ→ℝ) (x:ℕ→ G) (u:ℝ) := Tendsto (fun i=>(x i:ℝ)/(t i)) atTop (𝓝 u)
lemma ascends {u:ℕ→G}{t:ℕ→ℝ}{x y: ℝ}{w:ℕ→G}(h:front t u x)(p:front t w y): front t (u+w) (x+y):= (h.add p).congr fun i=> by simp [add_div]
lemma turnRight (P:Players G H)(x:H)(b a:G): dist (P.play b x) x ≤ dist (P.play (b+a) x) x + dist (P.play a x) x :=by
 rw [P.paved H b a x|>.symm,P.symmetric]
 calc dist _ _ = dist (P.play a (P.play b x)) (P.play a x):= (P.rigid H ..).symm
      _ ≤ _:=by exact (dist_triangle ..).trans_eq (by rw [dist_comm x (P.play a x)])
lemma deficit : dist (P.play u v) v ^ 2=2*(Δ P v u):= by
 rw [dist_comm,dist_eq_norm,norm_sub_sq (𝕜:=ℂ), P.wins H]
 dsimp only [Δ]; change ‖v‖^2-2*Complex.re (inner ℂ v (P.play u v))+_= _; ring
lemma reduction (h:inner ℂ v (P.play u (P.pi_c v))=inner ℂ v (P.play u v)): ‖v-P.pi_c v‖ ≤ dist (P.play u v) v:= by
 let y:=P.play u (P.pi_c v); have hs: y∈P.lives H:= Eq.mpr (congrArg (fun a=> a∈P.lives H) (show y=_ from DFunLike.congr_fun (P.pi_play u) v)) (P.repaired (P.play u v)) -- calc coer
 have he: ‖v-P.pi_c v‖≤ ‖v-y‖:= by
   unfold Players.pi_c; rw [Submodule.starProjection_minimal]; have hb : BddBelow (range (fun x:P.lives H=> ‖v-(x:H)‖)):= ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩; exact ciInf_le hb ⟨y,hs⟩
 apply he.trans; apply (sq_le_sq₀ (norm_nonneg _) dist_nonneg).mp
 rw [norm_sub_sq (𝕜:=ℂ),dist_comm,dist_eq_norm,norm_sub_sq (𝕜:=ℂ), show inner ℂ v y=_ from h]
 apply add_le_add_right -- orientation mathlib
 apply pow_le_pow_left₀ (norm_nonneg _); unfold y; simp_rw [P.wins H]; exact (P.lives H).norm_starProjection_apply_le _
variable (F:ℝ→ℂ)(x:ℕ→H)(e:ℕ→ℝ)
structure Recovers : Prop where
 zero :ContinuousAt F 0
 increases : ∀ t:ℝ,0<t→∃ d, front e (G:=G) d t
 norm_lands : Tendsto (fun i:ℕ=>‖x i‖^2) atTop (𝓝 ((F 0).re))
 meets : ∀ (u:ℕ→G) (t:ℝ), front e u t → 0<t → Tendsto (fun i=> inner ℂ (x i) (P.play (u i) (x i))) atTop (𝓝 (F t)) ∧ ∀ᶠ i:ℕ in atTop, inner ℂ (x i) (P.play (u i) (P.pi_c (x i)))=inner ℂ (x i) (P.play (u i) (x i))
variable {P F x e}(R:Recovers P F x e)
namespace Recovers
include R
private lemma close_choice {ε:ℝ}(h:0<ε): ∃ t> (0:ℝ), ∀ (d:ℕ→G), front e d t→∀ᶠ i:ℕ in atTop, dist (P.play (d i) (x i)) (x i)<ε := by
 let J(t:ℝ):ℝ:=2*((F 0).re-(F t).re); have he:J 0< ε^2:=by unfold J; simp; positivity
 have ht:ContinuousAt J 0:= continuousAt_const.mul (continuousAt_const.sub (Complex.continuous_re.continuousAt.comp R.zero))
 have hu:= eventually_nhdsWithin_of_eventually_nhds (s:=Set.Ioi (0:ℝ)) (ht.tendsto.eventually (gt_mem_nhds he)); obtain ⟨t,p,T⟩:= (hu.and (self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ)) (a:=0))).exists
 refine ⟨t,T,fun v e=>?_⟩
 have hv := (R.norm_lands.sub (Complex.continuous_re.continuousAt.tendsto.comp (R.meets v t e T).1)).const_mul 2
 filter_upwards [hv.eventually (gt_mem_nhds (show J t < _ from p))] with i c; exact (sq_lt_sq₀ dist_nonneg h.le).mp ((deficit P ..).trans_lt (show 2*Δ P (x i) (v i)<ε^2 from c))
lemma clear : Tendsto (fun i=>P.pi_c (x i)-x i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply Metric.tendsto_nhds.mpr; intro ε h; obtain ⟨t,v,V⟩:= R.close_choice h; obtain ⟨u,g⟩:=R.increases t v; filter_upwards [V u g,(R.meets u t g v).2] with i h₁ h₂
 simp only [Real.dist_eq,sub_zero,abs_norm]; rw [norm_sub_rev]; exact (reduction P (x i) (u i) h₂).trans_lt h₁
lemma continuous_on (u:ℕ→G)(x':front e u 0): Tendsto (fun i=>P.play (u i) (x i)-x i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply Metric.tendsto_nhds.mpr; intro ε h; obtain ⟨t,p,w⟩:= R.close_choice (half_pos h); obtain ⟨y,Y⟩:=R.increases t p
 filter_upwards [w y Y,w (u+y) (by simpa using ascends x' Y)] with i H J
 simp only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg,←dist_eq_norm] -- `zero` orientation
 apply (turnRight P (x i) (u i) (y i)).trans_lt; exact (add_lt_add J H).trans_le (le_of_eq (by ring))
end Recovers
end OrbitTools
namespace Alliance
variable {I:Type*}(S:Alliance I G H)(L:List I)(x:ℕ→H)
lemma stack_zooms (h:∀ i∈L, Tendsto (fun n:ℕ=>(S.crew i).pi_c (x n)-x n) atTop (𝓝 0)) : Tendsto (fun n=> S.stackS L (x n)-x n) atTop (𝓝 0):=by
 induction L with
 | nil=> exact tendsto_const_nhds.congr fun i=> (sub_self (x i)).symm
 | cons i L ih=>
    let f:= (S.crew i).pi_c; have he:= (f.continuous.continuousAt.tendsto.comp (ih (fun i p=>h i (List.Mem.tail _ p)))).add (h i (List.mem_cons_self ..)); rw [map_zero,zero_add] at he; refine he.congr fun n=>?_ ; simp [f, shel_step]
lemma raw_isometry (v:I→G)(x:H): ‖S.raw L v x‖=‖x‖:=by induction L with|nil=>rfl|cons i L ih=> rw [raw_step,ContinuousLinearMap.comp_apply,(S.crew i).wins H,ih]
lemma raw_zoom {v:ℕ→I→G}(h:∀ i∈L, Tendsto (fun n=>(S.crew i).play (v n i) (x n) - x n) atTop (𝓝 0)): Tendsto (fun n=> S.raw L (v n) (x n) - x n) atTop (𝓝 0) := by
 induction L with
 | nil=> exact tendsto_const_nhds.congr fun n=> (sub_self (x n)).symm
 | cons i L ih=>
    let f(n):=S.raw L (v n) (x n); let U(n:ℕ):=(S.crew i).play (v n i)
    have he: Tendsto (fun n=>U n (f n - x n)) atTop (𝓝 0):=by rw [tendsto_zero_iff_norm_tendsto_zero]; simp_rw [U,(S.crew i).wins H]; exact tendsto_zero_iff_norm_tendsto_zero.mp (ih (fun i v=> h i (List.Mem.tail _ v)))
    have hx:= he.add (h i (List.mem_cons_self ..)); rw [zero_add] at hx; refine hx.congr fun i=>?_ ; rw [map_sub]; exact sub_add_sub_cancel ..
end Alliance
end YM.CF.Buffered.Afterglow.Tower.Germ
