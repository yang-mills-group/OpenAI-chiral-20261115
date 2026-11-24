import YM.CF.BProof.Triple
import YM.CF.BProof.Borel

/-! Neighborhoods and labels in the finite cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mag
open Function SU NormedSpace Matrix Filter Metric Set MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius Topology ContDiff NNReal InnerProductSpace
local notation "M" => group.mat
local notation "E'" => group.lieExp

def fits (y : Triple) (k : E) := ∀ u, ‖y-orbit k‖≤‖y-orbit u‖
lemma fits_exists (y : Triple) : ∃ k,fits y k := by
 obtain ⟨k,-,hk⟩:= isCompact_univ.exists_isMinOn univ_nonempty (f:=fun k: E=>‖y-orbit k‖) ((continuous_const.sub orbit_cont).norm.continuousOn)
 exact ⟨k,fun u=>hk (mem_univ u)⟩
lemma fits_turn (x : Triple) (k a : E) : fits x k ↔ fits (turn a x) (k*a⁻¹) := by
 have he (x : Triple)(k a : E) : ‖turn a x-orbit (k*a⁻¹)‖=‖x-orbit k‖:=by rw [←orbit_move,← turn_sub,turn_norm]
 unfold fits; conv_rhs => rw [(Equiv.mulRight a⁻¹).surjective.forall]; simp only [Equiv.coe_mulRight,he]
lemma fits_graph : IsClosed {p : Triple×E|fits p.1 p.2} := by
 simp only [fits,setOf_forall]; exact isClosed_iInter fun _ => isClosed_le (Continuous.norm (continuous_fst.sub (orbit_cont.comp continuous_snd))) (Continuous.norm (continuous_fst.sub continuous_const))

abbrev fitAll : ∃ p : Triple → E,Measurable p ∧ ∀ x,fits x (p x) := closed_choice _ fits_graph fits_exists

def lead := fitAll.choose
lemma lead_spec : Measurable lead ∧ ∀ x,fits x (lead x) := fitAll.choose_spec

/- small orbit distance licenses a parameter in prescribed chart about 1, using compactness
rather than any global continuous choice. -/
lemma entered (ε : ℝ) (h : 0<ε) : ∃ c : ℝ,0<c ∧ ∀ k:E, ‖orbit k-B0‖ ≤ c →
    ∃ i : Fin 5, ∃ v∈ball (0:Lie) ε, center i*k=(E' v)⁻¹ := by
 let S := {u : E | ∃ v∈ball (0:Lie) ε,u=(E' v)⁻¹}
 have he : ContinuousAt (group.plog ∘ group.mat) 1 := by exact (show ContinuousAt group.plog (M 1) from group.plog_diff.continuousAt).comp group.continuous_mat.continuousAt
 have hu : S ∈ 𝓝 (1:E):=by
   have ht : ∀ᶠ x : E in 𝓝 1, x∈ {u:E|∃ v∈ball (0:Lie) ε,u=E' v}:=by
     have hk:=group.plog_right; filter_upwards [he (ball_mem_nhds (group.plog (M 1)) h),hk] with u hp H
     exact ⟨_,by simpa [Function.comp_apply] using! hp,H.symm⟩
   have hw:Tendsto (Inv.inv : E→E) (𝓝 1) (𝓝 1):=by simpa using (continuous_inv (G:=E)).tendsto (1:E)
   filter_upwards [hw.eventually ht] with u hg
   obtain ⟨v,hv,h⟩:=hg; exact ⟨v,hv,inv_eq_iff_eq_inv.mp h⟩
 obtain ⟨U,hU,u,Uu⟩:= _root_.mem_nhds_iff.mp hu
 let T:= {x : E| ∃ i : Fin 5, center i*x∈U}
 have hT:IsOpen T:=by unfold T; rw [setOf_exists]; exact isOpen_iUnion fun i=> u.preimage (continuous_const.mul continuous_id)
 have hk:IsCompact (orbit '' Tᶜ):= hT.isClosed_compl.isCompact.image orbit_cont
 have hz:B0∈ (orbit '' Tᶜ)ᶜ:= by
   rintro ⟨x,hx,hg⟩; obtain ⟨i,hi⟩:=(fiber x 1).mp (by simpa using hg); exact hx ⟨i,hi ▸ Uu⟩
 obtain ⟨c,hc,hl⟩:= Metric.mem_nhds_iff.mp (hk.isClosed.isOpen_compl.mem_nhds hz)
 refine ⟨c/2,half_pos hc,fun k H=>?_⟩
 have hh : k∈T:= not_not.mp (fun hi=> hl (show orbit k ∈ ball B0 c from mem_ball.mpr (by rw [dist_eq_norm]; linarith)) ⟨k,hi,rfl⟩)
 obtain ⟨i,H⟩:=hh; exact ⟨i,hU H⟩

lemma orbit_unique : ∃ c : ℝ,0<c∧∀ (k l : E) (x : Triple), ‖x-orbit k‖ ≤ c → fits x k → fits x l → orbit k=orbit l := by
 obtain ⟨b,δ,hb,hδ,H⟩:= ImmNormal (a:=(0:Lie)) patch_s.contDiffAt immersion
 obtain ⟨c,hc,V⟩:= entered b hb
 have hh (l : E) (x : Triple) (ha : ‖x-orbit 1‖≤min (c/2) δ) (h : fits x 1) (e : fits x l) : orbit l=orbit 1:=by
    obtain ⟨i,y,hy,p⟩:=V l (by
      rw [← orbit_one]; have hr:= ha.trans (min_le_left ..); exact (norm_sub_le_norm_sub_add_norm_sub _ x _).trans (by rw [norm_sub_rev (orbit l)]; linarith [e 1]))
    have hv (x:Lie): orbit ((E' x)⁻¹)=patch x:=by unfold orbit patch; rw [inv_inv]
    have ht : orbit l=patch y:=by rw [← orbit_center i l,p,hv]
    have hk : patch 0= orbit 1 := patch_zero.trans orbit_one.symm
    have hr:= H y hy x (hk.symm ▸ ha.trans (min_le_right ..)) (fun w=>by rw [hk,← hv]; exact h _) (by rw [hk,←ht]; exact e _)
    rw [ht,hr,hk]
 refine ⟨min (c/2) δ, lt_min (half_pos hc) hδ,fun k l x hx hk hl => turn_inj k ?_⟩
 rw [orbit_move, orbit_move,mul_inv_cancel]; symm
 have he:= (fits_turn x k k).mp hk; rw [mul_inv_cancel] at he
 apply hh _ _ _ he ((fits_turn x l k).mp hl)
 rw [← mul_inv_cancel k,← orbit_move,← turn_sub,turn_norm]; exact hx

/-- Linear cost from triple fit to position of at least one nearest frame. -/
theorem a_frame : ∃ C ε : ℝ,0<C ∧ 0<ε ∧ ∀ x : Triple, ‖x-B0‖ ≤ ε →
    ∀ k : E, fits x k → ∃ i : Fin 5, cd group (center i*k) 1 ≤ C*‖x-B0‖ := by
 obtain ⟨c,h,hc,hh,H⟩:= ImmPrice (a:=(0:Lie)) patch_s.contDiffAt immersion
 obtain ⟨w,u,hw,hu,V⟩:= chargedLip (a:=(0:Lie)) group.exp_jet.contDiffAt
 obtain ⟨ε,he,L⟩:= entered (min h u) (lt_min hh hu)
 have hs:=group.colorScale_pos
 refine ⟨(w*2/c)/group.colorScale,ε/2,by positivity,half_pos he,fun x hx k hk=> ?_⟩
 have hd : ‖orbit k-B0‖ ≤ 2*‖x-B0‖:= by
   apply (norm_sub_le_norm_sub_add_norm_sub _ x _).trans; rw [norm_sub_rev (orbit k)]; have H:=hk 1; rw [orbit_one] at H; linarith
 obtain ⟨i,v,hv,hq⟩:=L k (by linarith)
 have hV: ‖v‖ ≤ min h u:=by rw [mem_ball,dist_zero_right] at hv; exact hv.le
 have he:= H v (mem_closedBall.mpr (by rw [dist_zero_right]; exact hV.trans (min_le_left ..)))
 have hl:patch v=orbit k:=by rw [← orbit_center i k,hq,orbit,inv_inv]; rfl
 rw [patch_zero,hl,sub_zero] at he
 refine ⟨i,?_⟩; rw [hq,← cd_inv,_root_.inv_inv,inv_one,norm_le_scale]
 apply le_trans (b:=w*‖v‖); simpa only [Gauge.mat_lieExp_zero,sub_zero] using V v (mem_closedBall.mpr (by rw [dist_zero_right]; exact hV.trans (min_le_right ..))) 0 (mem_closedBall_self hu.le)
 field_simp; nlinarith
end YM.CF.BProof.Mag
