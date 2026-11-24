import YM.SU5.Reconstruction.Trap.Rebate
import Mathlib.Analysis.Complex.PhragmenLindelof
/-!
# In this same normalized unit, show payoff required about UV only (and needed vacuum recognition)
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a : Axis} {Γ : AddSubgroup ℝ} (S : OS.Semigroup H a)
variable (d : Dense (Γ:Set ℝ)) (X : Sunbelt a Γ H)
  (g : ∀ i,∀ (z : Γ) (t:ℝ≥0), ((X.track.crew i).play z).comp (S.E t)=(S.E t).comp ((X.track.crew i).play z))
local notation "Gt" => (Axis→Γ)
local notation "C₀" => X.track.aviator X.list
local notation "U" => glass X d S g
local notation "G₀" => X.track.Realm X.list
local notation "H₀" => H.space
local notation "D₁" => {i:Axis//i≠a}
local notation "Z" u:max s:max=> byStamp a u s

def Cheaper (e δ:ℝ):Prop := ∀ i:{i:Axis//i≠a},∀ z:Γ,0<(z:ℝ)→ (z:ℝ)<e → ∀ v:H,
   let u:=byStamp a i.val z
   let t:= (face u a).toNNReal
   ‖(S.E t) (transverse_play X u v)- S.E t v‖^2 ≤ ‖v-S.E t v‖^2 + δ*‖v‖^2
abbrev SmallCost : Prop:=∀ δ:ℝ, 0 < δ→ ∃ e>0,Cheaper S X e δ
abbrev Shelf : Set E4 := closure (⋃ x:H, (S.ℚmeasure.diagonal x).support)
variable {e δ : ℝ} (h : SmallCost S X) (v : Cheaper S X e δ)
include h g
lemma true_room: C₀=⊤:= by
 apply le_antisymm le_top; intro x _
 apply (X.track.assembled X.list x).mpr; intro i hi
 let E:= X.track.crew i
 apply E.living.mpr; intro e p
 let δ:= e^2/(100*(1+‖x‖^2)); have he: 0 < 100*(1+‖x‖^2):= by positivity
 obtain ⟨u,t,v⟩:= h δ (by dsimp only [δ]; positivity); have hD:δ*‖x‖^2 ≤ (e^2)/100:= calc
    _ ≤ δ*(1+‖x‖^2):= by
      exact mul_le_mul_of_nonneg_left (by linarith) (by unfold δ; positivity)
    _ = _:= by unfold δ; have he:1+‖x‖^2 ≠ 0:=(by positivity); field_simp
 have hp : ∀ᶠ z in 𝓝 (0:ℝ), dist x (S.E z.toNNReal x)< e/5 ∧ z < u := by
   apply Eventually.and _ (gt_mem_nhds t)
   refine (((continuous_const (y:=x)).dist ((S.continuousE x).comp continuous_real_toNNReal)).tendsto 0).eventually (p:=fun y=> y<e/5) ?_
   change ∀ᶠ y in 𝓝 (dist x (S.E (0:ℝ).toNNReal x)), y<e/5
   rw [Real.toNNReal_zero,S.eZero,ContinuousLinearMap.id_apply,dist_self]; exact gt_mem_nhds (by linarith)
 obtain ⟨w,wt,hp⟩:= Metric.mem_nhds_iff.mp hp
 have hv₀(z:Γ)(zt:0<(z:ℝ))(hz:(z:ℝ)<w): dist (E.play z x) x<e:=by
   obtain ⟨z0,z1⟩:= (show dist x (S.E (z:ℝ).toNNReal x)<e/5 ∧ (z:ℝ)<u from hp (mem_ball.mpr (by simpa [abs_of_pos zt])))
   specialize v i z zt z1 x; obtain ⟨_,h₁,h₂⟩:= spotlight2 X z i z; dsimp only at v; unfold byStamp at v; rw [h₁,h₂] at v
   let y:= S.E (z:ℝ).toNNReal x
   have hl: dist (E.play z y) y < e/2:= by
     have h1: dist (E.play z y) y ^ 2 ≤ (dist x y)^2 + δ* ‖x‖^2:= by
       rw [dist_eq_norm,dist_eq_norm]; nth_rw 1 [show E.play z y=S.E (z:ℝ).toNNReal (E.play z x) from DFunLike.congr_fun (g i z _) x]; exact v
     have h2:dist x y<e/5:= z0
     nlinarith [dist_nonneg (x:=x) (y:=y)]
   calc
    _ ≤ dist (E.play z x) (E.play z y)+(dist (E.play z y) y + dist y x):= (dist_triangle ..).trans (add_le_add_right (dist_triangle ..) _) 
    _ < _:= by rw [E.rigid H,dist_comm y x]; change dist x y < _ at z0; linarith
 refine ⟨w,wt,fun z t=>?_⟩; rcases lt_trichotomy (0:ℝ) (z:ℝ) with v|v|v
 · exact hv₀ z v (by simpa [abs_of_pos v] using t)
 · have h:z=0:= Subtype.ext v.symm; rw [h,E.play_zero]; simpa
 rw [← E.rigid H (-z) _ _, E.returns, dist_comm]; apply hv₀ (-z) (neg_pos.mpr v); simpa [abs_of_neg v] using t
-- price spectrum
omit g h
lemma shelf_ePays (p:E4) (h:p∈ Shelf S) : 0≤p a:= closure_minimal (iUnion_subset fun i=> S.nonneg i) (isClosed_le continuous_const (by fun_prop)) h
lemma shelf_ae (x:H): ∀ᵐ p ∂(S.ℚmeasure.diagonal x), p∈ Shelf S:= Eventually.mono MeasureTheory.Measure.support_mem_ae $ fun _ v=>subset_closure (mem_iUnion_of_mem x v)
private lemma soft_impl (i:D₁)(t:ℝ≥0)(v: ∀ x:H, ‖S.U ((t:ℝ) • cross a i.val i.property) (S.E t x)-S.E t x‖^2 ≤ ‖x-S.E t x‖^2+δ*‖x‖^2): ∀ p∈ Shelf S, tension ((t:ℝ) • cross a i.val i.property) t p ≤ δ:= by
 intro p x
 refine closure_minimal (t:={p | tension ((t:ℝ) • cross a i.val i.property) t p ≤ δ}) (iUnion_subset ?_) (isClosed_le (by fun_prop) continuous_const) x
 intro w; apply Measure.support_subset_of_isClosed (isClosed_le (by fun_prop) continuous_const)
 apply ae_le_of_forall_setIntegral_le (can_enter S w _ t) (integrable_const δ); intro r hr _
 rw [← restrictP S hr,integral_const,smul_eq_mul, mul_comm,all_norm,← pressure_amount]
 linarith [v (S.ℚmeasure.region r w)]
include d g v
private lemma stamp_smooth_T (z:Γ)(hp:0<(z:ℝ))(u:(z:ℝ)<e)(i:D₁)(x:G₀): let p:=byStamp a i.val z; let t:=(face p a).toNNReal
                                                                        ‖(U).U (diameter (face p)) ((U).E t x)-(U).E t x‖^2 ≤ ‖x-(U).E t x‖^2+δ*‖x‖^2:=by
 intro p t
 erw [← ContinuousLinearMap.comp_apply ( (U).U _), ← (U).independent, ContinuousLinearMap.comp_apply];
 change ‖(((U).E t ((U).U _ x):C₀).val:H)- ((U).E t x:C₀).val‖^2 ≤ ‖x.val-((U).E t x:C₀).val‖^2 + _
 rw [glass_heat,glass_heat,glass_move]; exact v i z hp u x.val
lemma soft_shelf (i:D₁)(t:ℝ≥0)(hp:0<t)(hx:(t:ℝ)<e) (x:E4)(h:x ∈ Shelf (glass X d S g)): tension ((t:ℝ) • cross a i.val i.property) t x≤δ:= by
 let P:=cross a i.val i.property
 refine soft_impl (U) i t (fun x=> ?_) x h
 let A:= glass X d S g; let y(w:ℝ):= A.E w.toNNReal x; have hy:Continuous y:= (A.continuousE _).comp continuous_real_toNNReal
 have hh: IsClosed {w:ℝ|‖A.U (w • P) (y w)-y w‖^2 ≤ ‖x-y w‖^2+δ*‖x‖^2}:= isClosed_le ((((A.cont_cross _ (fun x:ℝ=> x • P) hy (by fun_prop)).sub hy).norm).pow 2) ((((continuous_const.sub hy).norm).pow 2).add continuous_const)
 have hz: (t:ℝ)∈ {w:ℝ|‖A.U (w • P) (y w)-y w‖^2 ≤ ‖x-y w‖^2+δ*‖x‖^2}:= closure_minimal ?_ hh (isOpen_Ioo.closure_inter ⟨d (t:ℝ),(show (t:ℝ)∈ Ioo 0 e from ⟨by exact_mod_cast hp,hx⟩)⟩)
 · simpa only [P,mem_setOf,y,A,Real.toNNReal_coe] using hz
 rintro w ⟨z,z'⟩; let s:Γ:= ⟨w,z⟩; obtain ⟨b,q,h⟩:= spotlight2 X s i s; let p:= byStamp a i.val s; have ht:=stamp_smooth_T S d X g v s z'.1 z'.2 i x; dsimp only at ht; rw [show face (byStamp a i s) a=w from q, show diameter (a:=a) (face (byStamp a i s))= w • P from Subtype.ext b] at ht; exact ht
end YM.Roy
