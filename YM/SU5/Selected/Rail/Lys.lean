import YM.SU5.Selected.Rail.Aile
/-! # Transport of limit and AP kernels. All sorted for later gauge tests.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
open Finset
local notation "A"=> Aop
variable {x:Bin}{k:ℕ}(p:3≤k)(i:Axis)(h:x∈stemGuard)
lemma finale_20 : finale x 2 0= arc x:=by
 rw [finale,Adef,←Lat.raising, cutM,Matrix.mul_diagonal]; simp (config:={decide:=true}) [arc,show 2≠ (0:SpinIdx) by decide] -- names tune
-- local continuity of entries off the origin
include h
lemma timbre (z:x≠0) : ContinuousWithinAt (fun x=>tough x i) stemGuard x:=by
 let c:= ‖x‖/2;have hv:0<c:=div_pos (norm_pos_iff.mpr z) two_pos
 let S:= stemGuard∩ {x:Bin|c ≤ ‖x‖}; have hp :IsCompact S:= (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
 have ht : {y:Bin| c≤ ‖y‖} ∈ 𝓝[stemGuard] x:=(continuous_norm.continuousWithinAt (x:=x) (s:=stemGuard)).tendsto.eventually (show ∀ᶠ a in 𝓝 ‖x‖, c≤ a from le_mem_nhds (by unfold c; linarith [norm_pos_iff.mpr z])) -- tune
 have hg:S ⊆ {x:Bin| x≠0}:= fun t w=> norm_pos_iff.mp (hv.trans_le w.2)
 have hh(v:Cover): ContinuousOn (fun y=> slat y v i) S:=by
    intro y k; apply ContinuousAt.continuousWithinAt; have he: (↑(radius (y+stem v):ℝ):ℂ)≠0:= by exact_mod_cast (radius_pos _ (norm_pos_iff.mp ((norm_pos_iff.mpr (show y≠0 from hg k)).trans_le (peaks (stemG.mp k.1) (show peers y (y+stem v) from ⟨v,rfl⟩))))).ne'
    unfold slat; refine (ContinuousAt.mul (f:=fun y=> weave _ ^ 8) ?_ (g:=fun y=> _) ?_); · unfold weave skirt; fun_prop
    refine ContinuousAt.div ?_ ?_ he; · fun_prop
    unfold radius; fun_prop
 obtain ⟨C,hC,H⟩:=boundC i; obtain ⟨o,q⟩:= hp.bddAbove_image (hh 0).norm
 have he:ContinuousOn (fun x=> tough x i) S:=by
    apply continuousOn_tsum hh (u:= fun i:Cover=> C*income i+(Pi.single (0:Cover) o:Cover→ℝ) i) ((wallet.mul_left C).add (hasSum_pi_single ..).summable); intro v y u; by_cases h:v=0; · subst v; exact (q (Set.mem_image_of_mem _ u)).trans (by rw [Pi.single_eq_same]; exact le_add_of_nonneg_left ((mul_pos hC (income_2 _)).le))
    rw [Pi.single_eq_of_ne h,add_zero]; exact H _ (stemG.mp u.1) (hg u) _ h
 unfold ContinuousWithinAt; rw [← nhdsWithin_inter_of_mem' ht]; exact (he x ⟨h,show c ≤ _ from (by unfold c; linarith [norm_pos_iff.mpr z])⟩).tendsto -- ht orientation s=stemGuard
lemma tuning (z:x≠0): ContinuousWithinAt finale stemGuard x:= by
 have he: ContinuousWithinAt tough stemGuard x:= continuousWithinAt_pi.mpr fun i=> timbre i h z
 unfold finale; exact (continuousWithinAt_const.sub (zen_c.continuousAt.comp_continuousWithinAt he)).mul continuousWithinAt_const -- matrix
omit h
include p
def carillon (k:ℕ)(M:Maj)(x:Bin): Op SpinIdx:= fleece k x • wagon M x
def beat (k:ℕ)(x:Bin): Op SpinIdx:= fleece k x • finale x
private lemma prior(v:ℕ)(f:Bin→ Op SpinIdx)(H:∀ x∈stemGuard,x≠0→ vlow*‖x‖^2*‖f x‖≤1)(x:Bin)(h:x∈stemGuard)(e:k=v+2): ‖fleece k x • f x‖≤ vlow⁻¹*‖x‖^v:=by
 subst k; by_cases z:x=0; · subst x; simp [fleece,zero_pow (by omega: v+2≠0)]; have h:=vpay; positivity
 exact arc_plain _ _ (H x h z)
lemma beating : ContinuousOn (beat k) stemGuard:=by
 intro x h; by_cases t:x=0
 · subst x; have hz:beat k 0=0:=by simp [beat,fleece,zero_pow (by omega:k≠0)]
   unfold ContinuousWithinAt; rw [hz,tendsto_zero_iff_norm_tendsto_zero]; let G(u:Bin):=vlow⁻¹*‖u‖^(k-2); have hg:Continuous G:=by unfold G; fun_prop
   exact squeeze_zero' (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (eventually_mem_nhdsWithin.mono (fun u v=> show ‖beat k u‖≤ G u from prior p _ finale (fun y=>moving) u v (by omega))) (show Tendsto G _ _ from (show G 0=0 from (by simp [G,zero_pow (by omega:k-2≠0)]) ) ▸ (hg.continuousOn _ h : ContinuousWithinAt G stemGuard 0)) -- fun syntax support t
 exact ((fleece_c k).continuousAt.continuousWithinAt).smul (tuning h t)
lemma beating_compact: TendstoUniformlyOn (carillon k) (beat k) mtn stemGuard:=by
 rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (show IsCompact stemGuard from isCompact_closedBall ..), tendstoLocallyUniformlyOn_iff_forall_tendsto]; intro x h; let u:=mtn ×ˢ (𝓝[stemGuard] x); let U:=Op SpinIdx; let f:Maj×Bin→Bin:=Prod.snd; let g:Maj×Bin→U:=fun p=> carillon k p.1 p.2; have ht:Tendsto f u (𝓝[stemGuard] x):=tendsto_snd
 have hz:Tendsto g u (𝓝 (beat k x)):=by
    by_cases t:x=0
    · subst x; let G(u:Bin):=vlow⁻¹*‖u‖^(k-2); have hG:Continuous G:=by unfold G; fun_prop
      rw [show beat k 0=0 from (by simp [beat,fleece,zero_pow (by omega:k≠0)]),tendsto_zero_iff_norm_tendsto_zero]; exact squeeze_zero' (Filter.Eventually.of_forall fun _=>norm_nonneg _) ((ht.eventually eventually_mem_nhdsWithin).mono (fun i u=> show ‖g i‖≤ (G∘f) i from prior p _ _ (fun _ h=>disk_wagon h (i.1)) (f i) u (by omega))) (show Tendsto (G∘f) _ _ from (show G 0=0 from (by simp [G,zero_pow (by omega:k-2≠0)])) ▸ ((hG.continuousOn _ h).tendsto.comp ht)) -- tune binder and subst
    exact (((fleece_c k).continuousOn _ h).tendsto.comp ht).smul (imports h t (show Tendsto Prod.fst u mtn from tendsto_fst) ht)
 exact ((((beating p _ h).tendsto).comp ht).prodMk_nhds hz).mono_right (nhds_le_uniformity _) -- h used infer
omit p
lemma artP (x:Bin) : beat k x 2 0=fleece k x*arc x:=by rw [beat, Matrix.smul_apply,finale_20]; rfl
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms beating
#print axioms beating_compact
#print axioms artP
#print axioms timbre
