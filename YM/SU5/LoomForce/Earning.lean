import YM.SU5.LoomForce.Front
import YM.SU5.LoomForce.Clusters

/-! Physical election at new mixed and CRC gauges. Keep comparator actual Poll on these
entire selected-state costs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Morn Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey Heat
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Jewel Shuttle
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical
variable {I : Type*} [Fintype I] (P:Spine) (K:P.Register) {E:ℝ} {Mc:ℕ} (J:PreparedInvestment P K E Mc)
  (A:ℝ)(tag:I→ Sewer)(L:List I) {r:ℕ} (h:4≤r) {β:ℕ→ℝ}{f:ℕ→ℕ} (U:ℕ→ I → Cover)
  (F:I→ Gaia)(p:0 < A)(Pz:Pooling P.run (takenVolume P) (takenCutoff P) f β)(G:Injective F)
  (v:∀ i, Appoint P.par A (fun s=>U s i) (F i))(ht:L.Nodup)
local notation "Λ" => P.par
local notation "⊠" => P.calibration
local notation "F₀" => Prototype.goldF
local notation "F✚" n:max => (fun i=> gait P.par (F i) n)
local notation "F⚙" n:max => dualC (F✚ n)
local notation "Zα" n:max => kroll P.par A n
local notation "Z" tag:max F:max L:max => inked tag (fun _=>F₀) (fun _=>pairMood) F L
local notation "B_" n:max s:max => forward (U s) Λ A n s
local notation "W" tag:max u:max s:max L:max => onWord P A tag h β s u L
include v p J Pz h G ht
lemma polls_word : WakePoll P (fun s=> W tag (U s) s L) (Z tag F L) := by
  let F₀' := Z tag F L; let Y : I → Gaia := opposite ∘ F; let Z₀ := Z tag Y L; let YP n:= opposite ∘ (F✚ n)
  have hF(i j:I)(h:F i=F j): ∀ᶠ s in atTop, U s i = U s j:= Eventually.of_forall fun _=> congrArg _ (G h)
  let g n:= F✚ n; let b := P.calibration.ℓ; let η := Shuttle.twins L; let T:= Sum.elim tag tag
  let d n:= Z T (F⚙ n) η
  -- pay all those forward tests
  have he(a:I)(n:ℕ) : Appoint P.par A (fun s=> (B_ n s) a) (g n a) := xplus_a p (v a) n
  have hv : L.Pairwise (fun i j=> F i ≠ F j) := List.Pairwise.imp (fun i z=> i (G z)) ht
  have hp : ∀ᶠ n:ℕ in atTop, ∀ i, 0 < (g n i) 3 := Filter.eventually_all.mpr (fun i=> (gait_up Λ (F i)).eventually_gt_atTop 0)
  let B s:= W tag (U s) s L; let BP n s:= W tag (B_ n s) s L; let BM n s:= W tag (fun i => Shuttle.flip ((B_ n s) i)) s L
  have hm(n s:ℕ) : BP n s=P.halfShift 3 ((Zα n) s) (B s):= (onWord_tower ..).symm
  have hw(n s:ℕ) : BM n s = P.reflectTest 3 (BP n s):= (onWord_slide ..).symm
  have hδ : Tendsto (fun s=> P.eReadL s (B s)) atTop (𝓝 F₀') :=
    uptakes P K J A (fun _ => F₀) (fun _=>pairMood) F U p v tag L h Pz hF hv
  have ht0(n:ℕ) : Tendsto (fun s=> P.eReadL s (BP n s)) atTop (𝓝 F₀'):=hδ.congr (fun s=>hm n s ▸ (world_half P s (B s) _).symm) -- Eq.mp?
  have ht'(n:ℕ) : Tendsto (fun s=> P.eReadL s (BM n s)) atTop (𝓝 (star F₀')):= (ht0 n).star.congr (fun i=>hw n i ▸ (world_mirror P i _).symm)
  have hd (n:ℕ){a b:I} : g n a - g n b=F a-F b:= gait_d ..
  have hmP(n:ℕ){a b:I} : YP n a - YP n b= Y a-Y b :=by unfold YP Y; simp only [comp_apply,flip_d, gait_d]
  have jP(n:ℕ): Injective (g n):=fun _ _ h=> G (add_right_cancel h)
  have jM(n:ℕ): Injective (YP n):= flip_inj.comp (jP n)
  have hN : Z₀=star F₀' := by
    obtain ⟨n,w⟩:= hp.exists; let U' s:= Shuttle.flip ∘ B_ n s
    have p':Injective (YP n):=jM n
    have hg (i) : Appoint P.par A (fun s=>U' s i) (YP n i) := xflip_a (he i n)
    have hU(i j:I)(h:YP n i=YP n j): ∀ᶠ s in atTop, U' s i = U' s j:= Eventually.of_forall fun _=> congrArg _ (p' h)
    have q : L.Pairwise (fun i j=> YP n i≠YP n j):= List.Pairwise.imp (fun i z=> i (p' z)) ht
    have hy:= uptakes P K J A (fun _=>F₀) (fun _=>pairMood) (YP n) U' p hg tag L h Pz hU q
    rw [inked_at tag (YP n) Y L (fun i j=> hmP n)] at hy
    exact tendsto_nhds_unique (show Tendsto (fun s=>P.eReadL s (BM n s)) atTop (𝓝 Z₀) from hy) (ht' n)
  -- product moment at heights before target spacing. dual data monotone projection on 3
  have pM(n:ℕ)(u:∀ i,0 < (g n i) 3) : Tendsto (fun s=> P.eReadL s (P.reflectTest 3 (BP n s)* BP n s)) atTop (𝓝 (d n)) := by
    let U' s:= Sum.elim (Shuttle.flip ∘ B_ n s) (B_ n s); let f := dualC (F✚ n)
    obtain ⟨v,p'⟩:= troupe_loan p v hF n u
    have hz (x x':I): f (Sum.inl x) ≠ f (Sum.inr x'):=fun e=>by
      have hr:= congrArg (fun i:Gaia => i 3) e; change opposite (g n x) 3=g n x' 3 at hr; rw [opp_tim] at hr; exact (lt_trans (neg_lt_zero.mpr (u x)) (u x')).ne hr
    have hw: η.Pairwise (fun x y=>f x≠ f y):=by
      apply List.pairwise_append.mpr; refine ⟨List.pairwise_map.mpr ?_, List.pairwise_map.mpr ?_, ?_⟩
      exact List.Pairwise.imp (fun e h=> e (jM n h)) ht
      exact List.Pairwise.imp (fun e h=> e (jP n h)) ht
      intro i p j q; obtain ⟨a,v,rfl⟩:=List.mem_map.mp p; obtain ⟨b,w,rfl⟩:=List.mem_map.mp q; exact hz a b
    let l:= uptakes P K J A (fun _=>F₀) (fun _=>pairMood) f U' p v T η h Pz p' hw
    apply l.congr; intro s; change P.eReadL s (W T (U' s) s η)= _; unfold BP; rw [twoRoll]
  let μ := P.pillars 3; have HX:Tendsto d atTop (𝓝 (star F₀'* F₀')):= by rw [←hN]; exact clusterWake tag Y F YP g L (fun n _ _=> hmP n) (fun n _ _=> hd n) (fun i j=> foreign Λ (F i) (F j))
  refine ⟨fun t h' => ?_⟩
  have hl: Tendsto (fun i=> ‖d i-star F₀'*F₀'‖) atTop (𝓝 0):=by simpa only [sub_self, norm_zero] using (HX.sub_const (star F₀'* F₀')).norm
  obtain ⟨n,q,rn⟩:= ((hl.eventually (gt_mem_nhds h')).and hp).exists
  -- All prices now at this height/traj, no statement of equality on W coords/fields without estimator
  let R s := residualx P s F₀' (BP n s); let E0(s):= P.eReadL s (P.reflectTest 3 (R s)*R s); have ht:Tendsto E0 atTop (𝓝 (d n-star F₀'*F₀')):=by
    have he:= ((((pM n rn).sub ((ht' n).const_mul F₀')).sub ((ht0 n).const_mul (star F₀'))).add_const (F₀'*star F₀')); rw [show d n-F₀'*star _-star _*F₀'+ F₀'*star F₀'=d n-star F₀'*F₀' from ?_] at he; swap; · ring
    refine he.congr (fun s=>?_ ); unfold E0 R; rw [reTest, hw, world_mirror]; ring
  filter_upwards [ht.norm.eventually (gt_mem_nhds q), permit_words P A p L (g n) (fun s=> B_ n s) (he · n) rn (r:=r)] with s u Y
  change (∫ x:P.Spectrum0 3, ‖P.singleState 3 s x (B s)-F₀'‖^2 ∂μ)< _
  simp_rw [← halfAt P s (B s) ((Zα n) s), ← hm]; exact lt_of_le_of_lt (sectorCost P s F₀' (BP n s) (supportedWord ..) Y) u

#print axioms polls_word
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
