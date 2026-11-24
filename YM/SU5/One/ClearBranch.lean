import VerifiedSatinSelectedSectors

/-!
# On the actual bare stencil support the last advancement uses continuous branches

Step likelihood/prediction may not be globally continuous. Need a geometric
lemma uniform in torus sizes. Small *plaquette* chord buys openness in the
cover topology. Proof includes the max-distance/wrap cases by working only
in the cover. No global torus flattening claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.OneRegulator

open Lattice Wilson Pressure Function Filter Set Finset MeasureTheory RG Axial Patch
open scoped Topology BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side}

lemma pureGauge {U : CoverConfig G} (h : ∀ p: Face ℤ,G.chord (faceValue U p) ≤ 0) :
    ∃ t : Cover→G.El,Lattice.gauge t (1:CoverConfig G)=U := by
  let l:= allAxes (1:Lattice.Order)
  let a:= traveller l U 0
  have hall : Lattice.gauge a U=1:= by
    funext ⟨x,i⟩
    let d:= (univ:Finset Axis).sup (fun j=>(x j).natAbs); let n:=d+1
    have hh(j:Axis): (x j).natAbs ≤ d:= Finset.le_sup (s:=Finset.univ) (f:=fun j:Axis=>(x j).natAbs) (Finset.mem_univ j)
    have hs : slab n 0 l=Lattice.box n:=by
      ext x; simp only [slab_iff]; exact ⟨And.left,fun w=> ⟨w,fun i t=> False.elim (t (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))⟩⟩
    have hv : x∈slab n 0 l:=by
       rw [hs,Lattice.box_test]; constructor <;> intro i <;> specialize hh i <;> omega
    have hu : x+step i∈slab n 0 l:=by
       rw [hs,Lattice.box_test]; constructor <;> intro j <;> specialize hh j <;> simp only [Pi.add_apply,step_apply] <;> split <;> omega
    have h0:=Planned.AtomRegular.Foliage.Cube.variation_plane U (w:=0) (by norm_num) (fun i _ p=>h (i,p)) l ((List.nodup_finRange _).map (1:Lattice.Order).injective) x hv i hu
    let v:=Lattice.gauge a U (x,i)
    change G.chord v ≤ _*_*0 at h0; rw [mul_zero] at h0
    have he:= le_antisymm h0 (G.chord_nonneg _); unfold Gauge.chord at he
    rw [div_eq_zero_iff] at he
    apply G.mat_injective; rw [Pi.one_apply,Gauge.mat_one]; exact sub_eq_zero.mp (norm_eq_zero.mp (he.resolve_right (Real.sqrt_pos.mpr (by exact_mod_cast G.dimPos)).ne'))
  refine ⟨a⁻¹,?_⟩
  rw [←hall]; funext ⟨v,i⟩; simp [Lattice.gauge,mul_assoc]

private def delta (P : Patch) (i : Axis) : Cover:= P.L.val • step i
private def shift (P : Patch) (i : Axis) (U : CoverConfig G) := translate (delta P i) U
private def deck (P : Patch) (K : KernelChoices) (i : Axis) (U : CoverConfig G) (x y : P.FrameTag) : P.Connector G :=
  fun j=> P.frame K U x j * travel U j.val (List.replicate P.L.val (posDir i)) *
     (P.frame K (shift P i U) y j)⁻¹

private lemma equals_deck (S : StepData c f) (u : Site c) (U : Config G f) (t : S.SitesChoice) (i : Axis) :
    S.connector U t (u,i) = deck S.patch S.kernel i (expandAt (S.ratio.embed u) U) (t u) (t (u+step i)):= by
  have he : expandAt (S.ratio.embed (u+step i)) U=shift S.patch i (expandAt (S.ratio.embed u) U):=by
    rw [StepData.leap]
    funext ⟨x,a⟩; simp only [shift,Lattice.translate,expandAt,delta,map_add,map_nsmul,wrap_step]; congr 2; abel
  funext x; unfold deck StepData.connector StepData.frames; dsimp only; rw [he]

private lemma work (P : Patch) (i : Axis) (t : Cover→G.El) :
    shift P i (Lattice.gauge t 1) = Lattice.gauge (fun x=>t (x+delta P i)) 1:= by
  funext ⟨y,a⟩; simp only [shift,Lattice.translate,Lattice.gauge,Pi.one_apply]; rw [add_right_comm y]

private def Admissible (P : Patch) (K : KernelChoices) (X : CoverConfig G) : Prop:=
  P.usesMin K X ∧ (∀ i : Axis,P.usesMin K (shift P i X)) ∧
    (∀ i x y,P.usesBest K (deck P K i X x y))

private lemma stay_id (w : Walk) (x : Cover) : travel (1:CoverConfig G) x w=1:=by
  induction w generalizing x <;> simp_all [travel,Step.read]

private lemma goldMin (P : Patch) (K : KernelChoices) : P.usesMin K (1:CoverConfig G):=by
  intro l k x y
  simp only [Patch.via,Patch.axial, stay_id,inv_one,mul_one,G.chord_one]; exact K.frame_cut_pos

private lemma min_frame (P : Patch) (K : KernelChoices) (a : P.Branches K G) (x : P.FrameTag) : P.frame K (1:CoverConfig G) x=1:= by
  unfold Patch.frame; rw [if_pos (goldMin P K)]
  refine (a.frame_unique _ (goldMin P K)).unique (P.min_exists _).choose_spec ?_
  refine ⟨rfl,fun v _=>?_⟩
  have ht(z : P.Points)(x : P.Points)(l : Lattice.Order) : 0 ≤ G.price (P.via v (1:CoverConfig G) z x l):=(G.price_range _).1
  have he {I : Type} [Fintype I] (f : I → ℝ) (h : ∀ i,0 ≤ f i) : 0 ≤ average f:= mul_nonneg (by positivity) (sum_nonneg (fun i _=>h i))
  unfold score; simp only [via,Pi.one_apply,mul_one,inv_one,stay_id,G.price_one]
  change average (fun _ : P.Points=> average (fun _ : P.Points=> average (fun _ : Lattice.Order=> (0:ℝ)))) ≤ _
  rw [show average (fun _ : P.Points=> average (fun _ : P.Points=> average (fun _ : Lattice.Order=> (0:ℝ))))=0 from (by simp [Patch.average])]
  refine he _ (fun z=> he _ (fun u=> he _ (fun i=>?_)))
  simpa only [via, Pi.one_apply,inv_one,mul_one,stay_id] using ht z u i

private lemma deck_of_flat (P : Patch) (K : KernelChoices) (a : P.Branches K G) (t : Cover→G.El)
    (i : Axis) (x y : P.FrameTag) : deck P K i (Lattice.gauge t 1) x y= fun _=> t 0*(t (delta P i))⁻¹ := by
  have hx(j:Cover): stop j (List.replicate P.L.val (posDir i))=j+delta P i:=by
    let S:StepData 1 ((1:Side)*P.L):= ⟨P,K,rfl⟩; exact S.stop_repath i j
  funext m; unfold deck
  rw [work,(P.frame_gauged a t ..).2, (P.frame_gauged a (fun x=> t (x+delta P i)) ..).2, min_frame P K a x,min_frame P K a y]
  unfold Patch.changed; dsimp only; rw [travel_gauge,stay_id,hx,show P.center.val=0 from rfl,zero_add]; simp [mul_assoc]

private lemma flat_good (P : Patch) (K : KernelChoices) (a : P.Branches K G) {U : CoverConfig G}
    (h : ∀ v: Face ℤ,G.chord (faceValue U v) ≤ 0) : Admissible P K U:= by
  obtain ⟨t,rfl⟩:= pureGauge h
  refine ⟨(P.min_gauged _ _ _).mpr (goldMin P K),fun i=> by rw [work]; exact (P.min_gauged _ _ _).mpr (goldMin P K),fun i x y=>?_⟩
  rw [deck_of_flat P K a t]; apply lt_of_le_of_lt ((P.bond_min _).choose_spec (t 0*(t (delta P i))⁻¹))
  simpa [Patch.bondCost] using K.predictor_cut_pos

private lemma admissible_open (P : Patch) (K : KernelChoices) (h : P.Branches K G) (U : CoverConfig G)
    (a : Admissible P K U) : ∀ᶠ V : CoverConfig G in 𝓝 U, Admissible P K V:= by
  have he(X : CoverConfig G)(x:P.FrameTag)(ht : P.usesMin K X): ContinuousAt (fun u:CoverConfig G=>P.frame K u x) X:=by
    have hp: ∀ᶠ u : CoverConfig G in 𝓝 X, P.usesMin K u:= P.min_open.mem_nhds ht
    exact ((P.selected_cont h).continuousAt hp).congr (hp.mono (fun u hu=> Eq.symm (if_pos hu)))
  have hs(i:Axis): ContinuousAt (fun u:CoverConfig G=>shift P i u) U:=by exact continuousAt_pi.mpr (fun j=> (continuous_apply (A:=fun _ : Edge Cover=> G.El) (j.1+delta P i,j.2)).continuousAt)
  have hx(i:Axis) (x y:P.FrameTag) : ContinuousAt (fun u:CoverConfig G=>deck P K i u x y) U:=by
    refine continuousAt_pi.mpr fun j=>?_ ; unfold deck
    exact (((continuous_apply j).continuousAt.comp (he U x a.1)).mul (continuous_travel (G:=G) _ j.val).continuousAt).mul (((continuous_apply j).continuousAt.comp ((he _ y (a.2.1 i)).comp (hs i))).inv)
  exact (show ∀ᶠ u in 𝓝 U,P.usesMin K u from P.min_open.mem_nhds a.1).and ((eventually_all.mpr fun i : Axis=> (hs i).eventually (show ∀ᶠ u : CoverConfig G in 𝓝 (shift P i U),P.usesMin K u from P.min_open.mem_nhds (a.2.1 i))).and (eventually_all.mpr (fun i=> eventually_all.mpr (fun x=> eventually_all.mpr (fun y=> (hx i x y).eventually (show ∀ᶠ u : P.Connector G in 𝓝 (deck P K i U x y),P.usesBest K u from P.best_open.mem_nhds (a.2.2 i x y)))))))

private lemma uniform (P : Patch) (K : KernelChoices) (h : P.Branches K G)
    {t:ℕ→ℝ} (p:Tendsto t atTop (𝓝 0)) : ∀ᶠ s in atTop, ∀ u:CoverConfig G,
    (∀ i:Face ℤ,G.chord (faceValue u i) ≤ t s)→ Admissible P K u:= by
  by_contra! g
  -- use bigger sequence n≥ i
  have hy (m:ℕ):∃ s:ℕ,m ≤ s ∧ ∃ u:CoverConfig G,(∀ i:Face ℤ,G.chord (faceValue u i) ≤ t s) ∧ ¬ Admissible P K u:=by
    exact frequently_atTop.mp g m
  choose s b u a w using hy
  obtain ⟨z,f,q,v⟩:= CompactSpace.tendsto_subseq u
  have ht': Tendsto (t∘s∘f) atTop (𝓝 0):= p.comp ((tendsto_atTop_mono b tendsto_id).comp q.tendsto_atTop)
  have hz(i):G.chord (faceValue z i)≤0:=by
    let F (U:CoverConfig G):=G.chord (faceValue U i); have H:Continuous F:=by unfold F faceValue; fun_prop
    exact le_of_tendsto_of_tendsto' ((H.tendsto _).comp v) ht' (fun j=> a _ i)
  obtain ⟨j,e⟩:= (v.eventually (admissible_open P K h z (flat_good P K h hz))).exists; exact w (f j) e

lemma quiet_branch (P : Patch) (K : KernelChoices) (h : P.Branches K G) {t:ℕ→ℝ} (p:Tendsto t atTop (𝓝 0)) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S:StepData c f), S.patch=P → S.kernel=K →
      ∀ u:Config G f, (∀ i: Face (Per f), G.chord (faceValue u i) ≤ t s) →
        (∀ x : Site c, S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) u)) ∧
       (∀ v : S.SitesChoice,∀ e : Edge (Site c), S.patch.usesBest S.kernel (S.connector u v e)):= by
  filter_upwards [uniform P K h p] with s q
  rintro c f ⟨P',K',hf⟩ rfl rfl u hu
  let S:StepData c f:= ⟨P',K',hf⟩
  have hx(i:Site c) : Admissible P' K' (expandAt (S.ratio.embed i) u):=q _ (by
    rintro ⟨x,y⟩; unfold faceValue; rw [travel_at]; exact hu (_,y))
  refine ⟨fun i=> (hx i).1,fun v i=>?_⟩; obtain ⟨e,i⟩:=i
  change S.patch.usesBest S.kernel (S.connector u v (e,i)); rw [equals_deck]; exact (hx e).2.2 ..

section piece
variable (S : StepData c f) (h : S.patch.Branches S.kernel G)
      (x : Config G f)
      (p : ∀ i : Site c,S.patch.usesMin S.kernel (expandAt (S.ratio.embed i) x))
      (q : ∀ v : S.SitesChoice,∀ e : Edge (Site c),S.patch.usesBest S.kernel (S.connector x v e))
include p
private lemma min_nh (i) : ∀ᶠ u:Config G f in 𝓝 x,S.patch.usesMin S.kernel (expandAt (S.ratio.embed i) u):=by
  have hx(i : Site c) : Continuous (fun x:Config G f=>expandAt (S.ratio.embed i) x):=by unfold expandAt; fun_prop
  exact ((hx i).tendsto _).eventually (show ∀ᶠ u:CoverConfig G in 𝓝 (expandAt (S.ratio.embed i) x), S.patch.usesMin S.kernel u from S.patch.min_open.mem_nhds (p i))
include h
private lemma hConnect(t:S.SitesChoice)(e:Edge (Site c)) : ContinuousAt (fun u=> S.connector u t e) x:= by
  have hx(i : Site c) : Continuous (fun x:Config G f=>expandAt (S.ratio.embed i) x):=by unfold expandAt; fun_prop
  have hF(t:S.SitesChoice)(i:Site c):ContinuousAt (fun u=> S.frames u t i) x:=
    (((S.patch.selected_cont h).continuousAt (s:=_) (S.patch.min_open.mem_nhds (p i))).comp (hx i).continuousAt).congr ((min_nh S x p i).mono fun x p=> Eq.symm (show S.patch.frame S.kernel (expandAt _ x) _= _ from if_pos p))
  apply continuousAt_pi.mpr
  intro j
  unfold StepData.connector
  exact (((continuous_apply j).continuousAt.comp (hF t e.1)).mul ((continuous_travel (G:=G) _ j.val).continuousAt.comp (hx e.1).continuousAt)).mul (((continuous_apply j).continuousAt.comp (hF t _)).inv)

include q
private lemma best_nh(v : S.SitesChoice)(i : Edge (Site c)) : ∀ᶠ u:Config G f in 𝓝 x,S.patch.usesBest S.kernel (S.connector u v i):=
    (hConnect S h x p v i).eventually (show ∀ᶠ u:S.patch.Connector G in 𝓝 (S.connector x v i),S.patch.usesBest S.kernel u from S.patch.best_open.mem_nhds (q v i))

private lemma predict_near(t:S.Choices): ContinuousAt (fun u=> S.prediction u t) x:=by
     apply continuousAt_pi.mpr
     intro j
     apply ContinuousAt.congr (f:= fun u => S.patch.best (S.connector u t.1 j)) (((S.patch.best_cont h).continuousAt (S.patch.best_open.mem_nhds (q t.1 j))).comp (x:=x) (f:=fun u=>S.connector u t.1 j) (hConnect S h x p t.1 j))
     exact (best_nh S h x p q t.1 j).mono fun u p=> Eq.symm (show S.prediction u t j= S.patch.best _ from if_pos p)
private lemma pay_near(t:S.Choices): ContinuousAt (fun u:Config G f=> S.likelihood u t) x:=by
     unfold StepData.likelihood
     have ha(i: Site c): ContinuousAt (fun u:Config G f=> S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) u) (t.1 i)) x:=
       continuousAt_const.congr ((min_nh S x p i).mono fun x p=> Eq.symm (show _ from if_pos p))
     have hb(j : Edge (Site c)): ContinuousAt (fun u:Config G f=> S.patch.predictorMass S.kernel (S.connector u t.1 j) (t.2 j)) x:=
       continuousAt_const.congr ((best_nh S h x p q t.1 j).mono fun x p=> Eq.symm (show _ from if_pos p))
     apply ContinuousAt.mul
     · exact tendsto_finsetProd (f:=fun i u=>S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) u) (t.1 i)) _ fun i _=> (ha i).tendsto
     exact tendsto_finsetProd (f:=fun j (u:Config G f)=> S.patch.predictorMass S.kernel (S.connector u t.1 j) (t.2 j)) _ fun j _=> (hb j).tendsto
end piece
/-- Here continuity in the *fine* field is essential. The kernel assumed
in this application has no such hypothesis globally. -/
theorem density_here (S : StepData c f) (h : S.patch.Branches S.kernel G)
    (β : ℝ) (x : Config G f) (y : Config G c)
    (p : ∀ i : Site c,S.patch.usesMin S.kernel (expandAt (S.ratio.embed i) x))
    (q : ∀ v : S.SitesChoice,∀ e : Edge (Site c),S.patch.usesBest S.kernel (S.connector x v e)) :
    ContinuousAt (fun u:Config G f=> S.density β u y) x:= by
  let V (t:S.Choices) (u : Config G f):= S.likelihood u t * S.noise β (S.prediction u t) y
  have ht(t): ContinuousAt (V t) x:=by
    unfold V
    let X : ContinuousAt (fun u : Config G f=>(S.prediction u t,y)) x:= (predict_near S h x p q t).prodMk continuousAt_const
    have hv : ContinuousAt (fun u : Config G f=> S.noise β (S.prediction u t) y) x:=
      (S.noise_cont (G:=G) β).continuousAt.comp (x:=x) (f:=fun u=>(S.prediction u t,y)) X
    exact (pay_near S h x p q t).mul hv
  exact tendsto_finsetSum (f:=V) (a:=fun i=>V i x) Finset.univ fun i _=>(ht i).tendsto
end YM.OneRegulator
