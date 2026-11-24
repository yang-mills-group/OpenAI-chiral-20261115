import YM.SU5.FiniteGaugeData.Hierarchy.Edging

/-! # Menu for the push kernel. Part I

We didn't assume cross-period *identical* draws. Use exact `Satin.triangle` on the 
Haven promise as granted. Though the mixture weights on the Hall may not match across
periods, this proves a common Borel questions property for the entire operator value 
varying over the fine support input.  Crucial that the (different) mixture over all the
predictor choices uses discrete weights in the actual Step calculation.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Fiber
open VolumeCape

section accounting
variable {S T:Finset Cover}{C N P:Side}(K:ℕ→ℝ){G:Ratio N P}{A:StepData (More N) (More P)} (B:A.patch.Branches A.kernel SU.group)
variable {j:ℕ}{Q:Op SU.Slot}{M:Male}{ho:Odd G.count.val}{e:ℝ}(q:Chi)(β:ℝ)(l:Loom N)(D:ℕ)(v:LaurentRadius j G.count D)(r:0<e)(y:2*e<firstRadius SU.group)
variable (μ:Measure (Read.Wor (More N) C))[IsProbabilityMeasure μ](w:∀ x:Pane N,(depot N).map (fun z=>l (x,z))=((VolumeCape.Borel.Aerial.valsf N).prod μ).map (Dream.sceneQ C K N x))
variable {b:Bool}(L:Mark N)(g:AtSupport b (region S N) L)(h: S⊆T)(hv:halo (Advance.nearZero D) (region S N)⊆ region T N)(p: Tipping T N C)(c:Measurable l)

def centerPanel (C:Side)(K:ℕ→ℝ)(G:Ratio N P)(A:StepData (More N) (More P))(T:Finset Cover)(j:ℕ)(Q:Op SU.Slot)(M:Male)(ho:Odd G.count.val)(q:Chi)(e β:ℝ) (L:Mark N) (W:Fields P)(U:A.Choices)(s:Courses C T) (x:Hall C T):FC (Single P) :=
  let u:= replant T N (Common.pairs C K T s x)
  mist C T A β (A.prediction W.1 U ∘ stretch (porch C T) N) x.1 • gathered G j Q M ho q e L W u

include v g r y
lemma center_panel_envelope (s:Courses C T) (U:A.Choices) (W:Fields P): Envelope (centerPanel C K G A T j Q M ho q e β L W U s):= Girt.kitE _ _ (fun (a:ℂ) (v:FC (Single P))=>a • v) (by exact continuous_fst.smul continuous_snd)
 (Envelope.compactC ((mist_c C T A).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))))
 (Env.along (g:=fun x=>(W,replant T N (Common.pairs C K T s x))) (env_gathered G j Q M ho q e v r y L g.env) (measurable_const.prodMk ((replant_b T N).comp (pairs_m C K T _))))
include B h hv w c p
lemma push_offer (W:Fields P): pushMark G A j Q M ho q e β l L W =
    ∑ i:A.Choices,A.likelihood W.1 i • ∫ a, (∫ x,centerPanel C K G A T j Q M ho q e β L W i (chooseCourse C T N a) x∂ law C T)∂μ:=by
  let Z(V:Fields N):=gathered G j Q M ho q e L W V
  have he:Envelope Z:=Env.along (g:=Prod.mk W) (env_gathered G j Q M ho q e v r y L g.env) (measurable_const.prodMk measurable_id)
  let t: Orbit N→FC (Single P):= Z ∘ drawn l; let n(i:A.Choices)(x':Orbit N):ℝ:=A.noise β (A.prediction W.1 i) x'.1
  have m (i:A.Choices):Envelope (n i):= Env.along (g:=Prod.fst) (show Envelope (fun x':Pane N=> A.noise β (A.prediction W.1 i) x') from Env.compact (by unfold StepData.noise StepData.penaltyWeight; fun_prop)) measurable_fst
  have tt(i:A.Choices):Integrable (fun z=> n i z • t z) (city N):= Env.integrableX (Env.scale (m i) (Env.along he (drawn_m l c))) _
  rw [outright G A j Q M ho q e β l v c B r y _ g.env]; let Y(i):ℝ:= A.likelihood W.1 i
  change (∫ z:Orbit N,(∑ i:A.Choices,Y i*n i z) • t z ∂city N)=_
  simp_rw [Finset.sum_smul, mul_smul]; rw [integral_finsetSum]; swap; · intro i _; exact (tt i).smul (Y i)
  simp_rw [integral_smul]; refine sum_congr rfl fun i _=>?_ ; apply congrArg (fun v:FC (Single P)=> Y i • v)
  simp_rw [← Complex.coe_smul] -- also alter ..? inside centerPanel no
  apply Satin.triangle C K T N l c w P Z he _ A β (A.prediction W.1 i) p
  intro x y p e'; exact gather_dep G j Q M ho q e v _ g W W (fun _ _ _=>rfl) x y (agrees_mono p (image_subset_image h)) (agrees_mono e' hv)
#print axioms center_panel_envelope
#print axioms push_offer
end accounting

section menu
variable {I X:Type*}[MeasurableSpace X]{N P:I→Side} (T:Finset Cover)(L:Patch)(K:KernelChoices)
  (b:L.Branches K SU.group)(s:∀i, (P i).val=(N i).val*L.L.val)
local notation "G" => bead N L.L P s

abbrev keystone {n l m:ℕ} (t:l=n*m): l*2=(n*2)*m:=by rw [t,mul_right_comm]
abbrev pegged {I:Type*}{N P:I→Side}(L:Patch)(K:KernelChoices)(s:∀i,(P i).val=(N i).val*L.L.val)(i:I): StepData (More (N i)) (More (P i)) := Chalk.pinned L K (keystone (s i))
local notation "A"=> pegged L K s
variable (j D:ℕ)(v:LaurentRadius j L.L D)(r:Odd L.L.val)(q:Chi)(e:ℝ)(a:0<e)(u:2*e<firstRadius SU.group)
variable (Q:I→Op SU.Slot)(M:I→ Male)(β:I→ℝ){C' B' :ℝ}(hp:∀i,‖Q i‖≤C')(D':∀i,‖β i‖≤ B')
variable (C:Side)(K':ℕ→ℝ) (W:(i:I)→X→Fields (P i))(hW:Chalk.Fin (fun (i:Σ i:I,Edge (Seat (P i))) x=> (W i.1 x).1 i.2))
  (w':Deal (fun (i:Σ i:I,Edge (Seat (P i))) x=> (W i.1 x).2 i.2))(wm:∀i,Measurable fun x=>(W i x).1)
variable (F:I→ PairsC→ℂ)(H:ℝ)(h:∀ i x,‖F i x‖≤ H)(f:Chorus)

include b hW
omit [MeasurableSpace X] in
private lemma crop_deal (U:(i:I)→ (pegged L K s i).Choices): Chalk.Fin (Y:=rawF C T) (fun i x=> (A i).prediction (W i x).1 (U i) ∘ stretch (porch C T) (N i)) := by
  refine Chalk.collect (V:=fun _ : PoleL C T=> SU.E) ?_
  intro p; exact Chalk.predicts N P L K (fun i=>keystone (s i)) (fun i x=>(W i x).1) (fun y=>Chalk.post hW (fun i:I=>⟨i,y i⟩)) b _ U

include D' wm
set_option synthInstance.maxSize 30000 in
private lemma ticket_m (U:(i:I)→ (pegged L K s i).Choices)(y:I→ Hall C T):
    Menu (I:=I) (T:=fun _=>ℂ) (fun i x=> mist C T (A i) (β i) ((A i).prediction (W i x).1 (U i) ∘ stretch (porch C T) (N i)) (y i).1):=by
  classical
  rcases isEmpty_or_nonempty I with h | t
  · refine Menu.congr (Menu.zero (T:=fun _:I=>ℂ) (X:=X)) (fun i=>?_); exact isEmptyElim (i:I)
  obtain ⟨i⟩:=t; let Z:= (A i)
  let J(i:I)(x:X):rawF C T:= (A i).prediction (W i x).1 (U i) ∘ stretch (porch C T) (N i)
  have z:Deal J:= by
    apply Chalk.deals (crop_deal T L K b s C W hW U); intro i; refine measurable_pi_lambda _ fun t=>?_ ; exact (measurable_pi_apply (X:=fun _ : Edge (Seat (N i))=> SU.E) _).comp (((A i).prediction_meas b (U i)).comp (wm i))
  let t'(i:I)(x:X):ℝ×rawF C T×Hall C T:= (β i,J i x,y i)
  have ht :Deal t':= (Deal.pure (X:=X) (T:=fun _:I=>ℝ) β).prod (z.prod (Deal.pure (X:=X) (T:=fun _:I=>Hall C T) y))
  exact (Menu.clip ht (isCompact_Icc.prod isCompact_univ:IsCompact ((Set.Icc (-B') B') ×ˢ (Set.univ:Set (rawF C T × Hall C T)))) (fun i _=> ⟨abs_le.mp (D' i),Set.mem_univ _⟩) (mist_c C T Z)).congr fun i x=> rfl -- K and penaltyZ definitionally the same with this pegging.

omit b D' wm hW
include h
private lemma scale_k (Y:(i:I)→Fields (N i)) : Menu (I:=I) (T:=fun _=>ℂ) (X:=X) (fun i _=> F i (Prod.map (onC _) (onC _) (Y i))) := Menu.cnst _ (le_max_left 0 H) (fun i=> (h i _).trans (le_max_right 0 H))
include v r a u hp w'
private lemma knot_m (Y:(i:I)→Fields (N i)) : Menu (I:=I) (T:=fun i=> FC (Single (P i)))
    (fun i x=> gathered (G i) j (Q i) (M i) r q e (Satin.knot (N i) f (F i)) (W i x) (Y i)):= by
  refine ((scale_k (X:=X) F H h Y).scale (gather N L.L P s j D v r M Q hp q e a u f W Y w')).congr ?_
  intro i x; unfold gathered before avgF Satin.knot wholeZ; simp_rw [map_smul,← Finset.smul_sum]; exact smul_comm ..
include b D' wm hW
lemma center_menu (R : (i:I)→ (pegged L K s i).Choices)(V:I→ Courses C T)(p':I→Hall C T) :
    Menu (I:=I) (T:=fun i=> FC (Single (P i))) (fun i x=> centerPanel C K' (G i) (A i) T j (Q i) (M i) r q e (β i) (Satin.knot (N i) f (F i)) (W i x) (R i) (V i) (p' i)) :=
    (ticket_m T L K b s β D' C W hW wm R p').scale (knot_m L s j D v r q e a u Q M hp W w' F H h f _)
#print axioms center_menu

abbrev mix (C N:Side):= Read.Wor (More N) C
variable (μ:∀i,Measure (mix C (N i)))[∀i,IsProbabilityMeasure (μ i)]
variable (S:Finset Cover) (v':∀i,AtSupport (Sound.treble f) (region S (N i)) (Satin.knot (N i) f (F i)))
variable (l:∀i,Loom (N i))(r':∀i,Measurable (l i))(hv:∀ (i:I) (V:Pane (N i)), (depot (N i)).map (fun t=>l i (V,t))= ((VolumeCape.Borel.Aerial.valsf (N i)).prod (μ i)).map (Dream.sceneQ C K' (N i) V))

include v'
set_option maxHeartbeats 400000 in
private lemma upper_fleet (R : (i:I)→ (pegged L K s i).Choices) :
    Menu (I:=I) (T:=fun i=> FC (Single (P i))) (fun i x=> ∫ t,(∫ y, centerPanel C K' (G i) (A i) T j (Q i) (M i) r q e (β i) (Satin.knot (N i) f (F i)) (W i x) (R i) (chooseCourse C T (N i) t) y∂Common.law C T)∂ μ i):=by
  let S':= Σ i:I,mix C (N i); let X'(i:S') (x:X)(y:Hall C T):= centerPanel C K' (G i.1) (A i.1) T j (Q i.1) (M i.1) r q e (β i.1) (Satin.knot (N i.1) f (F i.1)) (W i.1 x) (R i.1) (chooseCourse C T (N i.1) i.2) y
  let J:=Σ i:S',Hall C T
  have h'(i:S')(x:X):Integrable (X' i x) (Common.law C T):= Env.integrableX (center_panel_envelope (C:=C) K' («G»:=G i.1) («A»:= A i.1) (ho:=r) q (β i.1) D v a u (Satin.knot (N i.1) f (F i.1)) (v' i.1) (chooseCourse C T (N i.1) i.2) (R i.1) (M:= M i.1) (Q:=Q i.1) (W i.1 x)) _
  refine menu_integral (V:=fun i:I=> mix C (N i)) ?_ μ (fun i x=> Integrable.of_finite)
  refine menu_integral (P:=fun i:S'=> FC (Single (P i.1))) (F':=fun i y x=> X' i x y) ?_ (fun i=> Common.law C T) h'
  let w(i:J):I:=i.1.1
  let n:=N∘w; let p:=P∘w
  have hW':Chalk.Fin (fun (k:Σ i:J, Edge (Seat (p i))) (x:X)=> (W (w k.1) x).1 k.2) := Chalk.post hW (fun v:Σ i:J,Edge (Seat (p i))=> ⟨w v.1,v.2⟩)
  exact center_menu (I:=J) T L K b (N:=n) (P:=p) (fun i=>s (w i)) j D v r q e a u (Q∘w) (M∘w) (β∘w) (fun i=>hp (w i)) (fun i=>D' (w i)) C K' (fun i x=> W (w i) x) hW' (w'.re fun k : (Σ i:J,Edge (Seat (p i)))=> ⟨w k.1,k.2⟩) (fun i=> wm (w i)) (F ∘ w) H (fun i=>h (w i)) f (fun i=>R (w i)) (fun i=> chooseCourse C T (n i) i.1.2) (fun i:J=> i.2)

set_option synthInstance.maxSize 30000 in
set_option maxHeartbeats 400000 in
lemma FineSide (g:S⊆T) (t:∀i,halo (Advance.nearZero D) (region S (N i))⊆region T (N i)) (τ:∀ i,Tipping T (N i) C) (h':∀ i,Dream.Haven C K' (N i) (l i))(m:∀ i,Measurable (l i)) :
    Menu (I:=I) (T:=fun i=>FC (Single (P i))) (fun i x=>pushMark (G i) (A i) j (Q i) (M i) r q e (β i) (l i) (Satin.knot (N i) f (F i)) (W i x)):=by
  let μ'(i:I):Measure (mix C (N i)):= Classical.choose (h' i); haveI hRate(i:I):IsProbabilityMeasure (μ' i):=(Classical.choose_spec (h' i)).1
  have hm(i:I) (x:X):pushMark (G i) (A i) j (Q i) (M i) r q e (β i) (l i) (Satin.knot (N i) f (F i)) (W i x) =
    ∑ z:(A i).Choices, (A i).likelihood (W i x).1 z •∫ t, (∫ w,centerPanel C K' (G i) (A i) T j (Q i) (M i) r q e (β i) (Satin.knot (N i) f (F i)) (W i x) z (chooseCourse C T (N i) t) w∂ Common.law C T)∂ μ' i:= push_offer («G»:=G i) («A»:=A i) (Q:=Q i) (M:=M i) (ho:=r) K' b q (β i) (l i) D v a u (μ' i) (Classical.choose_spec (h' i)).2.2 _ (v' i) g (t i) (τ i) (m i) (W i x) -- shadow t binder okay
  let J:=Σ i:I,(A i).Choices; let w(i:J):I:=i.1; let n:=N∘w; let p:=P∘w
  have hW':Chalk.Fin (fun (k:Σ i:J, Edge (Seat (p i))) (x:X)=> (W (w k.1) x).1 k.2) := Chalk.post hW (fun v:Σ i:J,Edge (Seat (p i))=> ⟨w v.1,v.2⟩)
  let μJ(i:J):Measure (mix C (n i)):= μ' (w i)
  haveI (i:J):IsProbabilityMeasure (μJ i):=hRate (w i)
  simp_rw [hm]
  refine menu_convex (V:=fun i:I=> (A i).Choices) ?_ (fun i t x=> (A i).likelihood_pos (W i x).1 t) (fun i x=> (A i).chosen b (W i x).1) ?_
  · exact upper_fleet (I:=J) T L K b (N:=n) (P:=p) (fun i=>s (w i)) j D v r q e a u (Q∘w) (M∘w) (β∘w) (fun i=>hp (w i)) (fun i=>D' (w i)) C K' (fun i x=> W (w i) x) hW' (w'.re fun k : (Σ i:J,Edge (Seat (p i)))=> ⟨w k.1,k.2⟩) (fun i=> wm (w i)) (F ∘ w) H (fun i=>h (w i)) f μJ S (fun i=> v' (w i)) (fun i:J=> i.2)
  exact Chalk.commonLight n p L K (fun i=> keystone (s (w i))) (fun i x=> (W (w i) x).1) b (fun i=> wm (w i)) Sigma.snd hW'
#print axioms FineSide
end menu
end Fiber
end YM.CF.Buffered.Afterglow.Hierarchy
