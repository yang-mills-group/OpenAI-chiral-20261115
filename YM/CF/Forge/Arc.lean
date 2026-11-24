import YM.CF.Forge.Pot
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open Jet
variable {A F E H α:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup H][NormedSpace ℝ H][TopologicalSpace α]
def wakeB (K:Finset (Bond c)): Directions G c→L[ℝ]Directions G c:= ContinuousLinearMap.pi fun i=>if i∈K then ContinuousLinearMap.proj i else 0
lemma steadyB (K:Finset (Bond c))(x:Directions G c)(i:Bond c):wakeB K x i=if i∈K then x i else 0:=by simp only [wakeB,ContinuousLinearMap.pi_apply]; split <;> rfl
def gyrate(I: Finset (Bond c))(U:Config G c) : Directions G c→ Config G c:= increment U ∘ wakeB I
lemma born(I:Finset (Bond c))(U:Config G c): gyrate I U 0=U:=by simp [gyrate]
lemma stickU(I:Finset (Bond c))(U:Config G c): Continuous (gyrate I U):= by unfold gyrate increment; fun_prop
variable {N:Type} [NormedAddCommGroup N][NormedSpace ℝ N]{I:Finset (Bond c)}{n:ℕ}
def Arbor (W:Set (Config G c))(f:α→ Config G c→ N)(I: Finset (Bond c))(n:ℕ)(C:ℝ):Prop:=∀ U:Config G c,U∈ W → ∀ t:α, Warm (fun t=>f t ∘ gyrate I U) n (t,0) ∧ Allows n (f t ∘ gyrate I U) 0 C
namespace Arbor
variable {W:Set (Config G c)}{f g:α→ Config G c→N}{C R D:ℝ}{K:Finset (Bond c)}
private def rote (I:Finset (Bond c))(x y:Directions G c): Directions G c:= fun i=> Lyre.gust G (wakeB I x i) (wakeB I (y-x) i)
private lemma shifty(G:Gauge)(I:Finset (Bond c))(x:Directions G c) : rote I x x=0 ∧ ContDiffAt ℝ (↑n) (rote I x) x:=by
 refine ⟨funext fun i=> ?_, contDiffAt_pi.mpr fun i=>?_⟩
 · unfold rote; rw [sub_self,map_zero]; exact (wander G _).1
 let g(y:Directions G c):= wakeB I (y-x) i; have hp:g x=0:=by unfold g; rw [sub_self,map_zero]; rfl
 exact ((show ContDiffAt ℝ ω _ (g x) from hp.symm ▸ (wander G (wakeB I x i)).2.2).of_le le_top).comp (f:=g) x (by unfold g; fun_prop)
private lemma matchQ(U: Config G c)(x:Directions G c): gyrate I U=ᶠ[𝓝 x] fun y=>gyrate I (gyrate I U x) (rote I x y):=by
 let H:= wakeB (G:=G) I
 have ht(i):∀ᶠ y in 𝓝 x,gyrate I U y i=gyrate I (gyrate I U x) (rote I x y) i:=by
    let a(y:Directions G c):=H (y-x) i; have he:a x=0:=by unfold a; rw [sub_self,map_zero]; rfl
    have hn:Tendsto a (𝓝 x) (𝓝 0):=by rw [←he]; exact (show Continuous a by unfold a; fun_prop).continuousAt
    filter_upwards [hn.eventually (Lyre.slip (H x i))] with y hy
    unfold gyrate Function.comp increment; by_cases g:i∈I; swap; · simp_rw [steadyB,if_neg g]; simp
    rw [steadyB I (rote I x y),if_pos g]; have hp: H x i+a y=H y i:=by unfold a; rw [map_sub,Pi.sub_apply,add_sub_cancel]
    rw [hp] at hy; change G.lieExp (H y i)*_= G.lieExp _*_; rw [hy,mul_assoc]; rfl
 filter_upwards [eventually_all.mpr ht] with y ht using funext ht
private lemma matchCost (G:Gauge)(I:Finset (Bond c))(R:ℝ)(n:ℕ):∃ D:ℝ,0≤D∧∀ x∈ Metric.ball (0:Directions G c) R, Allows n (rote I x) x D:=by
 let f(x:Directions G c × Directions G c):=rote I x.1 x.2; have he(x:Directions G c):ContDiffAt ℝ (↑n) f (x,x):=by
    refine contDiffAt_pi.mpr fun i=>?_ ; let p(y:Directions G c × Directions G c):=(wakeB I y.1 i, wakeB I (y.2-y.1) i); have hp:p (x,x)=(wakeB I x i,0):=by simp [p]
    exact (hp.symm ▸ ((wander G (wakeB I x i)).2.1.of_le le_top)).comp (f:=p) _ (by unfold p; fun_prop)
 have hw(i:Fin (n+1)):Continuous (fun x:Directions G c=>‖iteratedFDeriv ℝ (i:ℕ) (rote I x) x‖):=by
    apply continuous_iff_continuousAt.mpr; intro x; have hp:= ((Warm.together (he x)).light i (Nat.lt_succ_iff.mp i.isLt)).norm.comp (f:=fun (x:Directions G c)=>(x,x)) (ContDiffAt.continuousAt (n:=(↑n:WithTop ℕ∞)) (𝕜:=ℝ) (by fun_prop)); exact hp
 choose Z H using fun i=> (isCompact_closedBall (0:Directions G c) R).bddAbove_image (hw i).continuousOn
 let D:= ∑ i,|Z i|; refine ⟨D,(by unfold D; positivity),fun i l=>⟨(shifty _ _ _).2,fun n k=> ?_⟩⟩; let v:= (⟨n,Nat.lt_add_one_iff.mpr k⟩:Fin _); refine (H v (Set.mem_image_of_mem _ (ball_subset_closedBall l))).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=>|Z i|) (fun i _=>abs_nonneg _) (mem_univ v)))
lemma laurel (h:Arbor W f I n C)(U:Config G c)(x:Directions G c)(p:gyrate I U x∈ W)(t:α):Warm (fun v=> f v ∘ gyrate I U) n (t,x):=by
 let y:=rote I x; have he:= shifty (n:=n) G I x; apply (((Warm.simple y he.2).move (V:=fun v=>f v ∘ gyrate I (gyrate I U x)) ?_)).part -- tune syntax
 · filter_upwards [continuousAt_snd.tendsto.eventually (matchQ (I:=I) U x)] with i hi; exact congrArg (f i.1) (hi.symm)
 change Warm _ n (t,y x); rw [show y x=0 from he.1]; exact (h _ p t).1
lemma lime (G:Gauge)(I:Finset (Bond c))(n:ℕ)(r C:ℝ)(hp:0 ≤ C):∃ D:ℝ,0 ≤ D∧∀{W:Set (Config G c)}(f:α→ Config G c→ E),Arbor W f I n C→∀ t U x, gyrate I U x∈W→x∈Metric.ball 0 r→ Allows n (f t ∘ gyrate I U) x D:=by
 obtain ⟨b,hb,H⟩:=matchCost G I r n; refine ⟨composeCost n C b,?_ ,fun f h t U x p v=>?_⟩ -- implicit W
 · unfold composeCost; positivity
 apply Allows.germ (( (show Allows n (f t ∘ gyrate I (gyrate I U x)) (rote I x x) C by rw [(shifty (n:=n) G I x).1]; exact (h _ p t).2)).comp (H x v)); exact (matchQ U x).mono fun z hz=> congrArg (f t) hz.symm
lemma part(h:Arbor W f I n C)(ha:IsOpen W)(v:∀ t,Set.EqOn (f t) (g t) W):Arbor W g I n C:=by
 intro U t i; have hx:= (stickU I U).continuousAt (x:=0) |>.eventually (ha.mem_nhds (show gyrate I U 0∈W from (born I U).symm ▸ t)); obtain ⟨hp,hh⟩:=h _ t i; refine ⟨hp.part ?_,hh.germ (hx.mono fun y p=>v i p)⟩; filter_upwards [continuousAt_snd.eventually hx] with u he using v u.1 he
lemma lowB(h:Arbor W f I n C)(p:K⊆I)(g:0≤ D)(l:D≥composeCost n C 1) : Arbor W f K n D:=by
 have he(U:Config G c):gyrate K U=gyrate I U ∘ wakeB K:=by
    funext x; apply congrArg (increment U); funext i; simp_rw [steadyB]; by_cases g:i∈K; simp [g,p g]; simp [g]
 intro U p t; obtain ⟨ht,H⟩:= h _ p t; rw [he]; let L:= wakeB (G:=G) K; have hx := (show L 0=0 from map_zero ..)
 refine ⟨(show Warm (fun _:α=>⇑L) n (t,0) from Warm.simple _ L.contDiff.contDiffAt).move (V:=fun v=> f v ∘ gyrate I U) (hx.symm ▸ ht),((( (show Allows n _ (L 0) C from hx.symm ▸ H)).comp (allows_linear (L:=L) ?_ ?_)).mono l)⟩
 · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j=> by unfold L; rw [steadyB,one_mul]; split; exact norm_le_pi_norm _ _; rw [norm_zero]; exact norm_nonneg _
 rw [map_zero,norm_zero]; norm_num
end Arbor
end YM.CF.Forge
