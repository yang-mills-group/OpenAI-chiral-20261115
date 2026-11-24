/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Gong
/-! Infinitesimal curved gauge vector in THIS coordinate pricing chart -/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FlightFlux
open AnalyticBridge VerifiedReset Lattice Wilson RG OrderedFinpartition Gauge
open scoped ContDiff Topology InnerProductSpace BigOperators Classical Matrix Matrix.Norms.Frobenius
open Filter Function
variable (G:Gauge){n:Side}
abbrev GaugePay (G:Gauge):=G.Color×G.Color×G.Color
def EchoCost (q:GaugePay G) := G.mat (G.lieExp (-q.1))* G.mat (G.lieExp q.2.1)*star (G.mat (G.lieExp (-q.2.2)))
def EchoLog (q:GaugePay G):=G.plog (EchoCost G q)
lemma Cost_zero: EchoCost G 0=1:=by simp [EchoCost]
lemma Echo_zero: EchoLog G 0=0:=by simp [EchoLog,Cost_zero]
lemma Cost_K:ContDiff ℝ ω (EchoCost G):= ((G.exp_jet.comp (contDiff_fst.neg)).mul (G.exp_jet.comp (contDiff_fst.comp contDiff_snd))).mul ((starL ℝ:G.Mat≃L[ℝ]G.Mat).contDiff.comp (G.exp_jet.comp (contDiff_snd.comp contDiff_snd).neg))
lemma Echo_K:ContDiffAt ℝ ω (EchoLog G) 0:=(show ContDiffAt ℝ ω G.plog (EchoCost G 0) from (by rw [Cost_zero]; exact G.plog_diff)).comp (f:=EchoCost G) 0 (Cost_K G).contDiffAt
lemma Echo_silo: (fun i:G.Color=> EchoLog G (0,i,0))=ᶠ[𝓝 0] (fun i=>i):=by
 filter_upwards [G.plog_left] with x h; unfold EchoLog; rw [show EchoCost G (0,x,0)=_ from ?_]; exact h; simp [EchoCost]
lemma Echo_line (q:GaugePay G): fderiv ℝ (EchoLog G) 0 q=q.2.2 - q.1 +q.2.1:=by
 let f(x:G.Color):=G.mat (G.lieExp x); have he(a:G.Color):HasDerivAt (fun t:ℝ=>f (t • a)) (G.colorMat a) 0:=by exact G.expDiff_zero.comp_hasDerivAt_of_eq (0:ℝ) (show HasDerivAt (fun t : ℝ => t • a) a 0 from by simpa using (hasDerivAt_id' (0:ℝ)).smul_const a) (by simp)
 let A:=q.2.2-q.1+q.2.1
 have hx:HasDerivAt (fun t:ℝ=>EchoCost G (t • q)) (G.colorMat A) 0:=by
    have ht: (fun t:ℝ=>EchoCost G (t • q))= fun t:ℝ=> f (t • -q.1)* f (t • q.2.1)* star (f (t • (-q.2.2))):=by simp [EchoCost,f]
    rw [ht]; apply (((he (-q.1)).mul (he q.2.1)).mul ((he (-q.2.2)).star)).congr_deriv
    unfold A f; simp only [Pi.mul_apply,zero_smul,G.mat_lieExp_zero,G.mat_one,star_one,mul_one,one_mul,G.colorMat_skew,map_add,map_sub,map_neg,star_neg,neg_neg]; abel -- tune
 have h₀: EchoCost G ((0:ℝ) • q)=1:=by rw [zero_smul,Cost_zero]
 have hh:=(G.plog_diff.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hx h₀.symm
 exact ((Push.side _ ((Echo_K G).differentiableAt (by simp)) q).unique hh).trans (MultiNext.SignedSource.Pattern.physical _)
variable {G}
variable (s:Site n → G.Color)
abbrev Lift2 (G:Gauge)(n:Side):= Dir G n×ℝ
def Broad(q:Lift2 G n):Config G n:=gauge (fun x=> G.lieExp (-(q.2 • s x))) (increment 1 q.1)
def slice_G (i:Edge (Site n)):Lift2 G n→L[ℝ]GaugePay G:=
 let X:= ContinuousLinearMap.fst ℝ (Dir G n) ℝ; let P:= ContinuousLinearMap.snd ℝ (Dir G n) ℝ
 (P.smulRight (s i.1)).prod (((ContinuousLinearMap.proj (φ:=fun _ : Edge (Site n) => G.Color) i).comp X).prod (P.smulRight (s (i.1+step i.2))))
def ChordG(q:Lift2 G n):Dir G n:=fun i=> EchoLog G (slice_G s i q)
lemma broad_exp (q:Lift2 G n)(i:Edge (Site n)): G.mat (Broad s q i)=EchoCost G (slice_G s i q):=by unfold Broad Lattice.gauge EchoCost increment; simp only [Pi.one_apply,mul_one,G.mat_mul,G.mat_inv]; rfl
lemma BroadØ: Broad s 0=1:=by funext i; simp [Broad,increment,Lattice.gauge]
lemma Chord_0: ChordG s 0=0:=by funext i; unfold ChordG; rw [map_zero,Echo_zero]; rfl -- tune
lemma chord_K: ContDiffAt ℝ ω (ChordG s) 0:=contDiffAt_pi.mpr fun i=> (show ContDiffAt ℝ ω (EchoLog G) (slice_G s i 0) from (by rw [map_zero]; exact Echo_K G)).comp (f:=slice_G s i) 0 ((slice_G s i).contDiff.contDiffAt)
lemma recouped: (increment 1) ∘ ChordG s =ᶠ[𝓝 0] Broad s:=by
 have he (i : Edge (Site n)) : Tendsto (fun q => Broad s q i) (𝓝 0) (𝓝 1) := by
    rw [← (show Broad s 0 i = 1 by simp [BroadØ])]; have hf: (fun q=> G.mat (Broad s q i))=fun q=> EchoCost G (slice_G s i q):= funext fun q=>broad_exp s q i
    refine (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.tendsto_nhds_iff.mpr ?_
    have ht: Continuous (fun q=> G.mat (Broad s q i)):=by rw [hf]; exact (Cost_K G).continuous.comp (slice_G s i).continuous
    exact ht.tendsto _
 filter_upwards [eventually_all.mpr fun i => (he i).eventually G.plog_right] with q hq
 funext e; change G.lieExp _ * 1 = Broad s q e; rw [mul_one]; unfold ChordG EchoLog; rw [← broad_exp]; exact hq e
lemma chord_stand: ∀ᶠ i in 𝓝 (0:Dir G n), ChordG s (i,0)=i:=by
 have he(k:Edge (Site n)): Tendsto (fun i:Dir G n=>i k) (𝓝 0) (𝓝 0):= (continuous_apply k).tendsto _ -- tune
 filter_upwards [eventually_all.mpr fun i=> (he i).eventually (Echo_silo G)] with v hv
 funext e; rw [ChordG,show slice_G s e (v,0)=(0,v e,0) from ?_]; exact hv e; simp [slice_G]
-- vector derivative
local notation "jet2"=> ((0,1):Lift2 G n)
def earG (x:Dir G n) := fderiv ℝ (ChordG s) (x,0) jet2
abbrev strainG (u:Dir G n) := fderiv ℝ (earG s) 0 u
lemma Chord_line (x:Lift2 G n): fderiv ℝ (ChordG s) 0 x=x.2 • gradient s + x.1:=by
 funext i; let π:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Edge (Site n)=>G.Color) i; let Q:=slice_G s i; have hg: π.comp (fderiv ℝ (ChordG s) 0)= (fderiv ℝ (EchoLog G) (Q 0)).comp Q :=by
    have ht := (π.hasFDerivAt.comp 0 ((chord_K s).differentiableAt (by simp)).hasFDerivAt).unique (( (show DifferentiableAt ℝ (EchoLog G) (Q 0) from (by rw [map_zero]; exact (Echo_K G).differentiableAt (by simp))).hasFDerivAt).comp 0 Q.hasFDerivAt)
    exact ht
 have hx:= DFunLike.congr_fun hg x; rw [map_zero] at hx; change fderiv ℝ (ChordG s) 0 x i= fderiv ℝ (EchoLog G) 0 (Q x) at hx; rw [hx,Echo_line]; simp [VerifiedReset.gradient,Q,slice_G, smul_sub] -- tune
lemma earG_0 : earG s 0= gradient s:=by unfold earG; rw [show ((0,0):Lift2 G n)=0 from rfl,Chord_line]; simp -- tune
lemma earG_d: DifferentiableAt ℝ (earG s) 0:=by
 let H:=fderiv ℝ (ChordG s); let L:=ContinuousLinearMap.inl ℝ (Dir G n) ℝ; have he:ContDiffAt ℝ 1 H (L 0):=(chord_K s).fderiv_right (by simp); exact (he.differentiableAt (by simp) |>.comp 0 L.differentiableAt).clm_apply (differentiableAt_const _)
set_option maxHeartbeats 180000 in
lemma strainG_here (i:Edge (Site n))(u:Dir G n): strainG s u i = iteratedFDeriv ℝ 2 (EchoLog G) 0 ![(0,u i,0),(s i.1,0,s (i.1+step i.2))]:=by
 let Q:=slice_G s i; let π:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Edge (Site n)=>G.Color) i
 let L:=ContinuousLinearMap.inl ℝ (Dir G n) ℝ
 have hP:= ((π.iteratedFDeriv_comp_left (x:=0) (f:=ChordG s) (chord_K s) (i:=2) le_top))
 rw [show π ∘ ChordG s= EchoLog G ∘ Q from rfl, Next.Foundations.jets_linear Q ((Echo_K G).of_le le_top)] at hP
 let A:Lattice.Site n:=i.1; let y:Lift2 G n :=(u,0); let z := jet2
 change π (strainG s u)= _
 rw [show strainG s u =iteratedFDeriv ℝ 2 (ChordG s) 0 ![y,z] from ?_]
 · have hx:= (DFunLike.congr_fun hP ![y,z]).symm; change _= iteratedFDeriv ℝ 2 (EchoLog G) 0 (fun k : Fin 2=> Q ((![y,z]: Fin 2→Lift2 G n) k)) at hx; rw [show (fun k: Fin 2=> Q ((![y,z]: Fin 2→Lift2 G n) k))= _ from ?_] at hx; exact hx; funext i; fin_cases i <;> simp [slice_G,Q,z,y] -- tune
 let H:=fderiv ℝ (ChordG s); let T:= ContinuousLinearMap.apply ℝ (Dir G n) z
 have h:ContDiffAt ℝ 1 H (L 0):=(chord_K s).fderiv_right (by simp)
 change fderiv ℝ ((T ∘ H) ∘ L) 0 u= _; rw [fderiv_comp,ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,show L u=y from rfl,map_zero, iteratedFDeriv_two_apply]; -- tune
 . rw [fderiv_comp, T.fderiv]; rfl
   exact T.differentiableAt
   exact h.differentiableAt (by simp)
 · exact T.differentiableAt.comp _ (h.differentiableAt (by simp))
 exact L.differentiableAt
open MultiNext.SignedSource Lyre
variable (V B:ℝ)(P:BudgetPoint)(X:Support n)(o:Site n)
def ScoreWa (G:Gauge):= ‖iteratedFDeriv ℝ 2 (EchoLog G) 0‖
lemma ScoreWa_pos : 0 ≤ ScoreWa G:=norm_nonneg _
lemma strain_le {u:Dir G n} (h:∀ i∈X,‖s i‖≤ B)(g:Sized V u P o) (e:Edge (Site n))(v:Mom.needed X e): ‖strainG s u e‖≤ (ScoreWa G *B*V)* Lyre.width P o e:=by
 rw [strainG_here]; refine (ContinuousMultilinearMap.le_opNorm ..).trans ?_
 let k:= (u e); let a:=s e.1; let b:=s (e.1+step e.2); let Q: GaugePay G:=(0,k,0); let f:GaugePay G:=(a,0,b); let y:= Lyre.width P o e; have hx:0 ≤ y:= (Lyre.width_pos ..).le
 have hh:0 ≤ B:=(norm_nonneg _).trans (h _ v.1); have hu:0 ≤ V:= g.1
 have he: ‖Q‖ ≤ V*y:=by unfold Q; rw [Prod.norm_def]; refine max_le (by rw [norm_zero]; positivity) ?_; rw [Prod.norm_def]; exact max_le (g.2 _) (by rw [norm_zero]; positivity) -- tune Q fst
 have hz: ‖f‖ ≤ B:=by unfold f; rw [Prod.norm_def]; refine max_le (h _ v.1) ?_; rw [Prod.norm_def]; exact max_le (by rw [norm_zero]; positivity) (h _ v.2)
 rw [Fin.prod_univ_two]; exact (mul_le_mul_of_nonneg_left (mul_le_mul he hz (norm_nonneg f) (mul_nonneg hu hx)) (ScoreWa_pos (G:=G))).trans_eq (by change ScoreWa G * (V*y*B)=_; unfold y; ring)
lemma strain_pay {u:Dir G n}(hV:0≤B) (h:∀ i∈X,‖s i‖≤ B)(g:Sized V u P o): Sized (ScoreWa G*B*V) (Mom.screen X (strainG s u)) P o:=by
 have hu:=g.1; have hz:0 ≤ ScoreWa G*B*V:=mul_nonneg (mul_nonneg ScoreWa_pos hV) hu
 refine ⟨hz,fun e=>?_⟩; rw [Mom.screen_at]; split
 next u=> exact strain_le s V B P X o h g e ‹_›
 next=>rw [norm_zero]; exact mul_nonneg hz (Lyre.width_pos ..).le
end YM.FlightFlux
end
