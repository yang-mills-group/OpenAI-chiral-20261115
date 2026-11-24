import YM.CF.Cay.Cube
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open Matrix AnalyticBridge.RelativeLogdet.Ink
open Far
open Push.Uniform (lowerCol Primary Positions block)
variable {C s D M ε:ℝ}{g:Site c→SU.group.El}{k:S.Choices}
-- arbitrary rotated states. unscaled Ark along
abbrev north(T:Tube G S)(F:Forest S.ratio)(s:ℝ)(w:Mast G c): Ark T F:= (s • w,0)
def peer(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(β s:ℝ)(w:Mast G c): Directions G f→L[ℝ] Ark T F:= (ContinuousLinearMap.inr ℝ (Mast G c) (Fish (Key F G))).comp (coupling β • (paintO (Souk.μ₁ T F x k q d s l w)).comp (nub F x))
variable (T:Tube G S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(β s:ℝ)
lemma liveC(e:Directions G f)(u:Mast G c): north T F s u+peer T x F k q d l β s u e=(s•u,coupling β • glow T x F k s q d l e u):=Prod.ext (add_zero _) (zero_add _)
section
variable {T x F k q d l β s} {p:Site c}{A B: Monk SU.group S}{i:Along S}{t:Signed}{R:Directions G c→ Mast G c} {m:ℕ}
-- transfer at all Z
abbrev latticeFieldEstimates(S:StepData c f)(g:Site c→SU.group.El): Directions G f→L[ℝ] Directions G f:=Motion.swing (constantGauge g S.ratio)
lemma rays{L C₀:ℝ}(h:K.Funds S T)(hp:0<w)(hz:Ready T x)(hv:1000 ≤ radiusB x)(ht:ShardIncome n x L C₀ w T A.key A.park A.V A.k)(H:Lamp T s x A p g R m n)(hT:∀ u:Mast G c, ‖u‖<1→Fire T x A.park A.k l s n C u)(hR: separation p (herald S t i)+horn x l ≤ m*radiusB x): let Y:=dense T x q d l β t i; let X:=lava T A.park x A.k l t i; let L:=latticeFieldEstimates S g; ∀ᶠ v in 𝓝 (0:Directions G c), let M:=R v; let a:=north T A.park s M; let b:=peer T x A.park A.k q d l β s M;
 ‖M‖<1 ∧ Y ∘ rough (A.atop v x)=(fun z=> X (a+b (L z))):=by
 intro Y X L'; filter_upwards [waxy ht hp H] with v hv'; intro M a b; obtain ⟨hC,hD,hz'⟩:=hv'; refine ⟨hC,funext fun i'=>?_⟩
 let B:=A.atop v x; let P:= shiftZ g (rough B i'); let U:=shiftZ g A; let Z:= rough (means U.park U.k U.U s M U.z) (L' i'); have he : Y (rough B i')=Y P:= (congrFun (wage (M:=rough B i') g h hD (half_pos hp) (by omega) t).1 i).symm
 have hp' : Beat P Z (halo (m*radiusB x) {p}):= coat hz' fun _ _=> rfl
 rw [Function.comp_apply, he, show Y P=Y Z from calm t i hz hv (aroundBk (halo (m*radiusB x) {p}) (show Beat.shadows (o:=p) (halo (m*radiusB x) {p}) _ from Subset.refl _) hR) hp']
 unfold a b; rw [liveC]; exact lava_w (A:=Z) rfl h M (s:=s) rfl _ _ (hT _ hC)
lemma radion {z:Directions G f}{v:Mast G c}(h:Fire T x F k l s n C v)(ht:‖z‖ ≤ D) : Allows n (fun i=>peer T x F k q d l β s i z) v (|coupling β| * (D*C)):=by
 let H:= (glow_p (d:=d) (q:=q) h z ht).smul (coupling β); let R(i):=peer T x F k q d l β s i z; have hK (i):R i=(0,coupling β • glow T x F k s q d l z i):=rfl
 change Allows n R _ _; exact ((allows_const v (v:=(0:Mast G c)) (by rw [norm_zero]; exact H.nonneg)).pair H).germ (Eventually.of_forall fun i=> (hK i).symm)
lemma upBook {r j:ℕ}{z: Directions G f}{v:Mast G c}{L M:ℝ}{ε:ℝ} {W: Ark T F→ℝ}(h:∀ v:Mast G c, ‖v‖<1→ Fire T x F k l s r C v) (ht:n+(j+1) ≤ r)(hp:‖z‖≤ L)(hs:0<s)(he:‖v‖<1)(hx:s ≤ ε)(hv:∀ w:Ark T F,‖w‖<ε→ Allows r W w M)(hk: |coupling β| * (L*C) ≤ s/2): MastQ W (north T F s) (fun y=>peer T x F k q d l β s y z) M s (|coupling β| * (L*C)) v j n:=by
 constructor; filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr he)] with i hi; have he:‖i‖<1:= mem_ball_zero_iff.mp hi; let A:=north T F s; let B(i):=peer T x F k q d l β s i z
 have hB:Allows n B i (|coupling β| * (L*C)):= ((radion (d:=d) (q:=q) (β:=β) (h i he) hp).order (by omega)); let a: Mast G c→L[ℝ] Mast G c:= s • ContinuousLinearMap.id ℝ _; have hp' :‖a i‖<s:=by change ‖s • i‖<_; rw [norm_smul_of_nonneg hs.le]; exact mul_lt_of_lt_one_right hs he
 have ha : Allows n a i s:= allows_linear (pole0 s (Mast G c) (Mast G c) hs.le) hp'.le; have hA:Allows n A i s:=ha.pair (allows_const _ (by rw [norm_zero]; exact hs.le)); refine ⟨hA.smooth,hB,fun u hu=>?_⟩
 let L'(y):= u • B y; have ht':=hB.mono hk; have hU:Allows n L' i (s/2):=by refine (ht'.smul u).mono ?_; exact mul_le_of_le_one_left (half_pos hs).le (by rw [abs_of_nonneg hu.1]; exact hu.2)
 let F₁(y):=A y+L' y; have ht'(y):F₁ y=(a y,(L' y).2):=by refine Prod.ext ?_ (zero_add _); change a y+u • (0:Mast G c)= _; rw [smul_zero,add_zero]
 have hp:‖F₁ i‖<s:=by rw [ht',Prod.norm_def]; exact max_lt hp' (((norm_snd_le _).trans hU.value).trans_lt (half_lt_self hs))
 let V:= ContinuousLinearMap.snd ℝ (Mast G c) (Fish (Key F SU.group)); have hL:=hU.linear V (ContinuousLinearMap.norm_snd_le ℝ (Mast G c) (Fish (Key F SU.group))); have hy:Allows n (fun i'=> (L' i').2) i s:=hL.mono (by rw [one_mul]; exact (half_lt_self hs).le)
 have hr:Allows n F₁ i s:= ((ha.pair hy).germ (Eventually.of_forall fun k=> (ht' k).symm))
 exact ⟨hr,(hv (F₁ i) (hp.trans_le hx)).order ht⟩
end
end YM.CF.Cay
