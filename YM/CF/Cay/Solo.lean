import YM.CF.Cay.Yarn
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
open Slate.Far
open Matrix AnalyticBridge.RelativeLogdet
variable {A B:Monk SU.group S}{X: Support c}{p:Site c}{g:Site c→SU.group.El}{R:Directions G c→ Mast G c}{s C D E' ε:ℝ}{m j:ℕ}
lemma opus_i(e:Bond f)(h:K.Funds S T)(hp:0<w)(hz:0<β)(hr:Ready T x)(ht:FreeResolvent.Gap (baseX T x A.key A.park A.k A.V) w)(HV: 1000 ≤ radiusB x)(hs:Beat.shadows (o:=S.ratio.parent e.1) X (coverB l j*radiusB x)) (H:Beat (shiftZ g A) B X) (u:∀ s i,ContDiffAt ℝ (2:ℕ) (dense T x q d l β s i∘ rough B) 0): opus T x q d l β j e A=opus T x q d l β j e B:=by
 let P:=shiftZ g A; rw [← opus_p T x q d l β j e hs hr HV hz H]
 have hq:spring (adjust T x q d l β) e A=spring (adjust T x q d l β) e P:= by
    refine swing_g _ _ _ _ ((rivet _ _ _ _ _ β hz P).contDiffAt.of_le le_top) fun i=> rota_g g h (M:=rough A i) ht hp (by omega) hz
 let L(N:Monk G S)(s):=∑ i∈ rush x N.key s j,spring (dense T x q d l β s i) e N; change -β*averaged (L A)+spring _ e A=-β*averaged (L P)+spring _ e P; rw [hq]; suffices he:L A=L P by rw [he]
 funext s; refine Finset.sum_congr rfl fun i _=>?_; let t:=herald S s i; let M:=S.ratio.parent e.1; let O:= horn x l; let Z:= halo O {t}; let Y:= dense T x q d l β s i; have hv:Virt S Y Z:= calm s i hr HV (Subset.refl _)
 by_cases he: O < separation t M
 · change spring Y e A=spring Y e P; rw [off hv e (points_p e t he), off hv e (points_p e t he)]
 have hℤ: Z ⊆ X:= aroundBk X hs (by rw [separation_comm]; unfold coverB; rw [Nat.add_mul,mul_assoc]; unfold O horn at *; unfold M at he; omega); have heY:Y∘ rough P=Y∘ rough B:=funext fun i=>hv (coat (H.mono hℤ) fun _ _=>rfl)
 exact swing_g g A e Y (show ContDiffAt ℝ (2:ℕ) (Y ∘ rough P) 0 by rw [heY]; exact u s i) fun t=> congrFun (wage (q:=q) (d:=d) (l:=l) (β:=β) g h (M:=rough A t) ht hp (by omega) s).1 i
lemma waxy {L K₀:ℝ}(ht:ShardIncome n x L K₀ w T A.key A.park A.V A.k)(hv:0<w)(hs:Lamp T s x A p g R m n): let B:=shiftZ g A; ∀ᶠ i in 𝓝 0, let Q:=A.atop i x; let M:= means B.park B.k B.U s (R i) B.z;
 ‖R i‖<1 ∧ FreeResolvent.Gap (baseX T x Q.key Q.park Q.k Q.V) (w/2) ∧ Beat (shiftZ g Q) M (halo (m*radiusB x) {p}):=by
 intro B; have he : FreeResolvent.Gap ((baseX T x A.key A.park A.k ∘ Vmove x A.V) 0) w:=by simp only [Function.comp_apply,Vmove,smul_zero,Work.G07.at_zero_increment]; exact ht.soil
 have hE: ‖R 0‖<1:= hs.stage.value.trans_lt (by norm_num)
 filter_upwards [Differential.holds (Neige.transX ht.kernel|>.continuousAt) he (w/2) (half_lt_self hv) (FreeResolvent.native c) (Wisps.front A.key A.park), hs.stage.smooth.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hE)), hs.reads] with i hi v' l'
 intro Q M; refine ⟨mem_ball_zero_iff.mp v',hi,?_⟩; let X:=halo (m*radiusB x) {p}; have hh(y:Site c)(u:y∈X):separation p y ≤ m*radiusB x:=by obtain ⟨z,hz,v⟩:=halo_spec.mp u; rwa [mem_singleton.mp hz] at v
 refine ⟨fun y z=>?_ ,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun i p _=> l' i (hh i.1 p),fun _ _=>rfl,fun _ _=>rfl⟩
 have htY:y∉A.key.place:=fun t=> hs.sanda (halo_spec.mpr ⟨y,t,(separation_comm ..).trans_le ((hh y z).trans (Nat.mul_le_mul_right _ (Nat.le_succ _)))⟩); change (y∈ A.key.place↔ y∈(bareStores _).place); simp only [iff_false_intro htY]; simp [bareStores,Stores.place]
lemma plot_p(e:Bond f)(L D₀:ℝ)(h:K.Funds S T)(hp:0<β)(hy:0<w)(hN:2 ≤ n)(hs:0<s)(hz:s≤ ε)(hx: Ready T x)(hR:1000 ≤ radiusB x)(hr:Lamp T s x A (S.ratio.parent e.1) g R m n) (hu:coverB l j ≤ m)(ht:ShardIncome n x L D₀ w T A.key A.park A.V A.k)(H:∀ v:Mast G c, ‖v‖<1→ Fire T x A.park A.k l s n C v)(hT:∀ t i,KnotP (lava T A.park x A.k l t i) n D E' ε)(hC:0≤ C)(v:ℝ)(hA:‖A.z‖ ≤ v):
 Allows n (fun i=>opus T x q d l β j e (A.atop i x)) 0 (Jet.composeCost n (β*coupling β*(bankU* v*(2^n*C*(C*s^(l+2))))+(bankU*v) * (v*(C*s^3))) (1/2)):=by
 let B:=shiftZ g A; let P(i:Mast G c):=proxZ T B.park x B.k B.U q d l β s i
 let z:=arrow e B.z; let F(x'):ℝ:=fderiv ℝ (P x') 0 z; let U(x'):ℝ:= hdot (P x') 0 B.z z; let X(i):= F i+ U i/2; have he: ‖B.z‖≤ v:=(speed g A).trans hA
 let N:= bankU*v; have hZ: Souk.costU (nub A.park x z) ≤ N:= (fuelL (F:=A.park) (x:=x) e B.z).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans he) (by unfold bankU; positivity))
 let o:=R 0; have hl:‖o‖<1:=hr.stage.value.trans_lt (by norm_num); have hg(u t):= knotH (q:=q) (d:=d) B.U (v:=o) h H hl hp u t; obtain ⟨-,hU⟩:= hg B.z z; obtain ⟨hF,-⟩:= hg z z
 have ha':0≤ v:=(norm_nonneg _).trans he; have hN':0≤N:=by unfold N bankU; positivity
 let L':= N*(v*(C*s^3)); have hL':0≤L':=by unfold L'; positivity
 let Q:= β*coupling β
 have h₁: Allows n F o (Q*(N*(2^n*C*(C*s^(l+2))))):=by apply hF.mono; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ (by positivity)); exact mul_nonneg hp.le (coupling_pos hp).le
 have h₂: Allows n (fun i=>U i/2) o L':=by
    have ht' := hU.mono (show _≤L' from mul_le_mul hZ (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity) hN'); refine ((ht'.smul ((2:ℝ)⁻¹)).germ (Eventually.of_forall fun i=>?_)).mono ((mul_le_of_le_one_left hL' (by norm_num))); dsimp only; change _ * U i= _; ring
 apply ((h₁.add h₂).comp (f:=R) hr.stage).germ
 filter_upwards [waxy ht hy hr] with i hi; let P':= A.atop i x; let V:= R i; let Y':= means B.park B.k B.U s V B.z; obtain ⟨hW,hp',heP⟩:=hi
 have heW (i j):ContDiffAt ℝ (2:ℕ) (dense T x q d l β i j∘rough Y') 0:= (rosy (A:=Y') (s:=s) (q:=q) (d:=d) (β:=β) rfl h V rfl i j (H V hW) hW hs hz (hT _ _)).of_le (by exact_mod_cast hN)
 change F V+U V/2=opus T x q d l β j e P'; rw [opus_i (g:=g) e h (half_pos hy) hp hx hp' hR (?_) heP heW,strut_w _ _ _ _ _ _ _ _ _ rfl hp heW]; rfl -- tune halo monotonic farther
 intro i hi; obtain ⟨y,p,t⟩:=halo_spec.mp hi; exact halo_spec.mpr ⟨y,p,t.trans (Nat.mul_le_mul_right _ hu)⟩
end YM.CF.Cay
