import YM.CF.Slate.Oslo
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
open Work.E03 Souk
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open Push
local notation "G"=> SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
-- unscaled has protected; transfer to σ with polynomial lamp mask. λ can be comparable with lamp not from ψ.
namespace Spice
variable {M N s e:ℝ}{k:S.Choices}
lemma more {v:Mast SU.group c}(h:Spice T x F k l s n M v)(hp:0 ≤ s)(v':M ≤ N): Spice T x F k l s n N v:= ⟨h.serve,h.gram.mono v',h.shine,h.tip.mono (mul_le_mul_of_nonneg_right v' (pow_nonneg hp _))⟩
end Spice
structure Fire (T: Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(s:ℝ)(n:ℕ)(A:ℝ)(u:Mast G c):Prop extends Spice T x F k l s n A u where
 flame(q:Chi)(d:ℝ): let z₀:=bareStores S; let U:=satU (c:=c) G s; let N:= layX T x z₀ F k q d 1 l ∘ U
                     Protected n N u A ∧ Protected n (fun i=> (N i).transpose) u A ∧ Protected n (bankX T x z₀ F k q d 1 l ∘ U) u (A*s)∧ Protected n (fun y=> perturb (μ₁ T F x k q d s l y) (block (clipped T x F k) (pic T x F k l s y))) u (A*s^3)
lemma persp (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n l:ℕ)(hp:2 ≤ n)(hv:l ≤18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(V: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)):
 ∃ C e:ℝ,0 < C∧0 < e∧∀ᶠ x in atTop,0<lamp x ∧ temp x ≤ lamp x ∧ lamp x<e ∧∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F →∀ (k:S.Choices)(s:ℝ), lamp x ≤ s → s ≤ e →∀ u:Mast G c, ‖u‖ < 1 → Fire T x F k l s n C u:=by
 obtain ⟨Z,a,hZ,ha,H⟩:= cliffK P K p n l hp W; obtain ⟨H',g,hF,hg,Q⟩:=potP K P p n; obtain ⟨m,v,D,U,hm,hv',hD,J⟩:=metricsU K P n l hp hv p V
 let A:= (2:ℝ)^n*(2^n*H'* Z)* H'+1; let L:= min (min a g) 1; let E:=A/L; let ε:=L/2; let M:= max U 1; let G':=E+M
 have hL:0<L:=lt_min (lt_min ha hg) zero_lt_one; have he:0<ε:= half_pos hL; have ht:0<M:=zero_lt_one.trans_le (le_max_right ..); have hu:0 ≤ E:=by unfold E A; positivity
 have hz:0<G':=by unfold G'; positivity
 let X:= varyP n G'; let X':= delve n G'; have hx:= vicar (n:=n) G' hz.le; let C:=2^n* H'*(1+ X); have hQ:0 ≤ X:=hx.1
 let N:= max (max Z G') (max C X'); have hr:C≤ N:=(le_max_left ..).trans (le_max_right ..); have hZ': Z ≤ N:=(le_max_left ..).trans (le_max_left ..)
 refine ⟨N,ε,hZ.trans_le hZ',he,?_⟩; filter_upwards [H,Q,J,lamp_s.eventually (gt_mem_nhds he),Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,eventually_gt_atTop (0:ℝ)] with x hΛ hK hJ hx hS hy
 have hs:1 ≤ (radiusB x:ℝ):=Nat.one_le_cast.mpr (show 0 < radiusB x by omega); have hp': temp x ≤ lamp x:=le_mul_of_one_le_left (temp_nonneg _) (one_le_pow₀ hs)
 have he':0<lamp x:=(Work.E09.temp_pos hy).trans_le hp'; refine ⟨he',hp',hx,?_⟩; intro c f S T F hT hb k s ht' hR u hu'
 have hr':=he'.trans_le ht'; have hE':ε < L:=half_lt_self hL; have htR:= hR.trans hE'.le; have hw:L ≤1:=min_le_right ..; have hV:L≤g:=(min_le_left ..).trans (min_le_right ..); have hA:L ≤ a:=(min_le_left ..).trans (min_le_left ..)
 have hxA:=hΛ S T F hT hb k s hr' (hp'.trans ht') (htR.trans hA); refine { (hxA _ hu').more hr'.le hZ' with flame:=?_}; intro q d z₀ V' L₀
 let L'(v:Config G c):= bankX T x z₀ F k q d 1 l v; let W(v):=paintO (L' (satU G L v)); have hW(u:Mast G c)(hu: ‖u‖<1):Allows n W u A:=by
    have hh(v:Mast G c)(hv:‖v‖<1):= hΛ S T F hT hb k L hL (hp'.trans (ht'.trans htR)) hA v hv; obtain ⟨h₁,h₂⟩:=hK S T F hT k L ⟨hL.le,hV⟩ u hu.le
    have h₃ : Protected n (majorX T x (bareStores S) F k q d 1 l ∘ satU G L) u Z:=by
       refine transfer ((hh u hu).gram.germ ?_); filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu)] with i hi; exact congrArg paintO ((hh i (mem_ball_zero_iff.mp hi)).shine q d).1.symm
    exact subsid (fuseP h₁ h₂ h₃) (show Protected n (fun _:Mast G c=> (1:Neige.Shelf (Rows.In x (bareStores S) F («G»:=SU.group)))) u 1 from allows_const _ (by rw [paint_one]; exact ContinuousLinearMap.norm_id_le))
 have hM := ((hJ S T hT _ F _ (PhysicalNext.JointLoad.Heir.noFlags x SU.group c).symm hb k).2 q d (1:LinkArray SU.group (Frozen z₀ x F))).payX.value; have hpX:‖W 0‖ ≤ M*s:=by
    simp only [Vmove,Function.comp_apply, smul_zero,Work.G07.at_zero_increment] at hM; unfold W satU; rw [smul_zero,show facadeX G (0:Mast G c)=1 by simp [facadeX]]; refine hM.trans ((mul_le_mul_of_nonneg_right (le_max_left ..) he'.le).trans (mul_le_mul_of_nonneg_left ht' ht.le)) -- tune
 let p : ℝ:= s/L; have hp:0 ≤ p:=(div_pos hr' hL).le; have hf:p<1:=(div_lt_one hL).mpr (hR.trans_lt hE')
 have hh:= near_s hp hf.le (show 1≤n by omega) hf hW hu'.le; have hy:Protected n (L' ∘ V') u (G'*s):=by
    refine ((hh.add (allows_const u hpX)).germ (Eventually.of_forall fun i=>?_ )).mono ?_
    · change W (p • i) - W 0 + W 0= _; rw [sub_add_cancel]; unfold W satU; rw [smul_smul, show L*p=s from (by unfold p; field_simp)]; rfl
    exact le_of_eq (by unfold G' E p; field_simp)
 have hP:= hK S T F hT k s ⟨hr'.le,htR.trans hV⟩ u hu'.le; have hr : Protected n (port∘ L' ∘ V') u (1+X):=attach (A:=fun _:Mast G c=> (1:Neige.Shelf (Rows.In x z₀ F («G»:=SU.group)))) (allows_const _ (by rw [paint_one]; exact ContinuousLinearMap.norm_id_le)) ((pitchM hy hz.le hr'.le (htR.trans hw)).mono (mul_le_of_le_one_right hQ (htR.trans hw))) -- tune binder
 have hh':Protected n L₀ u C:= fuseN hP.1 hr; have hz' : Protected n (fun i=> legacy (Chief T x F k s i) (majorX T x (bareStores S) F k q d 1 l (V' i))) u (X'*s^3):=by
    refine (relic_p hy hz.le hr'.le (htR.trans hw)).germ (Eventually.of_forall fun i=>?_); dsimp only; rw [legacy_eq (Chief T x F k s i) (majorX T x (bareStores S) F k q d 1 l _) (sym_hessN l)]; rfl
 refine ⟨hh'.mono (by assumption),((fuseN hr hP.2).mono (le_trans (le_of_eq (show _=C by unfold C; ring)) (show C ≤ N by assumption))).germ ?_,hy.mono (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_left ..)) hr'.le),?_⟩
 · filter_upwards with i; apply congrArg paintO; unfold L₀; unfold layX; dsimp only [Function.comp_apply]; rw [turnQ _ (majorX T x z₀ F k q d 1 l (V' i)) (sym_hessN l)]
 let Lh:= pageX F x («G»:=SU.group); refine ((jump_up (leaveX F x) (visitX F x) (visit_n ..) (leave_n ..) hz').germ ?_).mono (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (pow_nonneg hr'.le _))
 filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hu')] with i hi; rw [← ((hxA i (mem_ball_zero_iff.mp hi)).shine q d).1]; let A₁:= L₀ i; let P':= majorX T x z₀ F k q d 1 l (V' i); change ((visitX F x).comp (paintO (perturb A₁ P'))).comp (leaveX F x)=paintO (perturb (A₁.submatrix Lh Lh) _)
 rw [perturb, perturb,fuseQ,fuseQ]; unfold ζ₁; change _ = paintO (((A₁.submatrix Lh Lh).transpose*P'.submatrix Lh Lh*A₁.submatrix Lh Lh)-1); rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,← Matrix.submatrix_one_equiv (α:=ℝ) Lh,← show (A₁.transpose*P'*A₁-1).submatrix Lh Lh= (A₁.transpose*P'*A₁).submatrix Lh Lh- Matrix.submatrix 1 Lh Lh from congrFun (congrFun (Matrix.submatrix_sub ..) (_: Key F SU.group→ _)) _]; rw [show Lh=pageX F x from rfl,tableVisit]; rfl
end YM.CF.Slate
