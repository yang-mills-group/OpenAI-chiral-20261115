import YM.CF.Slate.Roll
import YM.CF.Souk.Big
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
abbrev pic(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(s:ℝ)(u:Mast G c):= meetVar (s • u) (Newt.sol S T k x F l (s • u))
structure Spice(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(s:ℝ)(n:ℕ)(A:ℝ)(u:Mast G c):Prop where
 serve : ContDiffAt ℝ ω (clipped T x F k) (pic T x F k l s u)
 gram : Protected n (fun y=> block (clipped T x F k) (pic T x F k l s y)) u A
 shine (q:Chi)(d:ℝ): ζ₁ T F x k q d s l u= block (clipped T x F k) (pic T x F k l s u) ∧ orbitP T x (facadeX G (s•u)) k (bareStores S) F q d 1 l=leaveX F x (Newt.sol S T k x F l (s • u))
 tip: Allows n (fun y=>Slope (clipped T x F k) (pic T x F k l s y)) u (A*s^(l+2))
lemma cliffK (P:Patch)(K:Teller G)(p:P.Branches K.bind G)(n l:ℕ)(hn:2≤n)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3)):
 ∃ C e:ℝ,0 < C∧0 < e∧ ∀ᶠ x in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F →∀ (k:S.Choices)(s:ℝ),0<s→ temp x ≤ s → s≤ e → ∀ y:Mast G c,‖y‖<1 → Spice T x F k l s n C y:=by
 obtain ⟨a,Q,v,D,p',ha,hQ,hv,hD,hb,H'⟩:= yields K (n+1) l (by omega) P p W
 obtain ⟨t,b,hT,ht,H⟩:= cup (n+1) l (by omega) P K p W
 let A:=max D t; have hA:1 ≤ A:=hT.trans (le_max_right ..); have hA':0<A:=zero_lt_one.trans_le hA
 obtain ⟨u,h,C,hu,hh,hC,hM⟩:=Newt.mat_paid K P (n+3) (by omega) W; obtain ⟨hx,H''⟩:=tip_left (n+3) (l+2) P K
 let B:=min (min u a) 1; have hB:0<B:=lt_min (lt_min hu ha) zero_lt_one; let ε:=min (min p' b) (B/(6*A)); have hε:0<ε:=lt_min (lt_min hb ht) (by positivity)
 let X:=(1+Uniform.townCost G*countCost h)^(n+2); let r:= Char.peak (n+3) P K; let M:=(1+Uniform.townCost G*countCost r)^(n+2)
 let M':=(1+Uniform.townCost G*countCost r)^(n+1); let J:=2^n*composeCost n (C*X) 1*Q+composeCost n M 1; let E:= Jet.composeCost (n+1) (C*X+M) 1
 refine ⟨max 1 (max E J),ε,lt_of_lt_of_le zero_lt_one (le_max_left ..),hε,?_⟩
 filter_upwards [H',H,H''] with x hz he0 he''
 intro c f S T F hw hw' k s hs hp hk y hy; obtain ⟨z,hZ,p₀,ht',hJ⟩:=hz S T F hw hw'; let Z(y:Mast G c):=Uniform.station z (s•y); let g:= clipped T x F k; let m(y:Mast G c):=sol S T k x F l (s•y)
 obtain ⟨hr,hg⟩:=he0 S T F hw hw' s hs hp (hk.trans ((min_le_left ..).trans (min_le_right ..))) l le_rfl
 have hE: 3*A*s<B:=by have hL:s*(6*A)≤ B:= (le_div_iff₀ (show 0<6*A by positivity)).1 (hk.trans (min_le_right ..)); linarith
 have hL:s<B:=lt_of_le_of_lt (by nlinarith only [hA,hs,mul_le_mul_of_nonneg_right hA hs.le]) hE; have hW:3*A*s ≤1:=hE.le.trans (min_le_right ..)
 let U(y:Mast G c):= meetVar (s•y) (m y); let f:= costP F k T.high T.up
 have h₁ (y:Mast G c)(hy:‖y‖<1): Allows (n+1) Z y (A*s):=by
    have hh:= near_s (f:=Uniform.station z) hs.le (hL.le.trans (min_le_right ..)) (show 1≤n+1 by omega) (show s<a from hL.trans_le ((min_le_left ..).trans (min_le_right ..))) (fun x hx=> (p₀ x hx.le).2.1) hy.le
    simp_rw [show Uniform.station z 0=0 from by simp [Uniform.station,hZ.critical.1],sub_zero] at hh; exact hh.mono (mul_le_mul_of_nonneg_right (le_max_left ..) hs.le)
 have h₂(y:Mast G c)(hy:‖y‖<1): Allows (n+1) m y (A*s):= (hr.root k y hy).mono (mul_le_mul_of_nonneg_right (le_max_right ..) hs.le)
 have hI u' (hv:‖u'‖< B):= (((hM S T x hw).2.2.2 F k).2 u' (hv.trans_le ((min_le_left ..).trans (min_le_left ..))))
 let q:=s^(l+2); have hq:0≤ q:=pow_nonneg hs.le _; have hsq:q≤1:=pow_le_one₀ hs.le (hL.le.trans (min_le_right ..))
 have ht u'(hu:‖u'‖<B): Newt.Wax (f-g) u' (n+3) r q:=(he'' S T hw F k u' (hu.trans_le (min_le_right ..))).mono (pow_le_pow_left₀ (temp_nonneg _) hp (l+2)) -- tune
 have hxq:= (h₂ _ hy); have heZ : Allows (n+1) U y (3*A*s):= (Newt.turn_safe hxq hxq hs.le hA hy 0 (Set.left_mem_Icc.mpr zero_le_one)).germ (Eventually.of_forall fun i=>by simp [U]); have he := heZ.value.trans_lt hE; have hF:= hI _ he; have he' :=ht (U y) he; have hg':ContDiffAt ℝ ω g (U y):=by rw [←sub_sub_cancel f g]; exact hF.1.sub he'.1 -- tune
 refine ⟨hg',?_ ,fun q d=> ⟨?_,(hg q d 1 k y hy).1⟩,?_⟩
 · let W(y:Mast G c):=paintO (block g (U y)); have hb:=heZ.mono hW; have hg: (fun y' :Mast G c=>paintO (block f (U y')) -paintO (block (f-g) (U y')))=ᶠ[𝓝 y] W:=by
      filter_upwards [heZ.smooth.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr he))] with i hi; have ht1:=mem_ball_zero_iff.mp hi; have hf:=ht1; change ‖U i‖<B at hf; rw [block_minus (F:=F) (hI _ hf).1 ((ht (U i) hf).1),sub_sub_cancel]
   have hi:= ((stiffness hF.hv hF.he (Uniform.town F) hC.le hh).comp (f:=U) hb); have hj:=(((stiffness he'.hv he'.he (Uniform.town F) hq hx).mono (mul_le_of_le_one_left (by have hm:= Uniform.count_pos (show 0<r from hx); positivity) hsq)).comp (f:=U) hb) -- tune M
   refine (((subtract_p hi hj).order (show n ≤ n+1 by omega)|>.germ hg).mono ?_); apply le_trans _ (show E ≤ max 1 (max E J) from (le_max_left ..).trans (le_max_right ..)); unfold E Jet.composeCost X M; exact Eq.le (by ring)
 · unfold ζ₁; rw [blossom]; exact notSym (pageX F x) (hg q d 1 k y hy).2 hg'
 let X':= fun v=>Slope f v; let J'(v:Positions (Push.Uniform.Joint F G)):= Slope g v; -- tune
 have hw(v: Mast G c)(p: ‖v‖<1): X' (meetVar (s•v) (Z v))=0:= (p₀ (s•v) (by rw [norm_smul_of_nonneg hs.le]; refine (mul_lt_of_lt_one_right hs p).le.trans (hL.le.trans ((min_le_left ..).trans (min_le_right ..))))).2.2.1 k
 have hp':= hJ k s hs hp (hk.trans ((min_le_left ..).trans (min_le_left ..)))
 have hh'(v)(p:‖v‖< B):Allows (n+1) X' v (C*X):=(pin (hI _ p).hv (hI _ p).he (Uniform.town F) hC.le hh).order (by omega)
 have hb:= Hors.varying (m:=m) (z:=Z) hh' hy (fun j h=>⟨(h₂ _ h).order (show n≤n+1 by omega),(h₁ _ h).order (show n≤n+1 by omega)⟩) hs.le hA hE hW ((hp'.due _ hy).order (show n ≤ n+1 by omega)); let N':= max 1 (max E J)
 have heX: Allows n (fun x=> Slope (f-g) (U x)) y (Jet.composeCost n (q*M) 1):=((pin he'.hv he'.he (Uniform.town F) hq hx).order (show n ≤ n+2 by omega)).comp (f:=U) ((heZ.order (by omega)).mono hW)
 apply (subtract_p hb heX).germ _ |>.mono
 ·
   exact le_trans (le_of_eq (show _= J*q by unfold J q Jet.composeCost; ring)) (mul_le_mul_of_nonneg_right ((le_max_right E J).trans (le_max_right 1 _)) hq)
 filter_upwards [heZ.smooth.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr he)),isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with i h v
 rw [hw i (mem_ball_zero_iff.mp v)] -- maybe tune X
 have he := mem_ball_zero_iff.mp h; have hX:=hI _ he; have hh':= ht _ he; change X' _-0 - Slope (f-g) _= Slope g (U i); rw [sub_zero]
 ext j; have hv: Slope (f-g) (U i) j=Slope f (U i) j-Slope g (U i) j:=by
    unfold Uniform.Slope Uniform.entry; have hg: ContDiffAt ℝ ω g (U i):=by rw [←sub_sub_cancel f g]; exact hX.1.sub hh'.1
    rw [iteratedFDeriv_sub_apply (hX.1.of_le le_top) (hg.of_le le_top)]; rfl
 change Slope f (U i) j -Slope (f-g) (U i) j= _; rw [hv,sub_sub_cancel]
end YM.CF.Slate
