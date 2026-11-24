import YM.CF.Tarn.Quota
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
variable (T:Tube G S)(x:ℝ)
def ViaQ(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(s:Signed)(α:ℝ)(i: Along S)(y:Ark T F):ℝ:= TaleX T x α (vX T F k s y) (fX T x F k s l y) i
lemma priced_q {u:Ark T P.1}(h: Well T x P.1 P.2 s l n C u)(hf:∀ i, Allows n (fun y=>gplot (batch T.up.loop (Stores.till x)) (fX T x P.1 P.2 s l y) i) u D)(hq:∀ i,Allows n (fun y=>gplot (batch T.down.loop (Hors.cart x S.patch.L)) (vX T P.1 P.2 s y) i) u D)(α:ℝ)(p:|α| ≤ a)(hx:0 ≤ D)(hC:0≤ C)(i: Along S):let A:=2^n*C*C; let W:=max D (a*(C+(A+A))); Allows n (ViaQ T x P.1 P.2 l s α i) u W:=by
 intro A W; let R:= vX T P.1 P.2 s; let M:=ViaQ T x P.1 P.2 l s α i; rcases i with (i|i|i|i)|i|i
 · exact allows_const _ ((norm_zero).le.trans (hx.trans (le_max_left ..)))
 · exact allows_const _ ((norm_zero).le.trans (hx.trans (le_max_left ..)))
 · let T'(b:Bool):=fun y:Ark T P.1=> ‖XX T x P.1 P.2 s (i,b) y‖^2/2
   have he(b):Allows n (T' b) u A:=by
      have hv := breeze (h.P (i,b)) (h.P (i,b)); refine (((hv.smul (1/2:ℝ)).mono (mul_le_of_le_one_left hv.nonneg (by norm_num))).germ ?_); filter_upwards with v; unfold T'; rw [real_inner_self_eq_norm_sq]; change (1/2:ℝ)*_=_; ring
   have hp:= (h.Q i).add ((he true).add (he false))
   refine (((hp.smul (-α)).mono ?_).germ ?_)
   · exact (mul_le_mul_of_nonneg_right ((abs_neg α).le.trans p) hp.nonneg).trans (le_max_right ..)
   filter_upwards with v; unfold ViaQ; change _= -α*king _ _ _ _ _ _ _ _; rw [manta,Fintype.sum_bool]; rfl -- tune
 · exact allows_const _ ((norm_zero).le.trans (hx.trans (le_max_left ..)))
 · exact (hf i).mono (le_max_left ..)
 have ht:=(hq i).smul (-1:ℝ); rw [abs_neg,abs_one,one_mul] at ht; exact (ht.germ (Eventually.of_forall fun i=>neg_one_smul ℝ _)).mono (le_max_left ..)
-- truth ψ:sol and U etc. lift_s at input rep. glitter
lemma originY (g: Monk SU.group S)(v:Mast G c)(hv:g.key=bareStores S)(hp:g.V=satU G w v)(hu:g.z=0)(h:Fire T x g.park g.k l w n C v) (q:Chi)(d β:ℝ)(s:Signed): pull s 0 (g.sent x T q d l β)= fX T x g.park g.k s l (w • v,0):=by
 let W:=w • v; let P:=g.z; let B:= g.park; let z:=coupling β • glow T x B g.k w q d l g.z v; let A:= sol S T g.k x B l W
 have ht: z=0:=by
    unfold z; rw [hu]; suffices h : glow T x B g.k w q d l (0:Directions G f) v=0 by rw [h,smul_zero]
    change _ *ᵥ visitX B x ((tint G (Active (bareStores S) x B)).symm 0)=(0:Fish (Key B G)); rw [map_zero,map_zero,Matrix.mulVec_zero]
 rw [shineU hv v hp h,hp,←ht]; exact congrArg (pull s 0) (tray_x B x W (z+A))
lemma priced_v (l n:ℕ)(α:ℝ)(s:Signed)(P:Tab S)(u:ℝ)(h:0<u)(p:u ≤ 1)(i:Along S)(C:ℝ)(hr:∀ y : Ark T P.1, ‖y‖<u → Allows n (ViaQ T x P.1 P.2 l s α i) y C)(D:ℝ)(hp:∀ y:Mast G c, ‖y‖<1 → Fire T x P.1 P.2 l u n D y) (q:Chi)(d:ℝ): ∀ y:InputZ G c,‖y‖<u→ Allows n (satX (tilT T x q d α l P s i)) y (composeCost n C 1+composeCost n C 1):=by
 let L:= chair T P.1; let E:InputZ G c→L[ℝ] Ark T P.1:= (ContinuousLinearMap.inl ℝ _ _).comp L; let W(V):= loreG T x q d α l s i (bunk S P V)
 have he(y:InputZ G c):‖E y‖ ≤ ‖y‖:= max_le (Push.Uniform.tint_inv_le y) (by change ‖(0:Fish (Key P.1 G))‖ ≤ _; rw [norm_zero]; positivity)
 have hh(y:InputZ G c)(hu:‖y‖<u): W (represent y)=ViaQ T x P.1 P.2 l s α i (E y):=by
    let v:=u⁻¹ • L y; have hv: u • v=L y:= smul_inv_smul₀ h.ne' _; have hz: ‖v‖<1:=by have he:‖L y‖<u:= (Push.Uniform.tint_inv_le y).trans_lt hu; rw [←hv,norm_smul_of_nonneg h.le] at he; exact lt_of_mul_lt_mul_left (he.trans_eq (mul_one _).symm) h.le
    let g:= bunk S P (represent y); unfold W loreG; have hx:satU G u v=g.V:=by unfold satU; rw [hv,show L y= _ from rfl,chap] -- tune
    rw [originY T x g v rfl hx.symm rfl (hp _ hz)]; unfold ViaQ; apply congrArg₂ (fun X Y=> TaleX T x α X Y i)
    · rw [show g.V= _ from hx.symm]; unfold satU; rw [hv]; rfl
    rw [hv]; rfl -- tune
 let V:=Complex.ofRealCLM; let A:=composeCost n C 1; let Γ:= V∘ W ∘ represent; have hv(y:InputZ G c)(hy:‖y‖<u): Allows n Γ y A:=by
    refine ((((hr _ ((he y).trans_lt hy)).comp (allows_linear (show ‖E‖ ≤1 from ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (he i).trans_eq (one_mul _).symm) ((he y).trans (hy.le.trans p))|>(show _→Allows n E y 1 from id))).linear V (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; exact (Complex.norm_real i).le)).mono (one_mul _).le |>.germ ?_)
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with v hv; exact congrArg (fun x:ℝ=>(x:ℂ)) (hh v (mem_ball_zero_iff.mp hv)).symm
 intro y hy; have hx: Γ 0= V (W 1):=by unfold Γ; simp only [Function.comp_apply]; simp
 apply subtract_p (hv _ hy) (allows_const y (show ‖V (W 1)‖≤A from hx ▸ (hv 0 (by simpa)).value)) -- defeq?
end
end YM.CF.Tarn
