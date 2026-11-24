import YM.CF.Arena.Arm
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
lemma locus (i:Along S)(h:K.Funds S T)(ht: Ready T x)(hp:1000≤radiusB x): Rel.Atom (bale T P q x d l s i) (herald S s i) (horn x l):=by
 refine ⟨fun u v=>baleG _ _ _ _ _ _ _ h i v u,fun u v p=>?_⟩; apply congrArg (fun x:ℝ=>(x:ℂ)) (calm (q:=q) (d:=d) (l:=l) (β:=0) s i ht hp (X:=pavilion (horn x l) (herald S s i)) (Subset.refl _) (M:=bunk S P u) (N:=bunk S P v) ?_)
 exact ⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun i u _=>p i ((theatre _ _).mp u),fun _ _=>rfl,fun _ _=>rfl⟩
abbrev chair(T:Tube G S)(F:Forest S.ratio): InputZ G c→L[ℝ] Mast G c:=(tint G (Body 1 c)).symm.toContinuousLinearMap
lemma chap(T:Tube G S)(F:Forest S.ratio)(u:InputZ G c): facadeX G (chair T F u)=represent u:=by
 change represent (tint G (Body 1 c) ((tint G (Body 1 c)).symm u))=_; rw [ContinuousLinearEquiv.apply_symm_apply]
lemma caseA (K:Teller G)(P:Patch)(q:Chi)(ℓ:ℝ)(l n:ℕ)(hv:l≤18)(p:P.Branches K.bind G)(hp:3 ≤ n)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(V:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)):∃ σ D C:ℝ,0<σ∧σ ≤ 1∧0<C∧0<D∧∀ᶠ x in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S)(H:Tab S), Cert P K S T x→ sizedP G P K S T H.1→∀ (i:Along S)(s:Signed)(d:ℝ), let U:=bale T H q x d l s i; CakeF U (herald S s i) (horn x l) n σ C ∧ cFoot 2 (satX U)∧ ‖Nacre.cake 2 (satX U)‖ ≤ D*temp x^(l+1) :=by
 obtain ⟨C,E,hC,hE,H⟩:= persp K P p n l (by omega) hv W V; obtain ⟨D,E',hD,hE',V'⟩:= lava_p P K p n l hp V
 let A:= composeCost n D 1; have hA:0<A:=by unfold A composeCost; positivity
 let s:=min E (min E' 1); have hs:0<s:= lt_min hE (lt_min hE' zero_lt_one)
 refine ⟨s,D,A,hs,(min_le_right ..).trans (min_le_right ..),hA,hD,?_⟩ -- Pt use Slope
 filter_upwards [H,V',PatchReads.reserve K P, Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, lamp_s.eventually (ge_mem_nhds hs)] with x hΛ hK hU hB hv' -- lamp_s le_mem gt?
 intro c f S T P' hP H i u d U; let Y:=lava T P'.1 x P'.2 l u i; have hz:= hΛ.2.2.2 S T P'.1 hP H P'.2 s hv' (min_le_left ..); let F:= chair T P'.1; let G': InputZ G c→L[ℝ] Ark T P'.1:=(ContinuousLinearMap.inl ℝ (Mast G c) _).comp F; let V:= Complex.ofRealCLM
 have hT(w:InputZ G c):‖G' w‖ ≤ ‖w‖:= (max_le ((Push.Uniform.tint_inv_le w)) (by change ‖(0:Fish (Key P'.1 G))‖ ≤ _; rw [norm_zero]; positivity)) -- tune
 have he(w:InputZ G c)(hp:‖w‖<s): satX U w= V (Y (G' w)):=by
    let v:=s⁻¹ • F w; have hv : s • v= F w:= smul_inv_smul₀ hs.ne' _; have hz' : ‖v‖<1:=by
       have hh:‖F w‖<s:= (Push.Uniform.tint_inv_le w).trans_lt hp; rw [←hv,norm_smul_of_nonneg hs.le] at hh; exact lt_of_mul_lt_mul_left (show s*‖v‖<s*1 from hh.trans_eq (mul_one _).symm) hs.le
    let M:=bunk S P' (represent w); have hM:M.V=satU G s v:=by unfold satU; rw [hv,chap]
    have he0: glow T x P'.1 P'.2 s q d l (0:Directions G f) v=0:=by change _ *ᵥ visitX P'.1 x ((tint G (Active (bareStores S) x P'.1)).symm 0)=(0:Fish (Key P'.1 G)); rw [map_zero,map_zero,Matrix.mulVec_zero]
    change (stars T x M q d l 0 u i:ℂ)= _; rw [lava_w (A:=M) (s:=s) rfl hP.funds.1 v hM i u (hz _ hz')]; apply congrArg (fun x:Ark T P'.1=> V (Y x)); exact Prod.ext hv (show coupling 0 • glow T x P'.1 P'.2 s q d l (0:Directions G f) v=0 by rw [he0,smul_zero])
 have hp(w:InputZ G c)(h:‖w‖<s): satX U =ᶠ[𝓝 w] (V ∘ Y ∘ G'):= Filter.Eventually.mono (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr h)) fun i hi=> he i (mem_ball_zero_iff.mp hi)
 have hY := hK S T P'.1 hP H P'.2 i u; have hV:‖V‖ ≤1 :=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; exact (Complex.norm_real i).le -- tune
 have hQ: ‖G'‖ ≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> (hT i).trans_eq (one_mul _).symm
 have hl(w:InputZ G c)(hr:‖w‖<s): Allows n (Y ∘ G') w A:=by have hk:= (hT w).trans_lt hr; exact (hY.sails _ (hk.trans_le ((min_le_right ..).trans (min_le_left ..)))).comp (f:=G') (allows_linear hQ (hk.le.trans ((min_le_right ..).trans (min_le_right ..))))
 refine ⟨⟨locus i hP.funds.1 (hU _ _ hP.got hP.size hP.funds.1) hB,fun i h=>((((hl i h).linear _ hV).mono (one_mul _).le).germ (hp i h).symm)⟩,?_,?_⟩
 all_goals have h0:‖(0:InputZ G c)‖<s:=by simpa using hs
 all_goals have heZ(i:ℕ)(hi:i ≤ n):iteratedFDeriv ℝ i (satX U) 0=V.compContinuousMultilinearMap ((iteratedFDeriv ℝ i Y 0).compContinuousLinearMap (fun _=> G')):=by
              rw [((hp 0 h0).iteratedFDeriv ℝ i).eq_of_nhds,V.iteratedFDeriv_comp_left (show ContDiffAt ℝ (n:ℕ∞ω) (Y ∘ G') 0 from (hl _ h0).smooth) (by exact_mod_cast hi),Push.Uniform.iter_lin_at (L:=G') (by rw [map_zero]; exact ((hY.sails _ (by simpa)).order hi).smooth), map_zero]
 · intro i hi; rw [heZ i (by omega), show iteratedFDeriv ℝ i Y 0=0 from hY.peak i hi]; ext; simp
 have ht:‖(iteratedFDeriv ℝ 2 Y 0).compContinuousLinearMap (fun _=>G')‖ ≤ D*temp x^(l+1):=by apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; simp only [prod_const,card_univ,Fintype.card_fin]; exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hQ)).trans hY.cap
 unfold Nacre.cake; rw [norm_smul,heZ 2 (by omega)]; apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ((ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hV).trans ht)); norm_num [Nat.factorial]; -- tune
end YM.CF.Arena
