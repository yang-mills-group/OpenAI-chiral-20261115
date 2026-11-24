import YM.CF.Rink.Whet
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
open Affine Reine
section
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(h:K.Funds S T)(p: FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(hr:0 < β)
include hr
lemma trail: adjust T x q d l β M= costU (M.bell x)/2-β*((Fintype.card Signed:ℝ)⁻¹*(∑ i,purse T x M q d l β i)):=by
 unfold Cay.adjust purse wheel; simp_rw [sum_sub_distrib,mul_sub ((Fintype.card Signed:ℝ)⁻¹),media_q S]; have hh:= trim T x M q d l β hr; dsimp only at hh; linarith only [hh] -- tune
lemma reform(N:Monk G S)(S₀: M.zoo x≃ N.zoo x)(D:Equiv.Perm (Slots S))(he:∀ i,purse T x N q d l β i=purse T x M q d l β (D i))(hp:∀ i,‖N.bell x (S₀ i)‖=‖M.bell x i‖): adjust T x q d l β N= adjust T x q d l β M:=by
 have ht:costU (N.bell x)=costU (M.bell x):=by unfold costU; simp_rw [SectorChange.price_square, tape.apply_symm_apply]; rw [← Equiv.sum_comp S₀]; exact sum_congr rfl fun i _=>by rw [hp]
 rw [trail _ _ _ _ _ _ _ hr,trail _ _ _ _ _ _ _ hr, ht]; simp_rw [he]; rw [Equiv.sum_comp]
include p h hm hf
lemma adjust_s(s: Signed)(b:Site c): adjust T x q d l β (clue S s b M)= adjust T x q d l β M:=by
 let Y:=calendar x M.key M.park s b; refine reform T x M q d l β hr (clue S s b M) Y.onKey.symm Y.slots (capX T x M q d l β h p hm hf s b) ?_; intro i; let j:= Y.onKey.symm i; have he : ‖(clue S s b M).bell x j‖=‖M.bell x (Y.onKey j)‖:= (fiber s b M.V S j.val.val).norm_map _; exact he.trans (congrArg (fun z=>‖M.bell x z‖) (Y.onKey.apply_symm_apply i))
include hA
lemma adjust_f:adjust T x q d l β (cedar M)= adjust T x q d l β M:= reform T x M q d l β hr (cedar M) (Equiv.refl _) (Equiv.refl _) (purs_e T x M q d l β h p hm hf hA) (fun i=>frolic.norm_map _)
end
open Matrix
lemma stripe_e(P:ColorOrtho SU.group (Bond f))(S:Equiv.Perm (Bond f))(e)(b:Directions G f):Tensor.lifting P S (arrow (S e) b)= arrow e (Tensor.lifting P S b):=by
 funext i; simp_rw [Tensor.lifting_apply]; by_cases h:i=e
 · subst i; rw [arrow,arrow,Pi.single_eq_same,Pi.single_eq_same]; rfl
 unfold arrow; rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne (fun k=> h (S.injective k)),map_zero]
lemma shape_h(M N:Monk G S)(i:Bond f)(P: ColorOrtho SU.group (Bond f))(D:Equiv.Perm (Bond f))(Y Y': Monk G S→ℝ)(he:Y' ∘ rough N ∘ Tensor.lifting P D=Y ∘ rough M)(p:N.z=Tensor.lifting P D M.z): spring Y (D i) M=spring Y' i N:=by
 let F:=Y ∘ rough M; let H:=Y' ∘ rough N; let W:=Tensor.lifting P D; let a:=arrow (D i) M.z; have hh:W a=arrow i N.z:=by unfold W a; rw [p,stripe_e]
 change fderiv ℝ F 0 a+ hdot F 0 M.z a/2=fderiv ℝ H 0 _+_
 refine congrArg₂ (·+·) ?_ (congrArg (·/(2:ℝ)) ?_) -- tune
 · rw [show F=H ∘ W from he.symm,W.comp_right_fderiv,map_zero, ContinuousLinearMap.comp_apply]; change fderiv ℝ H 0 (W a)=_; rw [hh]
 have he':=derive2P H F W he M.z a; rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply,p.symm,show W a= _ from hh] at he'; exact he'.symm
lemma shine_p(M N:Monk G S)(P: ColorOrtho SU.group (Bond f))(D:Equiv.Perm (Bond f))(Y Y': Monk G S→ℝ)(he:Y'∘ rough N ∘Tensor.lifting P D=Y ∘ rough M)(p:N.z=Tensor.lifting P D M.z): shotB Y M=shotB Y' N:=by
 let H:=Tensor.lifting P D; let F:=Y' ∘ rough N; unfold shotB ash secT; rw [←bean_m, ←bean_m]; rw [show ∑ i,spring Y i M= ∑ i,spring Y' i N from by rw [←Equiv.sum_comp D]; exact sum_congr rfl fun i _=>shape_h M N i P D Y Y' he p]; -- now don't rewrite p below inside sum
 have hC:(Y ∘ rough M) M.z=(Y' ∘ rough N) N.z:=(congrFun he M.z).symm.trans (congrArg F p.symm)
 have hD:(Y ∘ rough M) 0=F 0:= (congrFun he 0).symm.trans (congrArg F (map_zero H)); rw [hC,hD]
end YM.CF.Rink
