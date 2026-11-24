import YM.CF.Cay.Sham
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
open Matrix
open Souk (μ₁)
variable {g:Site c→SU.group.El} {R:Directions G c→ Mast G c} {s C D:ℝ}{A: Monk SU.group S} {k:S.Choices}
def lava(T:Tube G S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(l:ℕ)(i:Signed):Along S→ Ark T F→ℝ:= Sum.elim (taste T F x k l i) (Sum.elim (parchF T x F k i l) (fun j v=> -parchC T x F k i j v))
lemma lava_w(p:A.key=bareStores S)(h:K.Funds S T)(v:Mast G c)(hp:A.V=satU G s v)(u:Along S)(i:Signed)(hv:Fire T x A.park A.k l s n C v): stars T x A q d l β i u= lava T A.park x A.k l i u (s • v,coupling β • glow T x A.park A.k s q d l A.z v):=by
 let F:=A.park; let z:=coupling β • glow T x A.park A.k s q d l A.z v; let W:Ark T F:= (s • v,z); rcases u with u|u|u
 · exact shineC p h v hp.symm u i hv
 · let Y:=z+sol S T A.k x F l (s • v); have hh:pull i 0 (A.sent x T q d l β)= fX T x F A.k i l W:=by rw [shineU p v hp hv,hp]; exact congrArg (pull i 0) (tray_x F x (s • v) Y)
   unfold stars; simp only [Sum.elim_inr,Sum.elim_inl,hh]; rfl
 unfold stars; simp only [Sum.elim_inr,hp]; rfl
lemma lava_p(P:Patch)(K:Teller SU.group)(p:P.Branches K.bind G)(n l:ℕ)(hp:3 ≤ n)(W: Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)):∃ D E:ℝ,0<D∧0<E∧∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x→ sizedP G P K S T F→ ∀ k:S.Choices,∀(u:Along S)(i:Signed), KnotP (lava T F x k l i u) n (D*temp x^(l+1)) D E:=by
 obtain ⟨A,H,hA,hH,h⟩:=tinPaid P K p n l hp W; obtain ⟨A',H',hA',hH',h'⟩:= Vol.ping K p Thera.yet_one n l hp W
 let D:=max A A'; have hD:0<D:=lt_of_lt_of_le hA (le_max_left ..); refine ⟨D,min H H',hD, lt_min hH hH',?_⟩; filter_upwards [h,h'] with x hK hQ c f S T F P H k u i; have hp':0≤ D*temp x^(l+1):=mul_nonneg hD.le (pow_nonneg (temp_nonneg _) _)
 obtain ⟨hz,hx⟩:= hQ S T F P H k i
 rcases u with u|u|u
 · exact (hK S T F P H k i u).mono (mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg (temp_nonneg _) _)) (le_max_left ..) (min_le_left ..)
 · exact (hz u).mono hp' (le_max_right ..) (min_le_right ..)
 have ht:=(hx u).scale (-1) hH' (by omega); simp only [abs_neg,abs_one,one_mul,neg_one_smul] at ht; exact ht.mono hp' (le_max_right ..) (min_le_right ..)
lemma rosy {s C C₀ D ε:ℝ}(p:A.key=bareStores S)(h:K.Funds S T)(v:Mast G c)(hp:A.V=satU G s v)(i:Signed)(j: Along S)(hz:Fire T x A.park A.k l s n C v)(hv:‖v‖<1)(hy:0<s)(hr:s ≤ ε)(hu: KnotP (lava T A.park x A.k l i j) n D C₀ ε): ContDiffAt ℝ (n:WithTop ℕ∞) ((fun A=>stars T x A q d l β i j) ∘ rough A) 0:=by
 let B:= (paintO (μ₁ T A.park x A.k q d s l v)).comp (nub A.park x); let T'(w): Ark T A.park:= (s•v, coupling β • B w)
 have he:‖T' 0‖< ε:=by unfold T'; rw [Prod.norm_def,norm_smul_of_nonneg hy.le,map_zero,smul_zero,norm_zero]; exact max_lt ((mul_lt_of_lt_one_right hy hv).trans_le hr) (hy.trans_le hr)
 refine ((hu.sails _ he).smooth.comp (f:=T') _ (contDiffAt_const.prodMk (B.contDiff.contDiffAt.const_smul _))).congr_of_eventuallyEq ?_
 exact Eventually.of_forall fun i'=> lava_w (A:=rough A i') p h v hp j i hz
end YM.CF.Cay
