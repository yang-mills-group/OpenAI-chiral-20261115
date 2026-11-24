import YM.CF.Slate.Para
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
variable {k:S.Choices}{s u C D:ℝ}{F:Forest S.ratio}
def glow(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(z: Directions G f)(v:Mast G c): Fish (Key F G):=let Y:=fun i:Active (bareStores S) x F=>z i.val.val; μ₁ T F x k q d s l v *ᵥ (visitX F x (tape.symm Y))
lemma shineC {g: Monk G S}(p:g.key=bareStores S)(h:K.Funds S T)(v:Mast G c)(hp:satU G s v=g.V)(u:Dill S)(i:Signed)(hv:Fire T x g.park g.k l s n C v): Slate.payer T x g q d l β i u = Slate.taste T g.park x g.k l i u (s•v,coupling β • glow T x g.park g.k s q d l g.z v):=by
 obtain ⟨K',F,k,V,U,z⟩:=g; dsimp only at p hp hv; subst K' V; let M:Monk G S:=⟨bareStores S,F,k,satU G s v,U,z⟩; let V:=M.V; let A:=M.key; let Y:=tape.symm (M.bell x); let J:= credW T M.key F k q d x (M.bush x) l V; let w:Fish (Key F G):=glow T x F k s q d l z v; let t:=coupling β; let X:= M.sent x T q d l β; let a:=Newt.sol S T k x F l (s•v); let W: Ark T F:= (s•v,t • w); let O:=a+(t•w); have ep:M.bush x=1:= funext fun i=>False.elim ((notChilled S F x i.val) i.property); have he:liftN T x V k A F q d (M.bush x) l=leaveX F x a:=by
    rw [ep,←(hv.shine q d).2]; funext i; unfold liftN; rw [if_pos]; unfold green; simp [A,M,bareStores,Stores.dome,Stores.place,halo_spec] -- tune
 have hp:J *ᵥ Y=leaveX F x w:=by
    let z:=visitX F x Y; have hz:w= Souk.μ₁ T F x k q d s l v *ᵥ z:=rfl; rw [hz]; conv_lhs=>rw [show Y=leaveX F x z from (visit_right ..).symm]
    have ht:=tableVisit F x J; change paintO J _=_; have hQ: J.submatrix (pageX F x) (pageX F x)= Souk.μ₁ T F x k q d s l v:=by unfold J; rw [ep]; rfl
    change _= leaveX F x (paintO _ z); rw [←hQ,ht]; exact (visit_right ..).symm
 have hs:M.fuel x T q d l β=leaveX F x (t•w+a):=by
    unfold Monk.fuel realP spinC; rw [show M.V=V from rfl]; change liftN T x V k A F q d (M.bush x) l+t • (J *ᵥ Y)=_; rw [he,hp,map_add,map_smul,add_comm]
 have hf : pull i 0 X=fX T x F k i l W:=by
    change pull _ _ (landed x M.key M.park M.V (M.bush x) (M.fuel x T q d l β)) =_
    rw [hs,ep]; exact congrArg (pull i 0) ((landed_exit (satU G s v) (x:=x) (F:=F) (t•w+a)).trans (tray_x F x (s•v) (t•w+a)))
 change Slate.payer T x M q d l β i u= Slate.taste T F x k l i u W; let L:= liftN T x V k A F q d (M.bush x) l; let Ψ:= wheel A F T x k q d (M.bush x); rw [tinB (d:=d) (q:=q) K T F x k l i h]; change Yaught T _ _ _ (pull i 0 V) (pull i 0 X) _ u-Gloss S i (fun j=> media j (Ψ (M.fuel x T q d l β) V)-media j (Ψ L V)) u=_; rw [hs,hf,show L= _ from he]; unfold Ψ; rw [ep]
lemma glow_p {v:Mast G c}(g:Fire T x F k l s n C v)(z:Directions G f)(p:‖z‖≤ D): Allows n (glow T x F k s q d l z) v (D*C):=by
 let Y:LogArray G (Active (bareStores S) x F):= fun i=>z i.val.val; let a:=visitX F x (tape.symm Y);
 have hv:= (g.flame q d).1; let A:= jump_up (leaveX F x) (visitX F x) (visit_n ..) (leave_n ..) hv
 have he: Protected n (μ₁ T F x k q d s l) v C:=A.germ (Eventually.of_forall fun i=>by change _=paintO (μ₁ T F x k q d s l i); unfold μ₁; rw [tableVisit]; rfl)
 have ht:‖a‖≤ D:=by
    refine ((visitX F x).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (visit_n ..)).trans ?_)
    exact (loomP _).trans ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans p)).mpr fun i=> (norm_le_pi_norm z i.val.val).trans p)
 exact he.linear (ContinuousLinearMap.apply ℝ _ a) (ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans p) fun b=> (b.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_comm ..)))
end YM.CF.Slate
