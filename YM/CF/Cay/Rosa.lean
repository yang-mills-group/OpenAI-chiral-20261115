import YM.CF.Cay.Left
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
open Push.Uniform (lowerCol Primary Positions block Slope bolt)
variable {k:S.Choices}{s C:ℝ}
def means(F:Forest S.ratio)(k:S.Choices)(U:Config G f)(s:ℝ)(v:Mast G c)(z: Directions G f): Monk G S:=⟨bareStores S,F,k,satU G s v,U,z⟩
lemma shineU {g: Monk G S}(p:g.key=bareStores S)(v:Mast G c)(hp:g.V=satU G s v)(hv:Fire T x g.park g.k l s n C v): let u:= g.sent x T q d l β; let t:=coupling β • glow T x g.park g.k s q d l g.z v+ Newt.sol S T g.k x g.park l (s•v);
 u=increment (replica S.ratio g.V) (trays S x g.park t) :=by
 obtain ⟨K',F,k,V,U,z⟩:=g; dsimp only at p hp hv; subst K' V; let M:Monk G S:=⟨bareStores S,F,k,satU G s v,U,z⟩; let V:=M.V; let A:=M.key; let Y:=tape.symm (M.bell x); let J:= credW T M.key F k q d x (M.bush x) l V; let w:Fish (Key F G):=glow T x F k s q d l z v; let t:=coupling β; let X:= M.sent x T q d l β; let a:=Newt.sol S T k x F l (s•v); let W: Ark T F:= (s•v,t • w); let O:=a+(t•w); have ep:M.bush x=1:= funext fun i=>False.elim ((notChilled S F x i.val) i.property); have he:liftN T x V k A F q d (M.bush x) l=leaveX F x a:=by
    rw [ep,←(hv.shine q d).2]; funext i; unfold liftN; rw [if_pos]; unfold green; simp [A,M,bareStores,Stores.dome,Stores.place,halo_spec] -- tune
 have hp:J *ᵥ Y=leaveX F x w:=by
    let z:=visitX F x Y; have hz:w= Souk.μ₁ T F x k q d s l v *ᵥ z:=rfl; rw [hz]; conv_lhs=>rw [show Y=leaveX F x z from (visit_right ..).symm]
    have ht:=tableVisit F x J; change paintO J _=_; have hQ: J.submatrix (pageX F x) (pageX F x)= Souk.μ₁ T F x k q d s l v:=by unfold J; rw [ep]; rfl
    change _= leaveX F x (paintO _ z); rw [←hQ,ht]; exact (visit_right ..).symm
 have hs:M.fuel x T q d l β=leaveX F x (t•w+a):=by
    unfold Monk.fuel realP spinC; rw [show M.V=V from rfl]; change liftN T x V k A F q d (M.bush x) l+t • (J *ᵥ Y)=_; rw [he,hp,map_add,map_smul,add_comm]
 intro u p; change landed x M.key M.park M.V (M.bush x) (M.fuel x T q d l β) =_ ; rw [hs,ep]; exact landed_exit (satU G s v) (F:=F) (x:=x) (t•w+a)
lemma meek_x {G':Monk G S}(h:G'.key=bareStores S)(p:K.Funds S T)(v:Mast G c)(hg:G'.V=satU G s v)(hv: Fire T x G'.park G'.k l s n C v): let w:=s•v; let t:=coupling β • glow T x G'.park G'.k s q d l G'.z v; let z:=t+Newt.sol S T G'.k x G'.park l w; let U:=G'.sent x T q d l β;
 mainTerm T.high (grainA T.up (Stores.till x)) U+ noiseTaylor S G'.V U G'.k= clipped T x G'.park G'.k (pic T x G'.park G'.k l s v+lowerCol t):=by
 intro w t z U; rw [← show meetVar w z= pic T x G'.park G'.k l s v+lowerCol t from (by unfold z; rw [add_comm,cumu])]; rw [← clip_actual,rack_actual]; unfold U; rw [show G'.sent _ _ _ _ _ _=_ from shineU h v hg hv]; simp only [hg]; rfl -- tune
lemma jump_dot (p: Prices G (Active (bareStores S) x F)): p ⬝ᵥ p = visitX F x p ⬝ᵥ visitX F x p:= (Equiv.sum_comp (pageX («G»:=SU.group) F x) (fun i=>p i * p i)).symm
section
variable(T:Tube G S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(U:Config G f)(q:Chi)(d:ℝ)(l:ℕ)(β s:ℝ)
def nub(F:Forest S.ratio)(x:ℝ):Directions G f →L[ℝ] Fish (Key F G):= (visitX F x).comp ((Push.Uniform.tint G _).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi fun i:Active (bareStores S) x F=>ContinuousLinearMap.proj (φ:=fun _=> SU.group.Color) i.val.val))
def proxZ(v:Mast G c)(z:Directions G f):=aster T x (means F k U s v z) q d l β
lemma reflected(v:Mast G c)(h:Fire T x F k l s n C v)(p:K.Funds S T)(ht:0<β)(x' z':Directions G f): let P:=nub F x; let M:=Souk.μ₁ T F x k q d s l v; let W:=Char.clipped T x F k; let t:=pic T x F k l s v; let z:= proxZ T F x k U q d l β s v
 ContDiffAt ℝ ω z 0 ∧ fderiv ℝ z 0 x'= -β*coupling β *(P x' ⬝ᵥ (M.transpose *ᵥ Slope W t)) ∧ hdot z 0 x' z'= -(P z' ⬝ᵥ (perturb M (block W t) *ᵥ P x')):=by
 intro P M W t z; let d':=mainTerm T.low (grainA T.down (Hors.cart x S.patch.L)) (satU G s v); rw [show z= (fun i=> -β*(W (t+lowerCol (coupling β • (M*ᵥ P i)))-d')+(P i ⬝ᵥ P i)/2) from ?_]; exact amass W t M P h.serve β d' ht x' z'
 funext i; unfold z proxZ; let m:=means F k U s v i; rw [deck_x _ _ _ _ _ _ _ ht p,meek_x (G':=m) rfl p v (s:=s) rfl h]; change _+(costU _)/2=_; unfold costU; apply congr_arg₂ _ rfl; exact congrArg (fun x:ℝ=> x/2) (jump_dot (F:=F) (x:=x) (tape.symm (m.bell x)))
end
end YM.CF.Cay
