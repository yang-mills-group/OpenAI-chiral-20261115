import YM.CF.Cay.Ton
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
local notation "Z"=>Directions G f
local notation "ζ"=> Monk G S
def rough(M:Monk G S)(z:Directions G f):Monk G S:={M with z:=z}
-- beat footprint. hens
abbrev Virt(S:StepData c f)(Y:Monk G S→ A)(X:Support c):Prop:=∀ ⦃M N⦄, Beat M N X→ Y M=Y N
lemma coat{M N: ζ}{X:Support c}(p:Beat M N X){u v: Z}(h:∀ i, Next.SectorChange.points S i ⊆ X→u i=v i): Beat (rough M u) (rough N v) X:=⟨p.road,p.fr,p.fe,p.trunks,p.view,p.data,h⟩
lemma selfC(M:Monk G S) (X:Support c): Beat M M X:=⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma fixat(f:E→A)(u x:E)(p:∀ (y:E)(a:ℝ), f (y+a•u)=f y) : fderiv ℝ f x u=0:=by
 by_cases h:DifferentiableAt ℝ f x
 · let g :ℝ→ E :=fun a=> x+a • u; have he:g 0=x:=by simp [g]
   have hv:DifferentiableAt ℝ f (g 0):=he.symm ▸ h
   have hg: HasDerivAt g u 0:= by simpa [g] using HasDerivAt.const_add x ((hasDerivAt_id' (x:=(0:ℝ))).smul_const u)
   have hh: HasDerivAt (fun t=>f (g t)) (fderiv ℝ f x u) 0:=by have he':= hv.hasFDerivAt.comp_hasDerivAt (0:ℝ) hg; exact (show fderiv ℝ f (g 0)=fderiv ℝ f x by rw [he]) ▸ he'
   rw [show (fun t=>f (g t))=(fun _=> f x) from funext (p x)] at hh; exact hh.unique (hasDerivAt_const _ _)
 rw [fderiv_zero_of_not_differentiableAt h,_root_.zero_apply]
lemma fixed(f:E→A)(u x:E)(p:∀ (y:E)(a:ℝ), f (y+a•u)=f y) : hdot f x u=0 ∧ ∀ v, hdot f x v u=0:=by
 refine ⟨fixat _ _ _ ?_,?_⟩
 · intro y a; rw [← fderiv_comp_add_right, show (fun y=>f (y+a•u))=f from funext fun z=>p z a]
 intro v; let X:= fderiv ℝ f; let L:= ContinuousLinearMap.apply ℝ A u; by_cases h:DifferentiableAt ℝ X x
 · have he:L ∘ X=(fun _=>0):=funext fun z=>fixat f u z p
   change L (fderiv ℝ X x v)= _
   rw [← ContinuousLinearMap.comp_apply,← (show fderiv ℝ (L ∘ X) x=L.comp (fderiv ℝ X x) from (L.hasFDerivAt.comp x h.hasFDerivAt).fderiv),he]; simp
 unfold hdot; rw [fderiv_zero_of_not_differentiableAt h]; rfl
lemma vanish{M:ζ}{Y:Monk G S→ℝ}{X:Support c}(p:Virt S Y X)(u:Directions G f)(h:∀ i,Next.SectorChange.points S i⊆ X→u i=0): let Q:=Y ∘ rough M; fderiv ℝ Q 0 u=0 ∧ hdot Q 0 u=0 ∧ ∀ v, hdot Q 0 v u=0:=by
 intro Q; have he(y:Z)(a:ℝ): Q (y+a•u)=Q y:= p (coat (selfC M X) (fun i k=>by rw [Pi.add_apply, Pi.smul_apply,h i k,smul_zero,add_zero])); exact ⟨fixat Q u 0 he,fixed Q u 0 he⟩
variable {X:Support c}{Y:Monk G S→ℝ}
def spring(Y: ζ → ℝ)(e: Bond f)(M:ζ):= let f:=Y∘ rough M; let z:=arrow e M.z; fderiv ℝ f 0 z + hdot f 0 M.z z/2
lemma stanza {X:Support c}(p:Virt S Y X)(e:Bond f): Virt S (spring Y e) X:=by
 intro M N h; let g:=Y ∘ rough M; have he:g=Y ∘ rough N:=funext fun i=>p (coat h fun _ _=>rfl)
 by_cases ht:Next.SectorChange.points S e ⊆ X
 · let z:=arrow e M.z; have hz:z=arrow e N.z:=congrArg (Pi.single e) (h.color _ ht)
   have hp:(hdot g 0) (M.z-N.z)=0:=(vanish p _ fun i u=>by simp only [Pi.sub_apply,h.color i u,sub_self]).2.1
   unfold spring; rw [← he,← show g=Y ∘ rough M from rfl,show arrow e N.z=z from hz.symm]; rw [map_sub,sub_eq_zero] at hp; dsimp only; rw [hp]
 have hh(M:ζ):spring Y e M=0:=by
    obtain ⟨u,v,t⟩:= vanish (M:=M) p (arrow e M.z) fun i p=> Pi.single_eq_of_ne (show i ≠ e from fun k=> ht (k ▸ p)) _; unfold spring; simp only [u,t,zero_div,add_zero]
 rw [hh,hh]
lemma off(p:Virt S Y X)(e:Bond f)(u:S.ratio.parent e.1∉X)(M:ζ): spring Y e M=0:=by
 obtain ⟨h,v,t⟩:=vanish (M:=M) p (arrow e M.z) (fun i p=> Pi.single_eq_of_ne (show i ≠ e from fun k=> u ((show Next.SectorChange.points S e ⊆ X from k ▸ p) (show _ from Set.mem_insert ..))) _); unfold spring; simp only [h,t,zero_div,add_zero]
end YM.CF.Cay
