import YM.CF.Girt.Turn
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
open scoped Classical
open Oriented Presented RG Next.SectorChange Next.Fluctuations Next.Fluctuations.Sector SectorNext.Remainder.Affine CF.Appel Pressure.Stores CF.Forge AnalyticBridge.Annulus1AD
section u
variable {m r b:Side} {S:StepData b r}(T':Tube G₀ S)(x β :ℝ) (V:Config G₀ b)(F:Forest S.ratio)(A:Stores S)(i:S.Choices)
variable (q':Chi)(J:ChartRatio G₀)(d s:ℝ)(l:ℕ){z N':ℝ}
abbrev youthℓ (U:Config G₀ r × Directions G₀ r): Monk G₀ S:=⟨A,F,i,V,U.1,U.2⟩
open Next.SectorChange.Gaussian
lemma put_mE (oT:ℕ)(p:MossX oT l x A F T' V i z d N' q') : Measurable (uncurry (putU β T' F A V i x l q' d)) :=by
 let f:=fun y:LinkArray G₀ (Frozen A x F) × LogArray G₀ (Active A x F)=> putU β T' F A V i x l q' d y.1 y.2
 change Measurable f; unfold f putU realP spinC; simp_rw [p.still]; exact tape.measurable.comp ((p.moves.measurable.comp measurable_fst).add (((Gaussian.acts_meas _).comp (tape.symm.measurable.comp measurable_snd)).const_smul (coupling β)))
lemma sendL(oT:ℕ)(pE:MossX oT l x A F T' V i z d N' q'): Measurable fun U: Config G₀ r × Directions G₀ r=> (youthℓ V F A i U).sent x T' q' d l β :=by
 let Ξ:= Config G₀ r × Directions G₀ r; let f(U:Ξ):LinkArray G₀ (Frozen A x F) :=fun w=> U.1 w.val.val; let g(U:Ξ): LogArray G₀ (Active A x F) :=fun j=> U.2 j.val.val
 have hf:Measurable f:= measurable_pi_lambda _ fun i:Frozen A x F=> (measurable_pi_apply i.val.val).comp measurable_fst; have hg:Measurable g:= measurable_pi_lambda _ fun i:Active A x F=> (measurable_pi_apply i.val.val).comp measurable_snd
 let fy(U:Ξ):=putU β T' F A V i x l q' d (f U) (g U); let H:= fun U:Ξ=>(f U,g U); have hm:Measurable fy:= by
    have hp:= hf.prodMk hg; exact (put_mE T' x β V F A i q' d l oT pE).comp (f:=H) hp -- tune parameter
 let Lj:= uncurry (Next.SectorChange.physical (x:=x) A F V); have he:Measurable (Lj ∘ (fun U:Ξ=> (f U,fy U))) := (show Measurable Lj from physical_meas (x:=x) A F V).comp (hf.prodMk hm); exact he
end u
open Scroll
variable {f n :Side}{e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
open scoped Classical
variable (V:Orbit (mid M B))(F: Forest T.ratio)(S:Tube SU.group T)(A: Stores T)(i:T.Choices)(q':Chi)(R':ChartRatio SU.group)(d' s:ℝ)(l:ℕ)(hW:0<W)(he:0<fiery SU.group x T.patch.L)
variable {z l':ℕ} {h K U₀ :ℝ}
abbrev land:= youthℓ V.1 F A i
-- Exact integrability not OR
include X p t
lemma pock (hβ:0<R.beta)(h:MossX l' l x A F S V.1 i K d' U₀ q')(hv:A.flags=RG.flags (temp x) V.1)(H:Teller G₀)(hw:H.Funds T S)(k:LocalRatio R')(hu:4*d'< R'.radius)(hf:0<d')(hs:wireP G₀ (coupling R.beta) d' (K*U₀) K ≤ s)(hy:0<s)(hp:Standing (F:=F) (A:=A) (q'.profiles G₀ T x W hW he) R' d' i V.1): let B' := q'.profiles G₀ T x W hW he
 let Ω:=((suit T).prod (tableG G₀ (Bond (Domain C B)) s)).prod (depot (mid C B))
 let g(W':(Config G₀ (Domain C B) × Directions G₀ (Domain C B))× Ids (mid C B)):= let M :=youthℓ V.1 F A i W'.1; plight S x R.beta q' R' d' l W M • waveV P G R F₁ F₂ q u (p ▸ F) V (M.sent x S q' d' l R.beta,W'.2)
 Integrable g Ω∧ (∫ a, B'.portion A F V.1 (through T F R.beta V.1 (fun _ a=> ropeG P G R F₁ F₂ q u (p ▸ F) V (F.drape a))) i a ∂F.order G₀)= (prefactor T G₀ R.beta*(spare R' R.beta*point G₀ s)^Fintype.card (Active A x F)) • ∫ Q, g Q ∂Ω:=by
 intro B' Ω Q
 obtain ⟨hq,g⟩:= patchL S x R.beta V.1 F A i _ q' R' d' s l hW he hβ h hv H hw k hu hf hs hy hp (grain X (p ▸ F) V)
 let X':= Config SU.group (Domain C B) × Directions G₀ (Domain C B)
 let M:= mid C B; let f(U:X'):= plight S x R.beta q' R' d' l W (youthℓ V.1 F A i U); let Y(U:X'):= (youthℓ V.1 F A i U).sent x S q' d' l R.beta -- shadow F!
 let ν:= (suit T).prod (tableG G₀ (Bond (Domain C B)) s)
 letI :IsProbabilityMeasure ν:=by
    unfold ν; haveI:IsProbabilityMeasure (suit T):=by unfold suit; infer_instance
    haveI:= how (α:=Bond (Domain C B)) G₀ hy; infer_instance
 have ha:Measurable Y:=sendL S x R.beta V.1 F A i q' d' l l' h
 let T'(x: X' × Ids M):= waveV P G R F₁ F₂ q u (p ▸ F) V (Y x.1,x.2); have ht:RG.Envelope T':= snap (X:=fun x:X' × Ids M=>(V,Y x.1,x.2)) (entersL X (p ▸ F)) (measurable_const.prodMk ((ha.comp measurable_fst).prodMk measurable_snd))
 have h₁:Integrable f ν:=by
    obtain ⟨hr,hv⟩:= patchL S x R.beta V.1 F A i (fun _=>(1:ℝ)) q' R' d' s l hW he hβ h hv H hw k hu hf hs hy hp (Envelope.const _); apply hr.congr (Eventually.of_forall _); intro i; change f i • (1:ℝ)= _; simp
 have h':Integrable Q Ω:=by obtain ⟨C,h⟩:= ht.cost; exact (h₁.comp_fst (depot M)).smul_bdd C ht.meas.aestronglyMeasurable (Eventually.of_forall h)
 refine ⟨h',?_⟩; rw [g, integral_prod Q h']; unfold Q ropeG; simp_rw [integral_smul]
end YM.CF.Girt
