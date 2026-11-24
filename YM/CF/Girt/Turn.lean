import YM.CF.Girt.Shore
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
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
section fig
open scoped Classical
variable {E X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] [MeasurableSpace E][BorelSpace E][SecondCountableTopology E][MeasurableSpace X][MeasurableSpace Y]
omit [MeasurableSpace E] [BorelSpace E][SecondCountableTopology E] in
lemma hinge {μ:Measure X}{ν:Measure Y}(F:X→Y)(G:Y→E)(p:MeasurePreserving F μ ν)(h:Integrable G ν): (∫ i,G i∂ν)= ∫ i,G (F i) ∂μ:= by
 rw [←p.map_eq]; apply integral_map p.aemeasurable; rw [p.map_eq]; exact h.aestronglyMeasurable
lemma normP {I J:Type}[Fintype I][Fintype J](μ:Measure Y)[IsProbabilityMeasure μ](v:I→J)(p:Injective v):MeasurePreserving (fun x:J→ Y=> x ∘ v) (Measure.pi fun _:J=>μ) (Measure.pi fun _:I=>μ):=by
 let Q:= Measure.pi fun _:J=>μ; let f(j:J)(x:J→Y):=x j; have ht (j): MeasurePreserving (f j) Q μ:= measurePreserving_eval _ _
 letI:IsProbabilityMeasure Q:=by unfold Q; infer_instance
 have hx:ProbabilityTheory.iIndepFun f Q:=by exact ProbabilityTheory.iIndepFun_pi (fun j=> (measurable_id (α:=Y)).aemeasurable (μ:=μ)) -- tune j unused
 have hp:ProbabilityTheory.iIndepFun (fun i:I=> f (v i)) Q:= ProbabilityTheory.iIndepFun.precomp p hx -- tune
 have he := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (fun i=>(ht (v i)).measurable.aemeasurable)).mp hp
 refine ⟨measurable_pi_lambda _ (fun i=>(ht _).measurable),?_⟩; simp_rw [(ht _).map_eq] at he; exact he
open Oriented Presented RG Next.SectorChange Next.Fluctuations.Sector SectorNext.Remainder.Affine CF.Appel Pressure.Stores CF.Forge AnalyticBridge.Annulus1AD
variable {m c f:Side} {S:StepData c f}(T':Tube G₀ S)(x β :ℝ) (V:Config G₀ c)(F:Forest S.ratio)(A:Stores S)(i:S.Choices)(B':Allocation G₀ S x W)(U:Config G₀ f→E)
variable (q':Chi)(J:ChartRatio G₀)(d s:ℝ)(l:ℕ)(h:0<W)(ht:0<fiery G₀ x S.patch.L)
variable {z N':ℝ}
def suit {c f:Side}(S:StepData c f):Measure (Config G₀ f):= prior G₀ f -- tune
abbrev plight (W:ℝ)(M:Monk G₀ S):=glowV W T' x β M.V M.park M.key M.k q' J d l (M.bush x) (M.bell x)
variable {l':ℕ}
lemma patchL (hβ:0<β)(t:MossX l' l x A F T' V i z d N' q')(v:A.flags=flags (temp x) V)(H:Teller G₀)(w:H.Funds S T')(k:LocalRatio J)(g:4*d<J.radius)(hg:0<d)(hs:wireP G₀ (coupling β) d (z*N') z ≤ s)(hy:0<s)(p:Standing (F:=F) (A:=A) (q'.profiles G₀ S x W h ht) J d i V)(L: RG.Envelope U): let B:=q'.profiles G₀ S x W h ht
 let Ω:= (suit S).prod (tableG G₀ (Bond f) s)
 let j(Q: Config G₀ f× Directions G₀ f):= let M:Monk G₀ S:=⟨A,F,i,V,Q.1,Q.2⟩; plight T' x β q' J d l W M • U (M.sent x T' q' d l β)
 Integrable j Ω ∧ (∫ a, B.portion A F V (through S F β V (fun _ a=> U (F.drape a))) i a ∂F.order G₀)= (prefactor S G₀ β*(spare J β*point G₀ s)^Fintype.card (Active A x F)) • ∫ Q, j Q ∂Ω:=by
 intro B Ω j; obtain ⟨hu,he,hv⟩:= pom T' x β V F A i U q' J d s l h ht hβ t v H w k g hg hs hy p L
 let l0:=fun j:Frozen A x F=> j.val.val; let l1:= fun i:Active A x F=>i.val.val; let I:= piHaar G₀ (Frozen A x F); let M:= tableG G₀ (Active A x F) s; letI:IsProbabilityMeasure M:=how G₀ hy; haveI:=Appel.feast_nn G₀ hy; haveI:IsProbabilityMeasure (suit S):=by unfold suit; infer_instance
 let j'(i':LinkArray G₀ (Frozen A x F)×LogArray G₀ (Active A x F)):=glowV W T' x β V F A i q' J d l i'.1 i'.2 • U (fieldU β T' F A V i x l q' d i'.1 i'.2); have hE:Integrable j' (I.prod M):=he
 let Φ(Q: Config G₀ f × Directions G₀ f):=(Q.1 ∘ l0,Q.2 ∘ l1)
 have hK: MeasurePreserving Φ Ω (I.prod M):=by exact (normP SU.group.probHaar l0 (fun x y p=> Subtype.ext (Subtype.ext p))).prod (normP (Appel.feast G₀ s) l1 (fun x y p=> Subtype.ext (Subtype.ext p)))
 rw [show j=j'∘Φ from rfl]; refine ⟨hK.integrable_comp_of_integrable hE,?_ ⟩; rw [hv]; rw [← show (∫ i,j' i∂(I.prod M))=_ from integral_prod j' hE, hinge Φ j' hK hE]; rfl
end fig
end YM.CF.Girt
