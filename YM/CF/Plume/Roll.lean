import YM.CF.Lich.Spear
import YM.CF.Eire.King
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open scoped Classical ENNReal
-- integral roll with two independent fields. programmable split. probability sandwiches flags
section sw
variable {E F:Type*}[MeasurableSpace E][MeasurableSpace F]
def rollQ(f:E→E→E)(x:E×E): E×E:= (f x.1 x.2, f x.2 x.1)
def bothQ(f:E→E→E)(g:F→F→F)(x y:E×F):= (f x.1 y.1,g x.2 y.2)
def reQ(x:(E×F)×(E×F)):=(x.1.1,x.2.1,x.1.2,x.2.2)
def packQ(x:(E×F)×(E×F)):= ((x.1.1,x.2.1),x.1.2,x.2.2)
def nestQ(x:(E×E)×(F×F)) := ((x.1.1,x.2.1), x.1.2,x.2.2)
lemma pack_m (μ:Measure E)(ν:Measure F)[SFinite μ][SFinite ν]: MeasurePreserving packQ ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)):=by
 let A:= μ.prod ν
 have ht:= measurePreserving_prodAssoc ν μ ν; have hp:MeasurePreserving (fun x:F × E × F=> (x.2.1,x.1,x.2.2)) (ν.prod A) (μ.prod (ν.prod ν)):= (measurePreserving_prodAssoc μ ν ν).comp (((Measure.measurePreserving_swap (μ:=ν) (ν:=μ)).prod (MeasurePreserving.id _)).comp ht.symm) -- maybe arguments
 exact (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm.comp (((MeasurePreserving.id _).prod hp).comp (measurePreserving_prodAssoc μ ν A))
lemma nest_m (μ:Measure E)(ν:Measure F)[SFinite μ][SFinite ν]: MeasurePreserving nestQ ((μ.prod μ).prod (ν.prod ν)) ((μ.prod ν).prod (μ.prod ν)):=by
 let W : (E× F)×(E×F)≃ᵐ(E×E)×(F×F):= {toFun:=packQ, invFun:=nestQ,left_inv:=fun _=> rfl,right_inv:=fun _=>rfl,measurable_toFun:= (pack_m μ ν).measurable, measurable_invFun:=by change Measurable (nestQ (E:=E) (F:=F)); unfold nestQ; fun_prop}
 exact (show MeasurePreserving W _ _ from pack_m μ ν).symm
lemma roll_m (μ:Measure E)(ν:Measure F)[SFinite μ][SFinite ν](f:E→E→E)(g:F→F→F)(h:MeasurePreserving (rollQ f) (μ.prod μ) (μ.prod μ))(p:MeasurePreserving (rollQ g) (ν.prod ν) (ν.prod ν)): let ψ:=μ.prod ν; MeasurePreserving (rollQ (bothQ f g)) (ψ.prod ψ) (ψ.prod ψ):=by
 intro ψ; exact (nest_m μ ν).comp ((h.prod p).comp (pack_m μ ν))
def treatQ(f:E→E→ E):Prop:=∀ x y,f (f x y) (f y x)=x
lemma treat_m(f:E→E→ E)(g:F→F→ F)(h:treatQ f)(p:treatQ g):treatQ (bothQ f g):=by rintro ⟨i,j⟩ ⟨v,k⟩; exact Prod.ext (h i v) (p j k)
lemma roll_in(f:E→E→E)(h:treatQ f): Involutive (rollQ f):=fun ⟨u,v⟩=> Prod.ext (h u v) (h v u)
-- transport pi using pair projection
variable{A:Type*} [Fintype A]
def prQ(X:A→Prop)[DecidablePred X](u v:A→E)(i:A):=if X i then u i else v i
lemma pr_t(X:A→Prop)[DecidablePred X]:treatQ (E:=A→E) (prQ X):=by intro x y; funext a; by_cases h:X a <;> simp [prQ,h]
lemma pr_m (X:A→Prop)[DecidablePred X](P:A→Measure E)[∀ i,SigmaFinite (P i)]: let ν:=Measure.pi P; MeasurePreserving (rollQ (prQ X)) (ν.prod ν) (ν.prod ν):=by
 intro ν; let W:= MeasurableEquiv.piEquivPiSubtypeProd (fun _:A=>E) X
 have hp : MeasurePreserving W ν _:= measurePreserving_piEquivPiSubtypeProd P X
 have ht:=hp.prod hp; have hx:=hp.symm.prod hp.symm; let L:=Measure.pi (fun i:Subtype X=> P i); let V:=Measure.pi (fun i:Subtype (fun i=>¬ X i)=> P i)
 let W':=((MeasurePreserving.id (L.prod L)).prod (Measure.measurePreserving_swap (μ:=V) (ν:=V))) -- name
 have H:MeasurePreserving (fun x:(A→E)×(A→E) => let q:=packQ ((W x.1,W x.2)); let p:=nestQ (q.1,q.2.swap); (W.symm p.1,W.symm p.2)) (ν.prod ν) (ν.prod ν):=hx.comp ((nest_m L V).comp (W'.comp ((pack_m L V).comp ht)))
 convert H using 1; funext x; apply Prod.ext
 all_goals apply W.injective; dsimp only; rw [W.apply_symm_apply]; apply Prod.ext <;> (funext i; change prQ X _ _ i.val =_; simp only [prQ])
 all_goals first| rw [if_pos i.property]; rfl| rw [if_neg i.property]; rfl
end sw
end YM.CF.Plume
