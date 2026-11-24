import YM.CF.Py.Cool
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Pyx
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
open Girt
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
variable (P:Grasp Y B e) (G:Ratio (CSide M B) (mid C B))(R:GramM (mid C B))(F₁:Scree.Loom (mid M B))(F₂:Scree.Loom (mid C B))(q:Chi)(u:ℝ)
variable {P G R F₁ F₂ q u}(X:BaseL P G R F₁ F₂ q u)(T:StepData (Domain M B) (Domain C B))(p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)
-- Explicit pull OF WAVE insertions, not multiplying independent detached expectations. Reader may be nonlocal/use auxiliary tags. SAME trial.Child. pure auxiliary ports.
variable (P G R F₁ F₂ q u)
abbrev tale (F:Forest (ratio G))(x:Orbit (mid M B))(y:Orbit (mid C B))(W: Phys (mid C B)):= T.density R.beta y.1 x.1 • fire (Vault.Thread j) G R.J.M (unionP (YF G F₁ F₂ q u F x y)) (cartsL (switchG G).symm W) -- P via j? P not used.include
local notation "J_"=> mid M B
variable {N:Side}
local notation "H_"=> mid C B
abbrev Oracle (n:Side):= Orbit n → Phys n→L[ℝ]ℂ
abbrev BoundedT (F:Oracle n):Prop:=∀ v:Phys n, Envelope fun x:Orbit n=>F x v
abbrev swipeP (F:Oracle J_)(y:Orbit H_)(x: Orbit J_)(W:Phys H_):ℂ:=F x ((Fintype.card (Forest (ratio G)):ℝ)⁻¹ • ∑ D,tale (j:=j) G R F₁ F₂ q u T D x y W) -- P argument order? future.
include X p t
-- use entrant envelope for general input variations
lemma flex(F:Forest (ratio G))(W:Orbit (mid M B)×Orbit (mid C B)→ Phys (mid C B))(b:Envelope W): Envelope fun z:Orbit J_ × Orbit H_ => tale (j:=j) G R F₁ F₂ q u T F z.1 z.2 (W z):=by
 obtain ⟨b',v,w,p,l⟩:= X.cap; obtain ⟨s,a,h,d,H,u',g⟩:= X.wick; let L'(Z: Orbit J_× Orbit H_):=YF G F₁ F₂ q u F Z.1 Z.2
 have hf:Measurable (fun i:Orbit J_× Orbit H_=>F₁ i.1) := p.bill.comp measurable_fst
 have he:Measurable L':= (((brake G q u F X.legal.1 X.legal.2).measurable.comp ((l.bill.comp measurable_snd).prodMk hf)).prodMk hf); let ψ:=R.J.M; have hh:= Girt.heat_k (pM:=ψ) X.power _ H u' g X.pe X.size L' W (fun z=>X.trial ..) he b
 apply Env.scale _ hh; unfold StepData.density; exact RG.Envelope.sum univ (fun i (x:Orbit J_ × Orbit H_)=>taggedKernel T R.beta i x.2.1 x.1.1) (fun i=>env_tagged R.beta i t (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_fst))
#check flex
#check swipeP
omit X p t
lemma listen {A:Type*} [MeasurableSpace A]{n:Side}(g:A→Orbit n)(h:Measurable g){V:A→Phys n}(x: Envelope V) {F: Oracle n}(p:BoundedT F) : Envelope (fun i=> F (g i) (V i)):=by
 -- infer finite
 let L:= Module.finBasis ℝ (Phys n); let Cx(i)(j):=L.coord i (V j); have hp(i) : Envelope (Cx i):= pole_w V (L.coord i) (L.coord i).continuous_of_finiteDimensional x
 let Q(i):= ∑ j,Cx j i • (F (g i) (L j)); have he: Envelope Q:= Env.total (g:=fun i x=> Cx i x • F (g x) (L i)) _ fun i=> Env.scale (hp i) (snap (p _) h)
 rw [show (fun i=>F (g i) (V i))=Q from ?_]; exact he
 funext i; unfold Q Cx; simp only [← map_smul,←_root_.map_sum]; exact congrArg _ (L.sum_repr (V i)).symm
variable {P G R F₁ F₂ q u}{F:Oracle (mid M B)}(b:BoundedT (n:=mid M B) F)
include X P b t p
lemma snob {W:Orbit (mid M B)× Orbit (mid C B)→ Phys (mid C B)}(s:Envelope W) : Envelope (fun z:Orbit J_× Orbit H_=> swipeP (j:=j) G R F₁ F₂ q u T F z.2 z.1 (W z)):=by
 refine listen Prod.fst measurable_fst (Env.scale (Envelope.const ((Fintype.card (Forest (ratio G)):ℝ)⁻¹)) (Env.total _ ?_)) b; intro i; exact flex P G R F₁ F₂ q u X T p t i _ s -- order
end YM.CF.Pyx
