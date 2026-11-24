import YM.CF.Girt.Pit
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
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
open Oriented Presented RG Next.SectorChange Next.Fluctuations.Sector SectorNext.Remainder.Affine CF.Appel Pressure.Stores AnalyticBridge.Annulus1AD
variable {m c f:Side} {S:StepData c f}(T':Tube G₀ S)(x β :ℝ) (V:Config G₀ c)(F:Forest S.ratio)(A:Stores S)(i:S.Choices)(B:Allocation G₀ S x W)(U:Config G₀ f→E)
def lightD(U:Config G₀ f→ E)(X:Config G₀ f):= Real.exp (β * Oriented.wholeGap T' x X V) • U X
lemma shadeW (K:Teller G₀)(l:K.Funds S T')(p:RG.Envelope U): RG.Envelope (lightD T' x β V U):=by
 have hx:RG.Envelope (fun X: Config G₀ f=> Oriented.wholeGap T' x X V):= env_mean (F:=(fun s a=> Next.Fluctuations.Sector.crownGap T' x (Lattice.pull s 0 a) (Lattice.pull s 0 V))) (fun s=>env_gap l _ (pulling_meas s measurable_id) measurable_const)
 exact Env.scale (((Envelope.const _).mul hx).exp) p
lemma matW (l:S.patch.Branches S.kernel G₀) (w:F.Slice G₀):
 B.portion A F V (through S F β V (fun _ a=> U (F.drape a))) i w=(prefactor S G₀ β) • attending B A F V i (leaseP T' A V i β x (lightD T' x β V U)) w :=by
 let W':=F.drape w
 have hu:=enters_eq l A β x i V W' (T:=T') -- tune
 unfold Oriented.leaves at hu
 have he: taggedKernel S β i W' V=(prefactor S G₀ β)*S.likelihood W' i*(Real.exp (-β *Rows.fee T' x V i A W')*Real.exp (β * Oriented.wholeGap T' x W' V)):=by
    nth_rw 1 [show taggedKernel S β i W' V= enters T' β x i V W'*Real.exp (β * wholeGap T' x W' V) from ?_]
    rw [Rows.fee,mul_add,Real.exp_add, hu]; ring
    unfold enters; rw [mul_assoc,← Real.exp_add]; simp
 unfold Allocation.portion through attending leaseP lightD; rw [he]; simp_rw [smul_smul]; congr 1; unfold W'; ring
variable (q':Chi)(J:ChartRatio G₀)(d s:ℝ)(l:ℕ)(h:0<W)(ht:0<fiery G₀ x S.patch.L)
variable {z N':ℝ}
variable (W) in
def glowV (Y: LinkArray G₀ (Frozen A x F))(Z:LogArray G₀ (Active A x F)):=
 let a:=putU β T' F A V i x l q' d Y Z; let X:=fieldU β T' F A V i x l q' d Y Z
 capsule x A F q' d J univ a*receipts q' A x W univ univ univ X V i*Real.exp (Real.log |(credW T' A F i q' d x Y l V).det| + embH T' A F V i q' β d x Y l Z (fun _=>globe S) + duty T' A F V i q' β d x Y l Z + phere T' A F V i q' d x Y l Z+ β * wholeGap T' x X V)
-- exact authentic weight on every fiber. supplies ALL proofs.
variable {w':ℝ} {l':ℕ}
lemma pom (hβ:0<β)(t:MossX l' l x A F T' V i z d N' q')(v:A.flags=flags (temp x) V)(H:Teller G₀)(w:H.Funds S T')(k:LocalRatio J)(g:4*d<J.radius)(hg:0<d)(hs:wireP G₀ (coupling β) d (z*N') z ≤ s)(hy:0<s)(p:Standing (F:=F) (A:=A) (q'.profiles G₀ S x W h ht) J d i V)(L: RG.Envelope U): let B:=q'.profiles G₀ S x W h ht
 let f:= glowV T' x β V F A i q' J d l (W:=W)
 let g(Y Z):=f Y Z • U (fieldU β T' F A V i x l q' d Y Z)
 let I:= piHaar G₀ (Frozen A x F)
 let ℳ:=tableG G₀ (Active A x F) s
 (∀ Y,Integrable (g Y) ℳ)∧ Integrable (uncurry g) (I.prod ℳ) ∧ (∫ a, B.portion A F V (through S F β V (fun _ a=> U (F.drape a))) i a ∂F.order G₀)= (prefactor S G₀ β*(spare J β*point G₀ s)^Fintype.card (Active A x F)) • (∫ Y, (∫ Z,g Y Z ∂ℳ) ∂I):=by
 intro B f B' I Q; let W':= leaseP T' A V i β x (lightD T' x β V U)
 have ht':RG.Envelope W':=lease_env T' A V i β x (shadeW T' x β V U H w L) H w -- tune
 obtain ⟨hc,he,hℓ⟩:= ret (q:=q') β W' ht' t B p k g hg hβ hs hy
 have hx: reelX β B q' J x d T' A F V i l W'=B':=by
    funext Y Z; unfold W'; obtain ⟨a,b,ha,hb⟩:=w.feeds; rw [← w.high] at ha; rw [seriesG T' A F V i q' β d x Y l Z hβ t J ha]; unfold B'; unfold f glowV lightD; rw [smul_smul]; congr 1; rw [mul_assoc (capsule ..),show B.bill _ _ _ _*S.likelihood _ _=_ from see q' _ _ _ _ h ht v]; dsimp only; simp_rw [Real.exp_add]; ring -- tune hs
 rw [hx] at hc he hℓ
 refine ⟨hc,he,?_⟩; simp_rw [matW T' x β V F A i B U (funds_branch w),integral_smul]; rw [hℓ,smul_smul]
end fig
end YM.CF.Girt
