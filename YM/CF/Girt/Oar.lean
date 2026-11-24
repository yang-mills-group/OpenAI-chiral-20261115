import YM.CF.Girt.Zero
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
variable {f n :Side}{CΛ δ v a P h d μ ε w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
lemma sweep(R:GramM (mid C B))(Z:Ward R)(p:R.J.P.toll a v h w)(T:Scree.Loom (mid C B))(b:ℕ)(hp:Roof _ d e b T)(x:Orbit (mid C B))(g:Seat (mid C B)→E)(A:Pearl P')(u:Stamped j L ho Y)(t:P'.roundZ ≤ (mid C B).val)(r:1≤j): denZ R P' T (gird g x)= effectK (tradew _ g).val (denZ R P' T x):=by
 let V:=tradew _ g; let z:=gird g x; let W:=P'.broadness _ t R.J.M
 have he:T (gird g x)=Lattice.gauge g (T x):=hp.rev _ _ _
 obtain ⟨_,_,_,hl⟩:=Z.area
 have hk: R.betaL T (gird g x)=R.betaL T x:=by
    change R.v-↑(R.path.inChannels R.funds R.p R.beta (gauge g x.1))-pigment _ (T (gird g x))=_; rw [he,pinG, thumb R hl]; rfl
 let B:= spar j R.J.M (T x)
 let S:= spar j R.J.M (T z); have hb:IsStarProjection B:=W.projection _ (hp.paid _); have hs:IsStarProjection S:= W.projection _ (hp.paid _); have hv:sings false V B=swapX false S:=by change twist V _=spar j R.J.M (T (gird g x)); rw [he]; exact (W.covary _ g (hp.paid _)).symm
 have hr: relV P' R.J (T z)=effectK V.val (relV P' R.J (T x)):=by change nest P' R.J.P _ (T (gird g x))=_; rw [he]; exact (salt_g A u t r _ _ p _ (hp.paid _)).symm
 unfold denZ; rw [effectK,map_smul,hk]; apply congrArg _ (show acts (tank S _) (relV P' R.J (T z))= acts (quantU V).val (acts (tank B _) (relV P' R.J (T x))) from ?_); rw [hr, show R.board (gird g x)=_ from march R Z _ _, tank_eq S _ hs,tank_eq B _ hb,← appleT hb hs false false V hv]; exact (Fock.swivel (quantU V) _ _).symm
end YM.CF.Girt
