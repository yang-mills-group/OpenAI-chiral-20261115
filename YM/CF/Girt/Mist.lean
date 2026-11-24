import YM.CF.Girt.Light
import YM.CF.Cour.Hue
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
open Nacre
lemma moveT (s: Signed): Continuous (Yg (n:=n) (incX s)):= by rw [show Yg (n:=n) (incX s)= Lattice.pull s 0 from funext fun i=>Nacre.Ywin s i]; exact Wilson.continuous_pull .. -- tune
lemma pigmentC (U:Pride n): Continuous (pigment U):=by
 unfold pigment lexn; refine Continuous.smul (f:=fun _=> ((Fintype.card Signed:ℝ)⁻¹)) continuous_const ?_; refine continuous_finsetSum _ fun i _=> (pays i).continuous.comp ((show Continuous (zinger U) from ?_).comp (moveT i))
 unfold zinger; refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> continuous_finsetSum _ fun k _=> (Continuous.smul ((show Continuous fun V:Config SU.group (More n)=> inner ℝ (silt (node i) j V) (silt (node i) k V) from (Cour.siltC ..).inner (Cour.siltC ..))) (continuous_const (y:=U i j k)))
lemma den_ct(X:Aim n): Continuous X.den:=by
 have hp(k:ℕ)(L:Font.Toy k n):Continuous (colorX L):=by
    refine Continuous.smul (f:=fun _=> ((Fintype.card Signed:ℝ)⁻¹)) continuous_const ?_
    refine continuous_finsetSum _ fun i _=> (Nacre.ZoneH _).continuous.comp ((show Continuous (Nacre.cavil L) from ?_).comp (moveT i⁻¹))
    unfold Nacre.cavil; refine continuous_matrix (fun i j=>?_) -- tune
    change Continuous (fun V=> (∑ x:Font.Trip k n,Nacre.mold L i.1 j.1 x V) i.2 j.2)
    refine (continuous_finsetSum _ (f:=fun x V=>Nacre.mold L i.1 j.1 x V) (fun x _=>?_)).matrix_elem _ _
    apply Continuous.mul
    · exact continuous_matrix fun t u=> (L _ _ _).cont.comp (continuous_pi fun w=>Cour.siltC _ _) -- tune
    exact matter_cont.comp (travel_cont ..)
 exact (hp _ X.x).add (hp _ X.y)
open Pastry
lemma dgCT (I:Type*)[Fintype I][LinearOrder I]:Continuous (dg (n:=I)):=continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> (continuous_id.matrix_elem i j).smul continuous_const
lemma house_k (A:Pearl P')(S:Stamped j L ho Y)(p:0<e)(h:1 ≤ j)(W:Cascade.Interest (mid C B))(t:P'.roundZ ≤ (mid C B).val): Continuous (fun i:CapX C B e=>relV P' W i.val):=by
 let L:=P'.broadness _ t W.M; let X:= Single (mid C B); have ht:Continuous (fun i:CapX C B e=> changeM P' i.val W.M):=by
    obtain ⟨_,_,_,_,T⟩:= cycle A S p h 0 1 le_rfl; obtain ⟨F,U,H,V,v⟩:= T C t W.M
    let Y:=chant C B j W.M (P'.cost C W.M); have he:Continuous (fun i:CapX C B e=>Y i.val):= continuousOn_iff_continuous_restrict.mp (freezing P'.topB P'.baseY.1 (P'.couture t W.M) L.continuousOn)
    let K:=candle C B (P'.cost C W.M); have hp:Continuous (fun i:CapX C B e=> K i.val):=by rw [funext v]; exact continuous_finsetSum _ fun i _=>(H i).cont
    exact (Complex.continuous_exp.comp hp.neg).smul he
 let f(i:CapX C B e):= spar j W.M i.val; have hf:Continuous f:=continuousOn_iff_continuous_restrict.mp L.continuousOn; have he:Continuous (fun i:CapX C B e=> capT (f i) (W.P.den i.val)):= (((continuous_const.sub hf).mul ((den_ct W.P).comp continuous_subtype_val)).mul hf)
 letI : NormedAlgebra ℚ (FC X):=NormedAlgebra.restrictScalars ℚ ℂ _
 exact (acts_cont.comp (NormedSpace.exp_continuous.comp ((dgCT _).comp he))).clm_apply ht
lemma tan_k (I:Type*)[Fintype I][LinearOrder I]:Continuous (uncurry (tank (I:=I))):=by
 have hv (S:List (LeanV I)):Continuous (fun x:Op I=> (S.map (drawT x)).prod):=by
    induction S with
    | nil=> exact continuous_const
    | cons a S ih=>
       refine Continuous.mul ?_ ih; unfold drawT; split; · exact continuous_finsetSum _ fun i _=> ((continuous_const.sub continuous_id).matrix_elem _ _).smul continuous_const
       exact continuous_finsetSum _ fun i _=> ((show Continuous (cc (n:=I)) from by unfold cc; fun_prop).matrix_elem _ _).smul continuous_const
 refine continuous_finsetSum _ fun i _=> (((continuous_subtype_val.comp (continuous_snd (X:=Op I))).matrix_elem _ _).smul ((hv _).comp continuous_fst))
end YM.CF.Girt
