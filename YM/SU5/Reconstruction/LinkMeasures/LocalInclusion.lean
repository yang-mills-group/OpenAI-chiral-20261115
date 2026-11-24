import YM.SU5.Reconstruction.LinkMeasures.LiteralAlgebra
import YM.SU5.Reconstruction.LinkMeasures.MorningRoom
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Set
variable (S T:Finset Cover)(h:S⊆T)(K:Calibration)
local notation "W" => Swatch S
local notation "X" => ScoreBook S
noncomputable def enlarge (x:LocalEdges S) : LocalEdges T := ⟨x.val, (localEdges T _).2 (show _∧_ from ⟨h ((localEdges S x.val).1 x.property).1,h ((localEdges S x.val).1 x.property).2⟩)⟩
noncomputable def oneGlow (f:Aerial T) : Aerial S:=f ∘ enlarge S T h
noncomputable def consider: ScoreBook T→ ScoreBook S:=Prod.map (oneGlow S T h) (oneGlow S T h)
lemma consider_seek(m:Side)(x:Fields (K.c m)): consider S T h (seek T K m x)=seek S K m x:=rfl
lemma consider_c: Continuous (consider S T h):=by have g:Continuous (oneGlow S T h):=continuous_pi fun i=> continuous_apply _; exact g.prodMap g
noncomputable def derives (f:Manifest S): Manifest T:= f.comp ⟨consider S T h,consider_c S T h⟩
lemma roomEnough (f:Manifest S)(p:f∈ sealA S): derives S T h f∈ sealA T :=by
 change f∈ StarAlgebra.adjoin ℂ _ at p; induction p using StarAlgebra.adjoin_induction with
 | mem x v=> obtain ⟨⟨e,b,i,j⟩,rfl⟩:=v; change derives S T h (elem S e b i j)∈ _; rw [show derives S T h (elem S e b i j)= elem T (enlarge S T h e) b i j from by cases b <;> rfl]; exact genre T _ b i j
 | add x y p q ih it=> exact (sealA T).add_mem ih it
 | mul x y p q ih it=> exact (sealA T).mul_mem ih it
 | star x p ih=> exact star_mem ih
 | algebraMap r=> exact (sealA T).algebraMap_mem r

lemma pointUp (x y)(a:badge K S x=badge K T y)(m:Side)(u: Hosp T (K.c m))(t:ScoreBook T):
   pointOp T K m y t=∑ i:Evens S, (accession S (x i)).val (consider S T h t) • spool (K.c m) (tagWord S i.val):=by
 let v:=prepare T K m t; have he:seek S K m v=consider S T h t:=by rw [←consider_seek S T h, show seek T K m v=t from seek_prepare T K m u t];
 unfold pointOp; rw [←appearRender, ←(show render S K x=render T K y from congrArg Subtype.val a), appearRender,seek_op S K m,he]
include h
lemma largerProgram (x:W)(p:x∈literal S)(y:Swatch T)(a:badge K S x=badge K T y): y∈ literal T:=by
 obtain ⟨m,t⟩:= (Buffered.separates K T).exists; let u:Hosp T (K.c m):=⟨t⟩; let M:=K.c m; choose g v t' using lecturer S x p
 refine literal_from T y fun j=>?_ ; let P(i:Evens S):= eye T K m u j (spool M (tagWord S i.val))
 refine ⟨∑ i:Evens S,P i • derives S T h (g i),(glancing T).sum_mem (fun i _=> (glancing T).smul_mem _ (roomEnough S T h (g i) (v i))),fun z=>?_⟩; rw [←head_price T K m u,pointUp S T h K x y a m u,map_sum]; simp_rw [t', map_smul,ContinuousMap.sum_apply,ContinuousMap.smul_apply]; exact Finset.sum_congr rfl fun i _=> mul_comm (g i (consider S T h z)) (P i)
lemma broadcast_growth: Polished S K ≤ Polished T K:=by
 intro x p; obtain ⟨a,p₀,rfl⟩:= (pol_here ..).1 p; obtain ⟨g,u⟩:= accolade K T _ (tallerBay K S true h (locatesBadge ..)); exact ⟨g,largerProgram S T h K a p₀ g u.symm,u⟩
lemma isotone: labOfGauge S K ≤ labOfGauge T K:=by unfold labOfGauge; exact inf_le_inf (broadcast_growth S T h K) le_rfl
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.isotone
