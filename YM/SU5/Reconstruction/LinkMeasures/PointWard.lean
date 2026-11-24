import YM.SU5.Reconstruction.LinkMeasures.SealGauge
import YM.SU5.Reconstruction.LinkMeasures.CountsUp
import YM.SU5.Reconstruction.Based.Residual
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
open PaymentCamera Tower Tower.PhaseChoice CF.Pannier.Chancel
variable (S:Finset Cover)
-- Access through any roomy host circle, and thus on link materials
variable (K:Calibration)(m:Side)(p:Hosp S (K.c m)) (Λ:Preparation)(l:ℕ)
local notation "n" => K.c m
local notation "W" => Swatch S
local notation "X" => ScoreBook S
local notation "M" => Manifest S
noncomputable def seek (v:Fields (K.c m)): ScoreBook S:= here S (Prod.map (onC n) (onC n) v)
noncomputable def prepare (x:ScoreBook S): Fields (K.c m):= replant S n (decode S x)
noncomputable def pointOp (f:Swatch S)(x: ScoreBook S) : FC (Single (K.c m)):= appear S K m f (prepare S K m x)
lemma seek_c : Continuous (seek S K m):=(here_c S).comp ((on_cont n).prodMap (on_cont n))
include p
lemma seek_prepare(x:X): seek S K m (prepare S K m x)=x:=by
 have he(v:LinksC): limitOne S (onC n (graft S n v))=limitOne S v:= (limits S _ _).2 (fun i h _=> Satin.tail S n p v i h)
 exact (show seek S K m (prepare S K m x)=here S (decode S x) from Prod.ext (he _) (he _)).trans (here_decode ..)
-- independent of p when paying from any host as whole flavor expression
omit p in
lemma lyric_entry (f:Pigment S)(x:PairsC): daub S f x=(accession S f).val (here S x):= by
 have h:= lyric S (accession S f); rw [known] at h; exact congrFun h x
omit p in
lemma seek_op (f:W)(v:Fields (K.c m)): appear S K m f v=∑ i:Evens S,(accession S (f i)).val (seek S K m v) • spool n (tagWord S i.val):=by rw [appearSpool]; simp_rw [lyric_entry S]; rfl
lemma paid_as (f:W)(x:X): pointOp S K m f x=∑ i:Evens S,(accession S (f i)).val x • spool n (tagWord S i.val):= by rw [pointOp,seek_op,seek_prepare S K m p]
lemma confirmation(f:W)(v:Fields (K.c m)): pointOp S K m f (seek S K m v)=appear S K m f v:=by rw [paid_as S K m p,seek_op]
lemma head_price (f:W)(x:X)(i:Evens S): eye S K m p i (pointOp S K m f x)=(accession S (f i)).val x:= eye_readCover ..
lemma head_le (f:W)(x:X)(i:Evens S): ‖(accession S (f i)).val x‖≤ ‖pointOp S K m f x‖:=by rw [←head_price S K m p]; exact eye_bounded ..
variable (g:Zodiac (K.c m))
local notation "Rr" => rotAct S (g∘wrap (More n))
local notation "U★" => star (atelier g)
lemma orbit_charge (f:W)(x:X): pointOp S K m (orbitC S K m f g) x=twist (star (quantU (tradew n g))) (pointOp S K m f (Rr x)):=by
 let v:= prepare S K m x
 have he: Rr x= seek S K m (simultaneous g v):=by
    calc
     _ = Rr (seek S K m v):= congrArg Rr (seek_prepare S K m p x).symm
     _ = _:= by change Rr (here S (onC n v.1,onC n v.2))= here S (onC n (Lattice.gauge g v.1),onC n (Lattice.gauge g v.2)); rw [rot_price, Rooted.wrappedGauge, Rooted.wrappedGauge]
 rw [he,confirmation S K m p,pointOp,orbitC_apply]; rfl
lemma single_entry (f:W)(x:X)(j:Evens S):
    let Q(i:Evens S):= eye S K m p j (twist (star (quantU (tradew n g))) (spool n (tagWord S i.val)))
    (accession S ((orbitC S K m f g) j)).val x = ∑ i:Evens S, Q i * (accession S (f i)).val (Rr x) :=by
 intro Q; rw [←head_price S K m p, orbit_charge S K m p,paid_as S K m p, map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=> (by rw [twist_scalar,map_smul,smul_eq_mul,mul_comm]) -- Q defeq
lemma budget_rotate(f:W)(x:X)(j:Evens S): ‖(accession S ((orbitC S K m f g) j)).val x‖ ≤ ∑ i:Evens S,‖(accession S (f i)).val (Rr x)‖:=by
 refine (head_le S K m p _ _ _).trans ?_; rw [orbit_charge S K m p,twist_norm,paid_as S K m p]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_); rw [norm_smul]; apply mul_le_of_le_one_right (norm_nonneg _); rw [←spool_sing K m _ (prepare S K m x)]; exact chorus_size ..
lemma gauge_fixed (f:W)(h:Tapestry.Neutral K (Tapestry.render S K f)): orbitC S K m f g=f:=by
 apply appear_inj S K m p; rw [orbitC_apply]; funext x; apply (twist (quantU (tradew n g))).injective; exact (trueBack (Tapestry.appear S K m f) g x).symm.trans (h m g x)

end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.gauge_fixed
#print axioms YM.CF.Buffered.Afterglow.Satori.budget_rotate
