import YM.CF.Sault.Gilt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sault
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Scree
variable {n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- general dΓ form
variable (b r:Bool)(V: UNI n)
local notation "S"=> sauce b r V
local notation "R"=> sings b V
abbrev hitL(A:Op n): Op n:= Thera.jazz r (sings b V A)
abbrev doveL (A:Op n):Op n:=if r then star (sings b V A) else sings b V A
lemma arm (F:Op n): S (faceD true false F)=faceD true false (hitL b r V F):=congrArg Subtype.val (Hest.sailR ..)
lemma lune (z:Op n) :Matrix.trace (doveL b r V z)=cSignX (b.xor r) z.trace:=by
 unfold doveL; cases r <;> simp only [singT]
 · simp [trace_twist,win_trace]
 simp only [ite_true,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose,trace_twist, win_trace]; cases b<;>simp [cSignX]
abbrev netL(f g:n→FC m)(P:Op n):=urn f g P
lemma handL (A:FC (LeanV n)): S (star A)=star (S A):=by rw [sauce,singT,win_s, map_star]; rfl
lemma arc(R':Op n): star (faceD true false (star R'))=urn (trailM false) (trailM true) R':=by
 unfold faceD twinD urn; rw [star_sum,sum_comm]; apply sum_congr rfl; intro i _; rw [star_sum]; apply sum_congr rfl; intro j _; rw [star_smul,star_mul]; change star (star (R' j i)) • (trailM false j *trailM true i) = _ -- check order
 rw [star_star]
lemma boon (A:Op n): S (urn (trailM false) (trailM true) A)=urn (trailM false) (trailM true) (hitL b r V A):=by
 rw [←arc, handL,arm,←arc]; congr 2; unfold hitL Thera.jazz; rw [singT,singT, win_s,map_star]; cases r <;>simp
abbrev grill(u:Bool)(A:Op n):Op n:=if u then A else -(cc (star A))
lemma gritz (A:Op n): grill false A= -Aᵀ:= by rw [grill,cc,star_star]; rfl
abbrev rockU (r u:Bool)(V:UNI n):= thread (if r then invFilm V else V) u
lemma brass(u:Bool)(i:n): twist (quantU (n:=LeanV n) (Scree.spice V r)) (wire u i)= crock (wire (u.xor r)) (rockU r (u.xor r) V).val i:=by
 cases r; · simp only [Bool.xor_false]; exact thread_in u V i
 rw [spirit,Bool.xor_true]; rfl
lemma brook(u:Bool)(i:n):twist (quantU (n:=LeanV n) (Scree.spice V r)) (trailM u i)=crock (trailM (u.xor r)) (cc (rockU r (u.xor r) V).val) i:=by
 rw [trailM, Fock.takeF, map_star,←show wire u i=put (n:=LeanV n) (u,i) from rfl, brass r V,crock,star_sum]; unfold crock; refine sum_congr rfl fun j _=>?_ ; rw [star_smul]; rfl
lemma rail (A: Op n)(u:Bool):twist (rockU r (u.xor r) V) (windX (b.xor r) (grill u A)) = grill (u.xor r) (hitL b r V A):=by
 have he(Z:Op n):windX (b.xor true) Z=cc (windX b Z):=by cases b; rfl; simp [windX]
 have hp(Z:Op n):windX b (cc Z)=cc (windX b Z):=by cases b<;>rfl
 have hx(Z:Op n):twist (invFilm V) Z=twist V Z:=by unfold invFilm; rw [Fock.twin,rankPhase]
 cases r
 · simp only [Bool.xor_false]; cases u
   · change twist (ccU V) (windX b (-cc (star A)))= -cc (star (twist V (windX b A)))
     rw [win_n,map_neg,hp,win_s,←cc_twist,map_star]
   rfl
 cases u
 · rw [he]; change twist (invFilm V) (cc (windX b (-cc (star A))))= -star (twist V (windX b A)); rw [hx,win_n,hp,win_s]; simp; rw [map_star]
 rw [he]; change twist (ccU (invFilm V)) (cc (windX b A))= -cc (star (-star (twist V (windX b A))))
 rw [←cc_twist,hx]; simp
abbrev crib(u:Bool)(A:Op n):= urn (wire u) (trailM u) (grill u A)
set_option maxHeartbeats 500000 in
lemma dew (A:Op n)(u:Bool): S (crib u A)=crib (u.xor r) (hitL b r V A):=by
 let v:=u.xor r; let K:=rockU r v V; let F:=grill u A; let L:=b.xor r; let Q (a:Bool)(Z:Op n):=urn (wire a) (trailM a) Z; let D:=twist (quantU (spice V r))
 have hv:windX L (crib u A)=Q u (windX L F):=by
    unfold crib urn; rw [win_sum]; apply sum_congr rfl; intro i _; rw [win_sum]; apply sum_congr rfl; intro j _; rw [win_c,win_m,wire,win_up,trailM,takeF,win_s,win_up]; exact congrArg (fun z:ℂ=> z • (wire u i * trailM u j)) (by change cSignX L (F i j)=(windX L F) i j; cases L <;>rfl)
 change D (windX L _) = urn (wire v) (trailM v) (grill v _); rw [←rail b r V A u]
 change D (windX L (crib u A))=urn (wire v) (trailM v) (twist K (windX L F))
 rw [hv,twist_formula K,←ccT, ←clove (m:=LeanV n)]
 unfold D Q urn; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_sum]; apply sum_congr rfl; intro j _; rw [twist_scalar,map_mul,brass,brook]
lemma urn_neg (f g:n→FC m)(P:Op n):urn f g (-P)= -urn f g P:=by simp only [urn, Matrix.neg_apply,neg_smul,sum_neg_distrib]
lemma forkL (P K T W Z:Op n):forge P K T W Z=faceD true false K+ crib true T+ (Matrix.trace P • 1+crib false W)+urn (trailM false) (trailM true) Z:=by unfold crib; rw [gritz, urn_neg,←sub_eq_add_neg]; rfl
lemma flare (F G:FC (LeanV n)):S (F+G)=S F+S G:=by simp only [sauce,singT,win_a,map_add]
lemma tiltH (H:Op n): S (Matrix.trace H • 1)=Matrix.trace (doveL b r V H) • 1:=by rw [lune,sauce,singT,win_c,win_i, twist_scalar,map_one]
lemma quest (F K T W Z: Op n): S (forge F K T W Z)=forge (doveL b r V F) (hitL b r V K) (hitL b r V (if r then W else T)) (hitL b r V (if r then T else W)) (hitL b r V Z):=by simp_rw [forkL]; rw [flare,flare,flare,flare, arm, dew, dew, boon, tiltH]; cases r; rfl; simp only [ite_true,Bool.xor_self,Bool.false_xor]; abel
end YM.CF.Sault
