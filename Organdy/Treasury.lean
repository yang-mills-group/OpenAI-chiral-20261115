import YM.SU5.FiniteGaugeData.Tower.Diagram
import Organdy.Spangles

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

/-- A local scalar projection read. -/
def Cello{K:Calibration} (S:Finset Cover)(f:Buffered.Family K):Prop:=
 ∃ g,Coeff true S g ∧ f=scalar K g ∧ ∀ x y z,g (x,y)=g (x,z)
def Treble{N:Side} (f:Mark N):Prop:=∀ x, ∃ c:ℂ,f x=c • (1:FC (Single N))
def Lily{N:Side} (f:Mark N):Prop:=∀ x y z,f (x,y)=f (x,z)

section
variable {N:Side}
abbrev gem(f:FC (Single N)) := f ∅ ∅
lemma gem_ct:Continuous (@gem N):=continuous_id.matrix_elem _ _
lemma gem_cut {f:Mark N}(u:Treble f)(x):gem (f x) • (1:FC (Single N))= f x:=by
 obtain ⟨t,hx⟩:=u x; simp [hx,gem]
end

section pure
variable {K:Calibration}{S:Finset Cover}{f:Buffered.Family K}(h:InTest K true S false f)
include h
lemma floret (n:Side)(t:Tivoli S (K.c n))(w:Lily (f n))(m:Side):Lily (f m):=by
 have hx:f=extendAtlas S K n t (f n):=box_ext K S h (dictionary S K n t _ (h.support _)) t.hosp (native S K n t _ (h.support n)).symm
 intro x y z; conv_lhs => rw [hx]
 conv_rhs => rw [hx]
 unfold extendAtlas; simp only [Finset.sum_apply,note_v,replant,piece,Prod.map,spool_sing]
 rw [w _ (graft S (K.c n) (onC (K.c m) y)) (graft S (K.c n) (onC (K.c m) z))]

lemma pearlescent (n:Side)(t:Tivoli S (K.c n))(w:Lily (f n))(u:Treble (f n)):
 Cello S f:=by
 let a:PairsC→ Fields (K.c n):= replant S _
 let x(v:PairsC):= gem (f n (a v))
 have hv:=h.support n
 have p:Coeff true S x:=
    ⟨fun _=>by contradiction,Girt.pole_w _ _ gem_ct (Env.along hv.env (replant_b S _)), fun i j b c=>congrArg gem (hv.dep _ _ (based S _ t _ _ b) (based S _ t _ _ c))⟩
 refine ⟨x,p,box_ext K S h (.seed p) t.hosp ?_,fun _ _ _=>congrArg gem (w _ _ _)⟩
 funext v
 let y:PairsC:= Prod.map (onC _) (onC _) v
 change f n v=gem (f n (a y)) • 1
 rw [hv.dep (a y) v (graft_native S _ t _) (graft_native S _ t _)]
 exact (gem_cut u v).symm
end pure

section
variable {K:Calibration}{I:Type*}{l:Filter I}[l.NeBot]{S:Finset Cover}{F:I→Buffered.Family K}{f:Buffered.Family K}
lemma Cello.treble (u:Cello S f)(n:Side):Treble (f n):= by obtain ⟨x,h,rfl,_⟩:=u; exact fun _=>⟨_,rfl⟩
lemma Q.lily (u:Q l S F f)(n:Side)(h:∀ i,Lily (F i n)):Lily (f n):=
 fun x y z=> tendsto_nhds_unique (u.atP n _) ((u.atP n (x,z)).congr fun i=> h i x z y)
lemma Q.treble(u:Q l S F f)(n:Side)(h:∀ i,Treble (F i n)):Treble (f n):=by
 intro x; refine ⟨gem (f n x),tendsto_nhds_unique (u.atP n x) ?_⟩
 have b:Continuous (fun v:FC (Single (K.c n))=> gem v • (1:FC (Single (K.c n)))):=gem_ct.smul continuous_const
 exact ((b.tendsto _).comp (u.atP n x)).congr fun i=>gem_cut (h i) x
end

/- Atlas paid as a `Q`, with charges and covariance across all sides.
 Actual N need only be equal to K.c (n i). -/
section skyline
variable {I:Type*}(l:Ultrafilter I) {K:Calibration}
 (S:Finset Cover){n:I→Side}
 (T:(i:I)→Tivoli S (K.c (n i)))
 (y:(i:I)→Mark (K.c (n i))) (a:∀i,AtSupport false (Satin.region S (K.c (n i))) (y i))
 (d:Menu (T:=fun i=>FC (Single (K.c (n i)))) (fun i x=> y i (replant S _ x)))
local notation "L"=> (↑l:Filter I)

include d
lemma peek (q:Evens S):
 Menu (fun i=>piece S K (n i) (T i) (y i) q : I→PairsC→ℂ):=by
 obtain ⟨C,h,x⟩:=d.budget
 refine ⟨d.deal.along (T:=fun i=> FC (Single (K.c (n i)))) (U:=fun _=>ℂ)
   (fun i v=>costume S K (n i) (T i) v q) ?_,
   C,h,fun _ _=> (biotech ..).trans (x ..)⟩
 refine fun ε g=> ⟨ε,g,fun i u v b=>?_⟩
 rw [dist_eq_norm] at *
 let X:= y i (replant S _ u)
 let Y:= y i (replant S _ v)
 have h':costume S K (n i) (T i) (X-Y) q= costume S K (n i) (T i) X q-costume S K (n i) (T i) Y q:=by

    rw [show X-Y=(-1:ℂ) • Y+X by rw [neg_one_smul,add_comm]; rfl,
        Tower.linearity]; ring
 change ‖costume S K (n i) (T i) X q-costume S K (n i) (T i) Y q‖ < ε; rw [←h']
 exact (biotech ..).trans_lt b

include a
theorem collector : ∃ f, Q L S (fun i=>extendAtlas S K (n i) (T i) (y i)) f:=by
 have c(i)(q):=painting S K (n i) (T i) (y i) (a i) q
 choose g p h v using fun q:Evens S=> marquis l (peek S T y d q) (fun i=> c i q)
 unfold extendAtlas
 exact ⟨_, Q.sum Finset.univ (fun q i=> note K (piece S K (n i) (T i) (y i) q) (tagWord S q.val)) (fun q=>note K (g q) (tagWord S q.val)) (fun q=> noteQ q (fun i=> c i q) (p q) (h q) (v q))⟩
end skyline

section
variable {I:Type*} {K:Calibration} {N:I→Side}
structure Bolt (l:Filter I) (S:Finset Cover) (n:I→Side)(e:∀ i,K.c (n i)=N i)
 (y:(i:I)→Mark (N i))(F:I→Buffered.Family K)(f:Buffered.Family K):Prop where
 queue: Q l S F f
 sees(i:I): ship (e i) (F i (n i))=y i

def Plumage (F:Buffered.Family K):Prop:=∀ m,Lily (F m) ∧ covariant (F m)

variable {l:Filter I}{S:Finset Cover}{n:I→Side}{e:∀i,K.c (n i)=N i}
 {Y W:(i:I)→Mark (N i)}{F G:I→Buffered.Family K}{x z:Buffered.Family K}
namespace Bolt
lemma quality [l.NeBot](a:Bolt l S n e Y F x)
 (t:∀i,Tivoli S (N i)) (h:∀ i,Lily (Y i)∧covariant (Y i)):
 (∀ i,Plumage (F i)) ∧ Plumage x:=by
 have ee:(K.c ∘n)=N:=funext e; subst N
 have k(i):=a.sees i
 have u(i):F i (n i)=Y i:=k i
 have p(i): Plumage (F i):=
   fun m=> ⟨floret (a.queue.goes i) (n i) (t i) ((u i).symm ▸ (h i).1) m,
     complete_cov K (a.queue.goes i) (n i) (t i).hosp ((u i).symm ▸ (h i).2) m⟩

 exact ⟨p,fun m=>⟨a.queue.lily _ (fun i=> (p i m).1),a.queue.color _ (Eventually.of_forall fun i=> (p i m).2)⟩⟩
lemma cello [l.NeBot] (a:Bolt l S n e Y F x) (t:∀i,Tivoli S (N i)) (h:∀ i,Lily (Y i)∧covariant (Y i))(H:∀ i,Treble (Y i)):
 (∀ i,Cello S (F i))∧Cello S x:=by
 have u:=a.quality t h
 have ee:(K.c ∘n)=N:=funext e; subst N
 have k(i):F i (n i)=Y i:= a.sees i
 have p(i): Cello S (F i):=pearlescent (a.queue.goes i) (n i) (t i) ((u.1 i _).1) ((k i).symm ▸ H i)
 obtain ⟨j,_⟩:=(Eventually.of_forall (f:=l) (fun i=>True.intro)).exists
 exact ⟨p,pearlescent a.queue.toBe (n j) (t j) ((u.2 _).1) (a.queue.treble _ (fun i=> (p i).treble _))⟩

lemma add (a:Bolt l S n e Y F x) (b:Bolt l S n e W G z):
 Bolt l S n e (Y+W) (F+G) (x+z):=by
 have p:=a.sees; have q:=b.sees
 have ee:(K.c ∘n)=N:=funext e; subst N
 exact ⟨a.queue.plus b.queue,fun i=> congrArg₂ (·+·) (p i) (q i)⟩

lemma scale(a:Bolt l S n e Y F x)(c:ℂ):Bolt l S n e (c • Y) (c • F) (c • x):=by
 have p:=a.sees
 have ee:(K.c ∘n)=N:=funext e; subst N
 exact ⟨a.queue.scale c,fun i=>congrArg (c • ·) (p i)⟩
lemma sub (a:Bolt l S n e Y F x) (b:Bolt l S n e W G z):
 Bolt l S n e (Y-W) (F-G) (x-z):=by
 rw [sub_eq_add_neg,sub_eq_add_neg,sub_eq_add_neg]; simpa only [neg_one_smul] using a.add (b.scale (-1))

lemma identity : Bolt l S n e (1:∀ i,Mark (N i)) 1 1:=by
 have ee:(K.c ∘n)=N:=funext e; subst N; exact ⟨Q.identity,fun _=>rfl⟩

lemma sum{J:Type*}(r:Finset J)(y:J→∀ i,Mark (N i))(f:J→I→Buffered.Family K)(g:J→Buffered.Family K)
 (h:∀ j,Bolt l S n e (y j) (f j) (g j)):
 Bolt l S n e (fun i=>∑ j∈r,y j i) (fun i=>∑ j∈r,f j i) (∑ j∈r,g j):=by
 have u (j)(i):=(h j).sees i
 have ee:(K.c ∘n)=N:=funext e; subst N
 refine ⟨Q.sum _ _ _ fun j=>(h j).queue,fun i=>?_⟩

 change (∑ j∈r,f j i) _=_; rw [Finset.sum_apply]
 exact Finset.sum_congr rfl fun j _=>u j i
end Bolt

theorem rollcall (l:Ultrafilter I)(n:I→Side)(e:∀i,K.c (n i)=N i)
 (t:∀i,Tivoli S (N i))
 (a:∀i,AtSupport false (Satin.region S (N i)) (Y i))
 (d:Menu (T:=fun i=>FC (Single (N i))) (fun i x=> Y i (replant S _ x))):
 ∃ F x, Bolt (l:Filter I) S n e Y F x:=by
 have ee:(K.c ∘ n)=N:=funext e; subst N
 obtain ⟨x,z⟩:=collector l S (K:=K) (n:=n) t Y a d
 refine ⟨_,_,z,fun i=>?_⟩
 exact Tower.native S K _ _ _ (a i)
end
