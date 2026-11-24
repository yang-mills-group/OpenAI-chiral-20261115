import Merino.Garter.Twirl
import Merino.Hem.Scar
import YM.Push.LOCAL_SPLITTING.Orientation
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}


structure StepIn(n:Side) where
 face : Signed
 there : Site n
abbrev Duo(n:Side):=StepIn n × StepIn n

namespace StepIn
abbrev apply1 (p:StepIn n) := affine p.face p.there
instance : Mul (StepIn n) where
 mul a b := ⟨a.face*b.face, a.apply1 b.there⟩

instance : One (StepIn n) where one:=⟨1,0⟩
@[simp] lemma mul_face(p q:StepIn n): (p*q).face=p.face*q.face:=rfl
@[simp] lemma mul_there(p q:StepIn n): (p*q).there=p.apply1 q.there:=rfl
@[simp] lemma apply_comp(p q:StepIn n)(x:Site n): (p*q).apply1 x=p.apply1 (q.apply1 x):=by
 simp [apply1,affine,Signed.act_mul,add_assoc]
lemma assoc(p q r:StepIn n):p*q*r=p*(q*r) := by
 rw [show p*q*r = ⟨(p*q).face*r.face,(p*q).apply1 r.there⟩ from rfl,
     mul_face,apply_comp,mul_assoc]; rfl

abbrev rotate (a:StepIn n)(g:Duo n):Duo n:=(a*g.1,a*g.2)
lemma mul_rotate (a b:StepIn n)(g:Duo n): (a*b).rotate g=a.rotate (b.rotate g) := by
 simp [rotate,assoc]


variable (p:StepIn n)
abbrev siteB : Equiv.Perm (Site n):= Push.Local.turnSites p.face p.there
@[simp] lemma apply_sep (x y) :
 separation (p.apply1 x) (p.apply1 y)= separation x y:=Push.Local.turn_sep .. 
@[simp] lemma apply_zero:p.apply1 0=p.there:=by simp [apply1,affine]
abbrev baseball (d:ℕ)(x:Site n) := halo d ({x}:Support n)
lemma apply_ball(d)(x): baseball d (p.apply1 x)=(baseball d x).image p.siteB:=by
 rw [baseball,baseball,←Push.Local.halo_map p.siteB p.apply_sep]
 rw [Finset.image_singleton]; rfl

abbrev cabin (V:Config G n): Config G n:=pull p.face p.there V
lemma agrees {x d}{U V:Config G n} (h:Agrees (baseball d (p.apply1 x)) U V):
   Agrees (baseball d x) (p.cabin U) (p.cabin V) := by
 rw [apply_ball] at h; exact Push.Local.agrees_pull _ _ h
lemma cabin_mul (g:StepIn n)(U:Config G n):
  (p*g).cabin U = g.cabin (p.cabin U) := (pull_pull ..).symm


abbrev steer (V:Dir G n):Dir G n:= bank p.face p.there V
abbrev sent := Face.send p.face p.there 
abbrev cost(i:Face (Per n)):= orient p.face i.2
lemma steer_mul (g:StepIn n)(X:Dir G n):
  (p*g).steer X=g.steer (p.steer X) := (bank_bank ..).symm
lemma swirl (i:Face (Per n))(X:Dir G n):
 faceCurl i (p.steer X)=p.cost i • faceCurl (p.sent i) X:=twirl ..
lemma posted (i:Face (Per n))(V:Config G n):
 G.chord (faceValue (p.cabin V) i)=G.chord (faceValue V (p.sent i)):=
  Face.send_price _ _ _ _ _ G.chord_inv (fun _ _ => G.chord_conj ..)

lemma sent_unique (a:Signed)(i:Face (Per n)) :
  Injective (fun x=> (StepIn.mk a x).sent i):=by
 intro u v h; have e:=congrArg Prod.fst h
 simpa [sent,Face.send,Face.lower,atFace,affine] using e

lemma toll (i:Face (Per n)) :
  separation p.there (p.sent i).1 ≤ separation 0 i.1+2 := by
 refine (separation_triangle _ (p.apply1 i.1) _).trans ?_
 conv => lhs; arg 1; rw [← p.apply_zero,apply_sep]
 apply Nat.add_le_add_left
 let t (d:Lattice.Step):Site n:= if d.neg then d.vec else 0
 have ht(d:Lattice.Step):pdist (t d) ≤ 1:= by
   unfold t Step.vec; split <;> first | simp [*,pdist_step] | simp [pdist,lift]


 let a := (posDir i.2.val.1).rotate p.face
 let b := (posDir i.2.val.2).rotate p.face
 rw [separation_comm,separation]
 rw [show (p.sent i).1-p.apply1 i.1=t a+t b from by
       change p.apply1 i.1+t a + t b-_=_
       abel]
 exact (pdist_triangle ..).trans (Nat.add_le_add (ht a) (ht b))
end StepIn


open StepIn
abbrev Packs (d:ℕ)(j:I→StepIn n):Prop :=
 Pairwise fun i k => Disjoint (baseball d (j i).there) (baseball d (j k).there)
lemma Packs.unique {d}{j:I→StepIn n}(h:Packs d j):Injective (fun i=>(j i).there):=by
 intro i k e
 by_contra h'
 have r:=h h'; dsimp only at e r; rw [e] at r
 have l: (j k).there ∈ baseball d (j k).there := halo_subset d _ (mem_singleton_self _)
 exact Finset.disjoint_left.mp r l l
lemma Packs.turn {d}{j:I→StepIn n}(h:Packs d j)(p:StepIn n) :
  Packs d (fun i=>p*j i):=by
 intro i k hik; dsimp only [StepIn.mul_there]; rw [apply_ball,apply_ball];
 exact (Finset.disjoint_image p.siteB.injective).mpr (h hik)

/-- j gives sample layouts on the basic pair. -/
def Pavilion(d:ℕ)(g:Duo n)(j:I→StepIn n) :=
 Packs d (fun i=> j i * g.1) ∧ Packs d (fun i=>j i * g.2)
lemma Pavilion.turn {d}{j:I→StepIn n}{g}(h:Pavilion d g j)(p:StepIn n):Pavilion d g (fun i=>p*j i):=by
 unfold Pavilion; beta_reduce; simp_rw [StepIn.assoc]; exact ⟨h.1.turn p,h.2.turn p⟩

end YM.CF.Merino.Garter
