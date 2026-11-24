import Organdy.Cygnet
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

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell


open Salt Roots
structure Blush (n:Side) where
 r:Site n
 A:Hookah n

abbrev Blush.spin{n:Side}(b:Blush n)(i:Axis)(z:ℤ):Blush n:=
 ⟨(plane i z).mills n b.r,b.A.twistL i z⟩

variable {P:Spine}{s q k:ℕ}{c:Cuts}{d:Stores}
local notation "N'" =>kitGap P s q
local notation "Y'" => guineas P s
local notation "ι'" => (hueW P.par.R.L Y' * yInvoice c.b)
local notation "W✽" => prismPan P.par.R d.v Y'
local notation "R✽" => shaft P s

structure Rouge (P:Spine)(c:Cuts)(s q k:ℕ)(b:Blush (kitGap P s q)):Prop where
 wears: node b.r∈ b.A.S
 fare:∃ U V,Boarding P q k s c.m c.a c.b c.f c.g b.r b.A.S b.A.x U V


open Hive BProof.Bide
variable {a:Blush (kitGap P s q)}
variable (t:Seating P c d s q k) (i:Axis)(z:ℤ)
include t
-- avoid motives in dependent induction by abstracting
lemma flurry {r S X U V}
 (h:Boarding P q k s c.m c.a c.b c.f c.g r S X U V):
 ∃ U' V',Boarding P q k s c.m c.a c.b c.f c.g ((plane i z).mills _ r)
      (hyphen i z S) (reflMark i z X) U' V':=by
 cases h
 case home u=>
   have b:=(posed0 P q k s t.reef.clearing u t.reef.toll.le).glow
   rw [←rippleY,←rippleM i z _ (fun x=>Chord.keys_of_chord (Chord.full (b.realc.allV x).sector))]
   exact ⟨_,_, Boarding.moved u _ (by unfold QuadClock.Earlier;rw [rpt,Shape.nodex,fling_there])⟩
 case moved u a g=>
   have b:=(posed0 P q k s t.reef.clearing u t.reef.toll.le).glow
   let h (x):=Chord.keys_of_chord (Chord.full (b.realc.allV x).sector)
   rw [rippleYY,← rippleM i z _ (fun x=>Keys.tour_b _ _ _ _ (h _)),chain _ _ _ h]
   exact ⟨_,_, Boarding.moved u _ (by
        unfold QuadClock.Earlier; rw [←sitV,rpt,Shape.nodex,fling_there]; exact g)⟩


lemma Rouge.tint(h: Rouge P c s q k a):Rouge P c s q k (a.spin i z):=by
 obtain ⟨b,u,v,e⟩:=h
 have w :node ((a.spin i z).r)=(plane i z).anon N' (node a.r):=by simp only [Shape.nodex]
 exact ⟨by rw [w];exact mem_image_of_mem _ b, flurry t i z e⟩

lemma payBlush {r S X U V}
 (h:Boarding P q k s c.m c.a c.b c.f c.g r S X U V):
 AtSupport false S X ∧ ∀ x,‖X x‖≤ι':=by
 cases h
 case home u=>
   have b:=(posed0 P q k s t.reef.clearing u t.reef.toll.le).glow
   exact ⟨b.realc,b.suprem⟩
 case moved u a g=>
   have b:=(posed P q k s a t.reef.clearing u t.reef.toll.le t.reef.stop.le g).glow
   exact ⟨b.realc,b.suprem⟩

lemma Rouge.paid(h: Rouge P c s q k a):
  AtSupport false a.A.S a.A.x ∧ ∀ x,‖a.A.x x‖≤ι':=by
 obtain ⟨u,v,z⟩:=h.fare; exact payBlush t z


omit t
abbrev wireG (B:ℕ):= 2*(B^3+B)
abbrev Safe {n:Side}(B:ℕ)(u v:Blush n) := Distant (wireG B+1) u.A.S v.A.S
def Tango (P:Spine)(c:Cuts)(s q k:ℕ)(A:Hookah (kitGap P s q)):Prop:=
   ∃ a b,Rouge P c s q k a ∧ Rouge P c s q k b ∧ Safe (shaft P s) a b ∧ 
     A.x=a.A.x*b.A.x ∧ A.S=a.A.S∪b.A.S
def vaudeville (P:Spine)(c:Cuts)(d:Stores)(s q k:ℕ)(v:Seating P c d s q k):Club (kitGap P s q) where
 accepts:= Tango P c s q k
 title A := by
   rintro ⟨a,b,w,g,_,x,r⟩;rw [r,x]
   exact ((w.paid v).1.mono subset_union_left).mulM ((g.paid v).1.mono subset_union_right)
 dance A i z := by
   rintro ⟨a,b,w,g,e,x,r⟩
   refine ⟨_,_,w.tint v i z,g.tint v i z,sparse_face e i z,?_,?_⟩
   · funext t
     change theta _ (A.x _)=_
     rw [x,Pi.mul_apply,theta_mul]; rfl
   change hyphen _ _ _= _
   rw [r]; exact Finset.image_union _ _

abbrev drew (t:Seating P c d s q k):=vaudeville P c d s q k t

include t
lemma feathers{L:List (Hookah (kitGap P s q))}(v:Romp (drew t) (wireG R✽) L):
 ∃ J:List (Blush N'),J.Pairwise (Safe R✽) ∧ J.length=2*L.length ∧ buffet L=(J.map (fun a=>a.A.x)).prod ∧
   ∀ a∈J,Rouge P c s q k a ∧ ∃ x∈L, a.A.S⊆x.S:=by
 induction L with
 | nil=>exact ⟨[],List.Pairwise.nil,by simp,buffet_empty, by simp⟩
 | cons A L ih=>
   let y:=List.pairwise_cons.mp v.annex
   obtain ⟨J,f,e,d,b⟩:= ih ⟨fun x g=> v.core _ (List.mem_cons_of_mem _ g), y.2⟩
   obtain ⟨a,c',g,h,s,g',h'⟩:=v.core A List.mem_cons_self
   have t₀:a.A.S ⊆ A.S:=by rw [h'];exact subset_union_left
   have t₁:c'.A.S ⊆ A.S:=by rw [h'];exact subset_union_right
   have r {w:Blush N'}(r:w.A.S⊆ A.S) : ∀ x∈J, Safe R✽ w x := by
      intro x l z t u v
      obtain ⟨_,p,e,d⟩:=b x l
      exact y.1 p e z (r t) u (d v)
   refine ⟨a::c'::J, List.pairwise_cons.mpr ⟨?_,List.pairwise_cons.mpr ⟨r t₁,f⟩⟩,
          by simp;omega,by rw [buffet_more,d,g',List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,mul_assoc],?_⟩

   · intro b₀ p; rcases List.mem_cons.mp p with rfl|e; exact s;exact r t₀ b₀ e
   intro x p
   rcases List.mem_cons.mp p with p|p; subst x;exact ⟨g,A,List.mem_cons_self,t₀⟩
   rcases List.mem_cons.mp p with p|p; subst x;exact ⟨h,A,List.mem_cons_self,t₁⟩
   obtain ⟨hs,w,x₁,u⟩:=b x p
   exact ⟨hs,w,List.mem_cons_of_mem _ x₁,u⟩
