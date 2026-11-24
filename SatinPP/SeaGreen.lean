import SatinPP.Blue

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal

section Wall
variable {σ:Type}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)
   (X:σ→H.Op)(u v s t:σ→ℝ)
local notation "E(" x ")" => S.E (Real.toNNReal x)
local notation "R"=>Aria.rector S X u v
local notation "J"=>Aria.behind S X u v s t
local notation "R'"=>Aria.rector S (Aria.behind S X u v s t) s t
lemma wreath (hΩ:∀ e,S.E e Ω=Ω) (h:s≤u)(k:v≤t) {L:List σ}
    (p:L.Pairwise (fun i j=> t i < s j)) (b:ℝ)
    (ht: L≠[] → b≤before s L):
    R' L b Ω=R L b Ω:=by
 induction L generalizing b with
 | nil=>rfl
 | cons i L ih=>
   have a:b ≤ s i:= ht (List.cons_ne_nil _ _)
   obtain ⟨o,p⟩:=List.pairwise_cons.mp p
   have c(e:L≠[]):t i<before s L ∧ t i<before u L:=by
      cases L with
      | nil=>exact(e rfl).elim
      | cons j _=>exact ⟨o j (List.Mem.head ..),(o j (List.Mem.head ..)).trans_le (h j)⟩
   have z:=ih p (t i) (fun e=>(c e).1.le)


   have y:=rector_deeper S Ω X u v hΩ (v i) (t i) L (k i) (fun e=>(c e).2.le)
   change E(s i-b) (E(u i-s i) (X i (E(t i-v i) (R' L (t i) Ω))))=E(u i-b) (X i (R L (v i) Ω))
   rw [z,y,← ContinuousLinearMap.comp_apply,terraces _ _ _ (sub_nonneg.mpr a) (sub_nonneg.mpr (h _)),show s i-b+(u i-s i)=u i-b by abel]
lemma ribbon (hΩ:∀ e,S.E e Ω=Ω) (h:s≤u)(k:v≤t) {L:List σ}
    (p:L.Pairwise (fun i j=> t i < s j)):
    receive S Ω J s t L=receive S Ω X u v L:=by
 unfold receive
 rw [wreath S Ω X u v s t hΩ h k p _ (fun _=>le_refl _)]
 exact rector_view S Ω X u v hΩ _ L
variable {K:Axis→Hilbert}(W:∀ a, OS.Semigroup (K a) a)(Z:∀ a,(K a).space)
 (F:σ→Shrine K)(x:σ→E4)(L:List σ)(a:Axis)

lemma land_port :
    Land.chorus W Z F x L a = receive (W a) (Z a) (actO W F x a) (startX F x a) (endX F x a) L :=by
 let A:=actO W F x a
 let d:=startX F x a
 let e:=endX F x a
 let T:=rector (W a) A d e
 let V:=Hierarchy.Mist.TapeT A (Leap W F x a)
 have m (i:σ)(l:List σ):V (i::l)=(A i).comp (T l (e i)):=by
    induction l generalizing i with
    | nil=>rfl
    | cons j l ih=>
       change A i * (_*V (j::l)) = _
       rw [ih]
       rfl
 cases L with
 | nil=>rfl
 | cons i l=>
    change inner ℂ _ (V (i::l) _) = inner ℂ _ (T (i::l) (d i) _)
    dsimp only [T]; rw [m,rector_left,sub_self,Real.toNNReal_zero,(W a).eZero]; rfl
end Wall

variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ" j:max => P.advocate 3 x j
local notation "K₁" j:max => P.ManyF j (P.advocate 3 x j)
local notation "Π'" j:max=>P.wealth j (P.advocate 3 x j)

/-- G (continuous-space) spacetimes at the Satin election, in Vantage units. -/
abbrev houses: Axis→Hilbert:=fun j=>K₁ j
abbrev socials (j:Axis):OS.Semigroup (P.houses x j) j:=P.seasons j (ξ j)
abbrev lights (j:Axis):(P.houses x j).space:=P.heaven j (ξ j)

local notation "Sh"=>Shrine (P.houses x)
local notation "W"=>P.socials x
local notation "ω"=>P.lights x

def allot (A:P.Apron)(f:Axis→ℝ≥0): Shrine (P.houses x):=
   ⟨f,fun j=>P.seating j x (P.locket j (ξ j) A (f j) (f j))⟩
abbrev Longer(A:P.Apron)(f:Axis→ℝ≥0):Prop :=∀ j,A.realWidth P j ≤ f j
/-- standard WOT sources -/
def Lore:Set Sh := {S| ∃A:P.Apron,P.Longer A S.t ∧ P.allot x A S.t=S}


variable (j:Axis)
local notation "S"=>P.socials x j

lemma light_on (u v:ℝ) (Y:(P.houses x j).Op)(p:E4):
  opt S p (jacket S u v Y) = jacket S u v (opt S p Y):=by
  change Land.leg S p * ((S).E u.toNNReal * Y * (S).E v.toNNReal) * Land.leg S (-p)=
     (S).E _ * (Land.leg S p * Y * Land.leg S (-p)) * (S).E _
  rw [mul_assoc, mul_assoc ((S).E u.toNNReal)]
  simp_rw [mul_assoc]
  rw [(leg_e S (-p) _).eq,←mul_assoc,(leg_e S p _).eq.symm,mul_assoc] -- try


variable {σ:Type}(Y:σ→Shrine (P.houses x))(A:σ→P.Apron)(p:σ→E4)(L:List σ)
variable (k:∀ i,P.Longer (A i) (Y i).t ∧ P.allot x (A i) (Y i).t=Y i)
local notation "l"=>startX Y p j
local notation "r"=>endX Y p j
local notation "b"=>P.porchY j A (roll ∘ p)
local notation "e"=>P.resignY j A (roll ∘ p)
include k

lemma actO_price (i:σ):
   actO W Y p j i =
     Aria.behind S (P.commuteTight j (ξ j) A (roll ∘ p)) b e l r i:=by
 let α:= (A i).realWidth P j
 let z:= p i j
 let D:=(Y i).t j
 let d:ℝ:= D-α
 have ll:b i-l i=d:= by change z-α-(z-D)=↑D-α; ring
 have rr:r i-e i=d:= by change z+↑D-(z+α)=↑D-α; ring
 let t:=P.seating j x ((A i).engine P j (ξ j))
 have v:
     opt S (p i) t=P.commuteTight j (ξ j) A (roll ∘ p) i:=by
   unfold opt
   have h(x0:E4):Land.leg S x0=P.cartage j (ξ j) (roll x0):=P.Q_cart j (ξ j) x0
   rw [h,h,map_neg]; rfl


 have q:(Y i).f j=jacket S d d t := by
   nth_rw 1 [←(k i).2]; exact P.seating_jacket j x d d ((A i).engine P j (ξ j))
 unfold actO Plot Aria.behind; rw [q,ll,rr,light_on,v]; rfl

lemma Lore_chorus (h:L.Pairwise (Seers Y p j)):
    P.Turnstile j A L (roll ∘ p) ∧
    Land.chorus W ω Y p L j = P.memorial j (ξ j) A L (roll ∘ p):=by
 have lq:l ≤ b:=fun i=>sub_le_sub_left ((k i).1 j) _
 have er:e ≤ r:=fun i=>by change p i j + _ ≤ p i j + _;exact add_le_add le_rfl ((k i).1 j)
 refine ⟨h.imp (fun {i z} t=>(er i).trans_lt (lt_of_lt_of_le (show r i < l z from t) (lq z))),?_⟩
 rw [land_port,funext (P.actO_price x j Y A p k)]
 exact ribbon S (ω j) _ b e l r (P.heaven_hot _ _) lq er h

#check @Lore_chorus
#print axioms Lore_chorus

omit k
lemma philosophy (Z:P.Ellis 3 x)(m:Axis): Philos (σ:=σ) W ω j m (P.Lore x):=by
 intro F y p L M hy _ hx ht
 choose H u using (show ∀ i,∃D,P.Longer D (F i).t ∧ P.allot x D (F i).t=F i from y)
 obtain ⟨v,a⟩:=P.Lore_chorus x j F H p L u hx
 obtain ⟨w,h⟩:=P.Lore_chorus x m F H p M u ht
 exact a.trans (((P.common_cult 3 x H (roll ∘ p) L Z (List.Perm.refl _) v).symm.trans (P.common_cult 3 x H (roll ∘ p) L Z hy w)).trans h.symm)
abbrev Cathedral:= Matte.Spigot (P.Lore x)
lemma philosophize [DecidableEq σ][Fintype σ](Z:P.Ellis 3 x)(m:Axis): Philos (σ:=σ) W ω j m (P.Cathedral x):=by
 intro F y p L M pm h u v
 exact Matte.transferUp W ω (P.Lore x) F p L M j h m (pm.nodup_iff.mp h)
   (fun f z=>P.philosophy x j Z m f z p L M pm h) y u v

#print axioms philosophize
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
