import Bay.D.Monsoon
import Bay.D.Masala
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Buffered Lamour.Bridge.Celeste.Clock Fabric
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow Papal
open Vale clocks
open YM.CF.Pannier.Chancel Journey Tower Tower.SlabMark VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

/-- The cover prescription for one complex first-Pane stencil. -/
structure Cache (K:Calibration)(S:Finset Cover) where
  pool:ℕ→Buffered.Family K
  lake:Dome K
  good:BQueue S pool lake.val
structure Lake (K:Calibration)(S:Finset Cover) where
  sun:Cache K S
  ray:Cache K S

variable {N:Side}{S T:Finset Cover} {K: Calibration}{i:ℕ}

namespace Cache
def union (x y : Cache K S):Cache K S:=
 ⟨x.pool+y.pool,x.lake+y.lake,trip_add x.good y.good⟩
def dropz (q:ℂ) (x:Cache K S):Cache K S:=
 ⟨q•x.pool,q•x.lake,trip_scale x.good q⟩
def mulC (x : Cache K S) (y:Cache K T):Cache K (S∪T):=
 ⟨x.pool*y.pool,x.lake*y.lake,BQueue.multiply x.good y.good⟩
def reflection (x:Cache K S) (r:ℤ):Cache K (reflectedBox 3 r S):=
 ⟨fun i=> mirror K 3 r (x.pool i),aureole K 3 r x.lake,x.good.revolve 3 r⟩
def moved (x:Cache K S) (r:ℤ):Cache K (plow K 3 r S):=
 let e:=x.good.station 3 r
 ⟨_,⟨_,aux_test e.landing⟩,e⟩
def tint (h:S⊆T)(x:Cache K S):Cache K T:= ⟨x.pool,x.lake,trip_enlarge h x.good⟩
end Cache

namespace Lake
def allLake(x:Lake K S): Dome K:= x.sun.lake + Complex.I • x.ray.lake

/-- Meanings to test at ONE actual-volume regulator only, for both real letters. -/
def Seal (x:Lake K S) (i:ℕ)(m:Side)(e:K.c m=N)(F:Pane N→ℂ):Prop:=
  arrange _ _ e (x.sun.pool i m)=Hookah.chalkOp (fun y=>((F y).re:ℂ)) ∧
  arrange _ _ e (x.ray.pool i m)=Hookah.chalkOp (fun y=>((F y).im:ℂ))

def tint(h:S⊆T)(x:Lake K S): Lake K T:= ⟨x.sun.tint h,x.ray.tint h⟩
def stream(x:Lake K S)(y:Lake K T): Lake K (S∪T) where
 sun := (x.sun.mulC y.sun).union ((x.ray.mulC y.ray).dropz (-1))
 ray := (x.sun.mulC y.ray).union (x.ray.mulC y.sun)

lemma flow (x:Lake K S)(y:Lake K T):
    (x.stream y).allLake=x.allLake*y.allLake:=by
 let a:=x.sun.lake
 let b:=x.ray.lake
 let c:=y.sun.lake
 let d:=y.ray.lake
 change a*c + (-1:ℂ)•(b*d)+Complex.I•(a*d+b*c)=(a+Complex.I•b)*(c+Complex.I•d)
 rw[add_mul,mul_add,mul_add]
 simp only[Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul,smul_add,Complex.I_mul_I]
 abel

variable {x:Lake K S}{y:Lake K T} {m:Side}{e:K.c m=N}{F G:Pane N→ℂ}
lemma Seal.stream (p:Seal x i m e F)(q:Seal y i m e G):
 Seal (x.stream y) i m e (F*G):=by
 subst N
 obtain ⟨p,v⟩:=p
 obtain ⟨q,u⟩:=q
 change x.sun.pool i m=_ at p
 change x.ray.pool i m=_ at v
 change y.sun.pool i m=_ at q
 change y.ray.pool i m=_ at u
 constructor
 · funext X
   change x.sun.pool i m X*y.sun.pool i m X + (-1:ℂ)•(x.ray.pool i m X*y.ray.pool i m X) = (((F X.1*G X.1).re:ℂ))•1
   rw[p,q,u,v]
   simp only[Hookah.chalkOp,Algebra.smul_mul_assoc,one_mul,smul_smul,Complex.mul_re,
     Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_mul,add_smul,neg_one_mul,neg_smul,sub_eq_add_neg]
 funext X
 change x.sun.pool i m X*y.ray.pool i m X + x.ray.pool i m X*y.sun.pool i m X = (((F X.1*G X.1).im:ℂ))•1
 rw[p,q,u,v]
 simp only[Hookah.chalkOp,Algebra.smul_mul_assoc,one_mul,smul_smul,Complex.mul_im,
    Complex.ofReal_add,Complex.ofReal_mul,add_smul]

def jab(x:Lake K S)(r:ℤ): Lake K (reflectedBox 3 r S):=
 ⟨x.sun.reflection r,(x.ray.reflection r).dropz (-1)⟩

lemma shore(x:Lake K S)(r:ℤ): (x.jab r).allLake=aureole K 3 r x.allLake:=by
 rw[allLake,allLake,map_add,map_smulₛₗ,starRingEnd_apply,
   Complex.star_def,Complex.conj_I]
 dsimp[jab,Cache.reflection,Cache.dropz]
 rw[smul_smul,mul_neg_one]

abbrev skip(N:Side) (r:ℤ):Kite (More N):= ⟨Signed.mirror 3,wrap _ (2 • (r • step 3))⟩

lemma Seal.jab (p:Seal x i m e F)(r:ℤ):
 Seal (x.jab r) i m e (star (F ∘ (skip N r).swirl)) :=by
 subst N
 obtain ⟨p,v⟩:=p
 change x.sun.pool i m=_ at p
 change x.ray.pool i m=_ at v
 constructor
 · funext X
   change reflMark 3 r (x.sun.pool i m) X=((star (F ((skip _ r).swirl X.1))).re:ℂ)•_
   rw[p]
   simp only[reflMark,Hookah.chalkOp,Fock.theta_smul,Fock.theta_one,
     Complex.star_def,Complex.conj_re,Complex.conj_ofReal];rfl
 funext X
 change (-1:ℂ)•reflMark 3 r (x.ray.pool i m) X=((star (F ((skip _ r).swirl X.1))).im:ℂ)•_
 rw[v]
 simp only[reflMark,Hookah.chalkOp,Fock.theta_smul,Fock.theta_one,
   Complex.star_def,Complex.conj_im,Complex.conj_ofReal,
   one_smul,Complex.ofReal_neg,neg_smul];rfl

def downstream(x:Lake K S)(a:ℤ):Lake K (plow K 3 a S):=
 ((x.jab 0).jab (gaugeT K a)).tint (by rw[support_translation,sub_zero]; exact Subset.refl _)

lemma sail(P:VacuumSelection.Spine)(l:Lake P.calibration S)(a:ℤ):
    (l.downstream a).allLake=P.shifts 3 a l.allLake:=by
 unfold downstream
 suffices ((l.jab 0).jab (gaugeT P.calibration a)).allLake=_ from this
 rw[shore,shore]
 rfl
abbrev jumper (K:Calibration)(N:Side)(a:ℤ):=
 wrap (More N) ((ruler K.B*a) • step 3)
lemma skied(a:ℤ):
 (skip N (gaugeT K a)) * skip N 0 = forward (jumper K N a) :=by
 unfold skip forward jumper
 change Kite.mk (Signed.mirror 3*Signed.mirror 3) (affine (Signed.mirror 3)
    (wrap _ (2 • ((gaugeT K a) • step 3))) (wrap _ (2 • ((0:ℤ) • step 3))))=_
 apply congrArg₂
 · nth_rw 2 [← Signed.mirror_inv]
   rw [mul_inv_cancel]
 simp only [zero_smul,smul_zero,map_zero,affine,Signed.act_zero,zero_add]
 apply congrArg
 have p : 2*(gaugeT K a)=ruler K.B*a:=by unfold gaugeT Heat.gaugeShift ruler; ring
 rw [←p,mul_smul]; simp


lemma Seal.downstream (p:Seal x i m e F)(a:ℤ):
 Seal (x.downstream a) i m e (F ∘ (forward (jumper K N a)).swirl) :=by
 have h:= (p.jab 0).jab (gaugeT K a)
 have l: star (star (F ∘ (skip N 0).swirl) ∘ (skip N (gaugeT K a)).swirl)= F ∘ (forward (jumper K N a)).swirl:=by
   funext X
   rw [Pi.star_apply,comp_apply,Pi.star_apply,comp_apply,comp_apply,star_star,Kite.union,skied]
 rw [l] at h
 exact h

def swallow(x:Lake K S) (a:ℤ):Lake K (reflectedBox 3 0 (plow K 3 a S)):=
 (x.downstream a).jab 0
lemma downbird (p:Seal x i m e F)(a:ℤ) (c:Seat N)
   (w:c=(Signed.mirror 3).act (jumper K N a)):
 Seal (x.swallow a) i m e (star (F ∘ (after c).swirl)):=by
 have hp:(skip N 0) * forward (jumper K N a)=after c:=by
    change Kite.mk (Signed.mirror 3 * 1) ((Signed.mirror 3).act _ + wrap _ (2 • ((0:ℤ) • step 3)))=_
    simp only [mul_one,w,zero_smul,smul_zero,map_zero,add_zero]
    rfl
 have h:=(p.downstream a).jab 0
 have : (F ∘ (forward (jumper K N a)).swirl) ∘ (skip N 0).swirl=F ∘ (after c).swirl:=by
    funext X
    simp only[comp_apply,Kite.union,hp]
 rw[this] at h; exact h

abbrev paint(K: Calibration)(S:Finset Cover)(a:ℤ):= reflectedBox 3 0 (plow K 3 a S) ∪ plow K 3 a S
def tones (x:Lake K S) (a:ℤ): Fin 3→Lake K (paint K S a):=
 ![(x.downstream a).tint subset_union_right,
   (x.swallow a).tint subset_union_left,
   (x.swallow a).stream (x.downstream a)]

lemma tone_three (p: Seal x i m e F)(a:ℤ) (c:Seat N)
   (w:c=(Signed.mirror 3).act (jumper K N a)) (j:Fin 3):
 Seal (x.tones a j) i m e (strata F (forward (jumper K N a)) (after c) j):=by
 have h:=downbird p a c w
 have q:=p.downstream a
 fin_cases j
 · exact q
 · exact h
 change Seal _ _ _ _ (_*_)
 rw[mul_comm]
 exact h.stream q

abbrev notes (P:VacuumSelection.Spine)(x:P.Test):Fin 3→P.Test:=
 ![x,P.reflectTest 3 x,P.reflectTest 3 x * x]
lemma tone_clause (P:VacuumSelection.Spine) (x:Lake P.calibration S)
    (a:ℤ)(j:Fin 3):
   (x.tones a j).allLake=notes P (P.shifts 3 a x.allLake) j:=by
 have e := sail P x a
 have q:(x.swallow a).allLake=P.reflectTest 3 (P.shifts 3 a x.allLake):=by
    unfold swallow
    rw [shore,e]
 fin_cases j
 · exact e
 · exact q
 change ((x.swallow a).stream (x.downstream a)).allLake=_ 
 rw [flow,q,e];rfl
end Lake
