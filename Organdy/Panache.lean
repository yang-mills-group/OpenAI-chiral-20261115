import Organdy.Scabbard

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

open Hive Levier Urn

-- Frame proof for projected pieces, independent of election
private lemma windSector{I:Type*}[LinearOrder I][Fintype I] {S:Finset I}{A:FC I}{b:Bool}
 (c:Bool) (p:Sector S b A):Sector S b (windX c A):=by
 induction p with
 | zero=>rw [win_z]; exact .zero _
 | one=>rw [win_i];exact .one
 | up i e=>rw [Spire.win_up]; exact .up i e
 | down i e=>rw [takeF,win_s,Spire.win_up];exact .down i e
 | add _ _ h k=>rw [win_a];exact h.add k
 | mul _ _ h k=>rw [win_m];exact h.mul k
 | scale _ u h=>rw [win_c];exact h.scale _

lemma twisted_teen{I:Type*}[LinearOrder I][Fintype I]{S:Finset I}{A:FC I}{b:Bool}
 (c r:Bool)(U V W: UNI I)
 (h:U.val*windX c V.val=W.val * U.val)
 (p:Sector S b A):
  lotB c r U (twist (quantU V) A)=twist (quantU W) (lotB c r U A):=by
 let Y:UNI I:= if c then ccU V else V
 have y:windX c V.val=Y.val:=by cases c<;>rfl
 have e:U*Y=W*U:=Subtype.ext (by rw [y] at h;exact h)
 have H:windX c (twist (quantU V) A)=twist (quantU Y) (windX c A):=by
    rw [twist_formula,twist_formula]
    change windX _ (quant V.val*A*star (quant V.val))=_ 
    rw [win_m,win_m,win_s,swish,y];rfl

 cases r
 · change twist (quantU U) (windX c _)=twist (quantU W) (twist (quantU U) (windX c A))
   rw [H,←Fock.twin,←Fock.twin]
   exact congrArg (fun L=>twist L (windX c A))
      (Subtype.ext ((quant_mul U.val Y.val).symm.trans ((congrArg (fun L:UNI I=>quant L.val) e).trans (quant_mul W.val U.val)))) -- tune
 · change theta U (windX c _)=twist (quantU W) (theta U (windX c A))
   rw [H]
   exact Window.theta_twist_right _ _ _ (congrArg Subtype.val e) (windSector c p)

variable {N:Side}
abbrev maskX (s:Sweep N)(g:Seat N→SU.E):Seat N→SU.E:= polarT s.charge ∘ g ∘ boxA s

lemma turnFrame(c:Bool)(g:Seat N→SU.E):
 windX c (tradew N g).val= (tradew N (polarT c ∘ g)).val := by
 dsimp only [tradew]
 simp only [Function.comp, matterX]
 cases c
 · rfl
 · exact jump_cc ..


lemma teen_frame(s:Sweep N)(g:Seat N→SU.E)
 {S: Support (More N)}{b:Bool}{f:Mark N}
 (y:AtSupport b S f)(p:Buffered.covariant f)
 (v:Fields N):
 voltaM s f (simultaneous g v)= twist (quantU (tradew N g)) (voltaM s f v):=by
 let g':=maskX s⁻¹ g
 have a: voltaF s⁻¹ (simultaneous g v)=simultaneous g' (voltaF s⁻¹ v):=by
    let x:Dial.Stun N := Classical.arbitrary _
    exact Prod.ext (siren _ _ _ _ x g).1 (siren _ _ _ _ x g).1
 unfold voltaM;rw [a,p]
 apply twisted_teen _ _ _ _ _ _ (y.allV _).sector
 rw [turnFrame]

 let c:=s.charge
 let T:=castX s
 let h:=polarT c ∘ g'
 have w:h∘(castX s).anon N=g:=by
    funext i
    change polarT c (polarT c (g ((boxA s⁻¹) (boxA s i))))=_
    rw [sitU,Equiv.symm_apply_apply,polar_t,Bool.xor_self];rfl
 have z:=Nacre.envoy T (spinU c T.s) h
 rw [w] at z
 exact congrArg Subtype.val z

lemma flounce_title {K:Calibration} (T:Shape) (f:Dome K)(h:f∈enclave K):
 flounce K T f∈ enclave K:=by
 rw [enclave_spec] at h ⊢
 intro m
 let y:= (marque K).mp f.property
 let v:=y.paid.choose_spec
 change Buffered.covariant ((flick T f.val) m)
 rw [paidFlick T v]
 exact fun g u=>teen_frame _ g (v.support m) (h m) u

variable {P:Spine}{s:ℕ}{r q:ℕ}
lemma clothed {f:P.Test}(h:f∈ room P s):
 pauldron P.calibration f∈room P s:=by
 let D:=room P s
 rw [showtime]
 refine D.smul_mem (D.sum_mem fun v _=>D.smul_mem (show flounce P.calibration _ f∈room P s from
    ⟨?_,flounce_title _ f h.2⟩) _) _
 change InTest P.calibration true (mortise (shaft P s)) false (flick (incX v) f.val)
 let t:=flick_holds (incX v)
    (show InTest P.calibration true (mortise (shaft P s)) false f.val from h.1)
 rw [trims] at t
 exact t

variable {c:Cuts}{I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
variable (p:Parade l P c d s i k X F x)

def sylvan : Subalgebra ℂ P.Test where
 carrier:={f| ∀m,Lily (f.val m)}
 zero_mem':=fun _ _ _ _=>rfl
 one_mem':=fun _ _ _ _=>rfl
 mul_mem' {a b} h₁ h₂:=fun m x y z=>congrArg₂ (·*·) (h₁ m x y z) (h₂ m x y z)
 add_mem' {a b} h₁ h₂:=fun m x y z=>congrArg₂ (·+·) (h₁ m x y z) (h₂ m x y z)
 algebraMap_mem':=fun u=>by rw [Algebra.algebraMap_eq_smul_one];exact fun _ _ _ _=>rfl

def Place(P:Spine)(s:ℕ): Subalgebra ℂ P.Test:= room P s ⊓ sylvan

lemma birthright(j):labeled p j∈Place P s:=
 ⟨labeledInside p j, fun m=> ((p.pins j).2.2 m).1⟩

lemma bastion :
 corset p∈Place P s:= (Place P s).add_mem (birthright p _) ((Place P s).sum_mem
    (fun j _=>(Place P s).sub_mem (birthright p _) (birthright p _)))

lemma raisedHigh (v:Signed){f:P.Test}(h:f∈Place P s):
 flounce P.calibration (incX v) f∈ Place P s:=by
 refine ⟨⟨?_,flounce_title _ f h.1.2⟩,?_⟩
 · change InTest _ true (mortise (shaft P s)) false (flick _ f.val)
   let t:=flick_holds (incX v)
      (show InTest P.calibration true (mortise (shaft P s)) false f.val from h.1.1)
   rw [trims] at t; exact t

 · intro m
   change Lily (flick _ f.val m)
   rw [paidFlick (incX v)
      (show InTest P.calibration true (mortise (shaft P s)) false f.val from h.1.1)]
   intro x y z
   exact congrArg (teen _) (h.2 m _ _ _)

lemma appealPopularity {f:P.Test}(h:f∈Place P s):
 pauldron P.calibration f∈Place P s:=by
 rw [showtime]
 exact (Place P s).smul_mem ((Place P s).sum_mem (fun v _=>(Place P s).smul_mem (raisedHigh v h) _)) _

lemma hatBorne(j:Axis):
 hatAxis (tenor p) j∈Place P s:=
 (Place P s).smul_mem ((Place P s).sum_mem
     fun _ _=>(Place P s).smul_mem ((Place P s).smul_mem (raisedHigh _ (birthright p _)) _) _) _

theorem cashbox
 (m:Grand P c s)
 (o:reach (guineas P s) r)(n:Aligned P r q)
 {f:P.Test}(h:f∈Place P s):
 Stamped P s r q f:=
 cashesView P s n (inRegion r (m.path r o).2.2) f h.1.1 h.1.2

#print axioms hatBorne
#print axioms appealPopularity
