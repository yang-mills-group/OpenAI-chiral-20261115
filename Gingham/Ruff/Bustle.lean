import Gingham.Ruff.Minuet

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical

open Nacre


open Buffered
open Reed (Fine think)
set_option synthInstance.maxSize 16000

namespace GarlandBook

variable {p:BudgetPoint}{u:Side}{r l:ℕ}{E a c e:ℝ}
    {U':Scree.Loom N}{f h:Chin N→OP N}
    (B:GarlandBook u a c e f h)(g:Briefly p r e U')
    (G:Tagbill a E u l r p.B)
    (d:Shape)(U:UNI SpinIdx)
    (T:Plumes f h a c e)(j:JetS d.s false (detX d.s) U)

def fountain:= cupN false (B.tire g)
def fountainQ (v:Pane N):ℂ:= Matrix.trace (B.tire g (v,dustId N))
lemma fountainPure(x:Fields N): B.fountain g x=B.fountainQ g x.1 • 1:=rfl
def bassin(i:Axis):= cupN true (B.eye g i)
abbrev foufee(u:Side)(e a c:ℝ):=costGlass e (pepCharge u a c)
def beaker(i:Axis)(w:Cover) := cupN true (B.eyeAt g w i)
abbrev basinfee(u:Side)(e a c:ℝ):=costGlass e (tableland^2 * pepCharge u a c)
include G
lemma fountain_premier: Premier (B.fountain g) 0 p (foufee u e a c):= wear3 (opera g G B.pump) false
lemma bassin_premier(i:Axis):
 Premier (B.bassin g i) 0 p (foufee u e a c):=wear3 (opera g G (B.point i)) true
lemma beaker_premier(i:Axis)(w:Cover):Premier (B.beaker g i w) (wrap N w) p
  (basinfee u e a c):=by
 have z:=wear3 (opera g G (B.lamprey w i)) true
 change Premier (B.beaker g i w) _ _ _ at z
 rw [finale_lag,zero_add] at z
 exact z
lemma beaker_style(i:Axis)(w:Cover):
 style (lagX w) 1 (B.bassin g i)= B.beaker g i w:=by
  funext x; have t:detX (lagX w).s=false:=det_i
  unfold style rotary;rw [t,if_neg (by decide:false≠true)]
  exact B.shiften g G w i (pitchK x) (pitchK _) rfl

lemma beaker_axis(i:Axis)(s:ℤ):
  reflMark i s (reflMark i 0 (B.bassin g i))= B.beaker g i (hem i s):=by
 rw [moveQ i s (B.bassin_premier g G i).good,B.beaker_style g G]
omit G
def brim :Mark N :=
 B.fountain g+ ∑i,(B.beaker g i (advancePlus u i) -
                         B.beaker g i (advanceNeg u i))
theorem balm(x:Fields N):
 B.brim g x = B.brocade g (pitchK x):=by
 rw [B.brocade_eq g,brim,Pi.add_apply]
 congr 1

/-- The Mark stencil. -/
def vase (u:Side)(A:Mark N)(Z:Axis → Mark N): Mark N:=
 A + ∑i,(reflMark i u.val (reflMark i 0 (Z i)) -
         reflMark i (-(u.val:ℤ)) (reflMark i 0 (Z i)))

include G in
lemma brink: vase u (B.fountain g) (B.bassin g)= B.brim g:=by
 unfold brim vase
 congr 1
 refine sum_congr rfl fun i _=>?_
 rw [beaker_axis B g G,beaker_axis B g G]
 have h:hem i (-(u.val:ℤ))=advanceNeg u i:=neg_smul ..
 rw [h]

def Loyal (S:Support (More N)): Submodule ℂ (Mark N) where
 carrier := {F|AtSupport false S F ∧ covariant F}
 zero_mem' :=⟨AtSupport.zeroM, fun _ _=> (map_zero _).symm⟩
 add_mem' := by
    intro f k v t
    obtain ⟨v,u⟩:=show AtSupport false S f ∧ covariant f from v
    obtain ⟨t,w⟩:=show AtSupport false S k ∧ covariant k from t
    refine ⟨v.addM t, fun p x=>?_⟩
    rw [Pi.add_apply,u,w,Pi.add_apply,map_add]
 smul_mem' := by
   rintro c f ⟨v,w⟩
   refine ⟨v.smulM c,fun p x=>?_⟩
   rw [Pi.smul_apply,w,Pi.smul_apply,twist_scalar]

lemma lower {y:Site N}{F:Mark N}{s:ℝ}(t:Premier F y p s)
 {S:Support (More N)}(j:beagle y p⊆S):
 F∈Loyal S:= ⟨t.good.mono j,t.tint⟩

def crinoline (p:BudgetPoint)(u:Side):=
  hoop (0:Site N) (p.B+2+2*u.val)

lemma hip(p:BudgetPoint)(u:Side){x:Cover}(w:∀i,|x i|≤u.val):
 beagle (wrap N x) p⊆ crinoline p u:=by
 apply halo_spread (s:=2*u.val) _ le_rfl
 intro i v
 obtain rfl:=mem_singleton.mp v
 rw [bouton,bouton,←Ratio.root_embed,map_zero,Ratio.embed_wrap,separation_comm,Lattice.separation,sub_zero]
 apply Work.E01.pdist_wrap_le
 rw [Lattice.box,mem_Icc]
 constructor
 · intro i; obtain ⟨c,v⟩:=abs_le.mp (w i)
   change -( (2*u.val:ℕ):ℤ) ≤ (2:ℕ) • (x i)
   rw [two_smul]
   omega
 intro i; obtain ⟨c,v⟩:=abs_le.mp (w i); change (2:ℕ) • x i ≤ Nat.cast (2*u.val); rw [two_smul];omega

include G
lemma hoopdance: B.brim g∈Loyal (crinoline p u):=by
  apply (Loyal ..).add_mem (lower (B.fountain_premier g G)
    (Corona.halo_mono (by omega) le_rfl))
  apply (Loyal ..).sum_mem
  intro i _
  apply (Loyal ..).sub_mem (lower (B.beaker_premier g G i _) (hip _ _ ?_))
         (lower (B.beaker_premier g G i _) (hip _ _ ?_))
  all_goals intro j; simp only [advanceNeg,Pi.neg_apply,advancePlus,hem_apply];split <;> simp

#print axioms hoopdance


abbrev marksleeve (word:List (Axis×ℤ))(x:Fields N):=
 (Yg (maidS word) x.1, Yg (maidS word) x.2)

lemma heraldry(word:List (Axis×ℤ))(x:Fields N)(z:Orbit N)(t:z.1=x.1):
 maiden word (B.brim g) x=
 ribbonSign (maidS word) (B.pen g (maidS word) (maidU word) z):= by
 rw [procession word (B.hoopdance g G).1,style,B.balm]
 apply B.ornate g G _ _ (maidJ word)
 simp [pitchK,t]

#print axioms heraldry

