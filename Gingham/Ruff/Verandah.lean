import Gingham.Ruff.Bustle
import Gingham.Ruff.Trellis

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

/-- ledger for occupied *one-body* block on S. -/
def Ensign (S:Support (More N)): Submodule ℂ (OP N) where
  carrier:= {M|∀ i j:Single N,M i j≠0→
       node i.1.1∈S ∧ node j.1.1∈ S}
  zero_mem':=fun _ _ n=>False.elim (n rfl)
  add_mem':= by
    intro A B h t i j n
    by_cases e:A i j=0
    · apply t i j
      rwa [Matrix.add_apply,e,zero_add] at n
    exact h i j e
  smul_mem':= by
    intro c A h i j n
    apply h i j
    intro b
    exact n (by rw [Matrix.smul_apply,b,smul_zero])
lemma fell {S:Support (More N)}{M:OP N}
     (h:M∈Ensign S): ∀i j,M i j≠0→i∈modesIn N S ∧ j∈modesIn N S:=by
  intro i j e;rw [modes_at,modes_at]; exact h i j e

lemma stripes {S:Support (More N)}{M:OP N}
     (h:M∈Ensign S):Sector (modesIn N S) false (dg M):=by
     apply pair_charge; ext i j
     rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
     by_cases t:M i j=0
     · simp [t]
     obtain ⟨k,s⟩:=fell h i j t
     rw [if_pos k,if_pos s,one_mul,mul_one]

lemma badgeRibbon {M:Orbit N→OP N}{y:Site N}{S}
    (v:Matinee p y e c M)(h:belle y p.B⊆S)(x:Orbit N): M x∈Ensign S:=by
    intro i j n
    obtain ⟨w,z,k,t,r⟩:=v.fees
    obtain ⟨u,v⟩:= k i j ((norm_pos_iff.mpr n).trans_le (t ..)).ne'
    exact ⟨h u,h v⟩
lemma WWg(y:Site N){S}(v:node y∈S): WW y∈Ensign S:=by
  intro i j h
  have g:=WWi y 1 i j; rw [mul_one,Matrix.one_apply] at g
  rw [g] at h;split_ifs at h with k e
  · unfold cabin at k; subst i
    exact ⟨k.symm ▸ v,k.symm ▸ v⟩
  all_goals contradiction

abbrev Pall(p:BudgetPoint)(d:Shape)(N:Side):=hoop (@flagAnchor N d) (2*p.B)
lemma house (y:Site N)(r:Cover)(h:∀i,|r i|≤u.val):
 separation (bouton y) (bouton (y+wrap N r))≤ 2*u.val:=by
 rw [separation_comm,Lattice.separation,bouton,bouton,←Ratio.root_embed,←Ratio.root_embed,
    map_add,add_sub_cancel_left,Ratio.root_embed,Ratio.embed_wrap]
 apply Work.E01.pdist_wrap_le
 rw [Lattice.box,mem_Icc]
 constructor
 · intro i; change -((2*u.val:ℕ):ℤ)≤(2:ℕ) • (r i); rw [two_smul]
   have z:=(abs_le.mp (h i)).1;omega
 intro i;change (2:ℕ) • r i ≤ Nat.cast (2*u.val); rw [two_smul]
 have z:=(abs_le.mp (h i)).2;omega

include G
lemma housing {w:Cover}(v:∀i,|w i|≤u.val):
    belle (crossAnchor (N:=N) d w) p.B ⊆ Pall p d N:=by
   apply halo_spread (s:=2*u.val) _ (by
      have y:=G.largeB; unfold widthL at y;omega)
   intro a t
   obtain rfl:=mem_singleton.mp t
   unfold flagAnchor crossAnchor
   rw [bouton_finale,bouton_finale d,finale_lag]
   unfold Shape.anon Lattice.affine
   rw [separation_translate,separation_signed]
   exact house 0 w v

lemma balk: hitchAt N u d ∈ Ensign (Pall p d N):=by
 unfold hitchAt block
 apply Submodule.sum_mem;intro x t
 let y:=flagAnchor (N:=N) d
 have a:=house (u:=u) y x (fun i=>abs_le.mpr
  ⟨(apron_spec.mp t i).1, (apron_spec.mp t i).2.le⟩)
 apply WWg;apply halo_spec.mpr
 refine ⟨bouton y,mem_singleton_self _,
   (separation_triangle _ (bouton _) _).trans ((Nat.add_le_add a (bouton_clear _)).trans ?_)⟩
 have z:=G.largeB;unfold widthL at z
 omega

lemma furnished(x: Orbit N):
  B.fill g d U true x ∈ Ensign (Pall p d N):=by
  unfold fill surplus;apply Submodule.sum_mem
  intro i _
  refine Submodule.sub_mem _
   (badgeRibbon (opera g G (B.streamer d U i _)) (housing G d ?_) x)
   (badgeRibbon (opera g G (B.streamer d U i _)) (housing G d ?_) x)
  all_goals
    intro j; simp only [advanceNeg,Pi.neg_apply,advancePlus,hem_apply]
    split<;>simp

lemma Lawn(x:Orbit N):
 Sector (modesIn N (Pall p d N)) false (B.pen g d U x) ∧
 Sector (modesIn N (Pall p d N)) false (B.villa g d U x):=by
 have subF {a b:FC (Single N)} {s:Finset (Single N)}
 (p:Sector s false a)(q:Sector s false b): Sector s false (a-b):=
   by rw [sub_eq_add_neg,←neg_one_smul ℂ b];exact p.add (q.scale _)
 have t:=B.furnished g G d U x
 constructor
 · rw [pen,portico,touchP]
   exact Sector.add (Sector.one.scale _) (fine_𝒿 _
     (s:=Tset N) (fell t)).sector
 exact subF (Sector.add (Sector.one.scale _) (stripes t)) (subF (stripes
    (balk (N:=N) G d)) (Sector.one.scale _))

#print axioms Lawn

