import Gingham.Ruff.Gazebo

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


namespace GarlandBook

variable {p:BudgetPoint}{u:Side}{r l:ℕ}{E a c e:ℝ}
    {U':Scree.Loom N}{f h:Chin N→OP N}
    (B:GarlandBook u a c e f h)(g:Briefly p r e U')
    (G:Tagbill a E u l r p.B)
    (d:Shape)(U:UNI SpinIdx)
    (T:Plumes f h a c e)(j:JetS d.s false (detX d.s) U)

def valance (a E c:ℝ)(u:Side)(l:ℕ):=
 fanbill a E (tableland^2*pepCharge u a c) u l
def torsade (a E c:ℝ)(u:Side)(l:ℕ):=
 fanbill a E (tableland^2*(tableland^2*pepCharge u a c)) u l
def Lint(a E c:ℝ)(u:Side)(l:ℕ):=
 valance a E c u l+2*(8*torsade a E c u l)
def nod(a:ℝ)(p:BudgetPoint):=Real.exp (-a*(p.B:ℝ)/3200)
include G

abbrev flagAnchor:=finale (N:=N) d 0
abbrev crossAnchor(w:Cover):=finale d (finale (N:=N) (lagX w) 0)
def soldA(β:Bool):
 Flares (flagAnchor d) u l r E (a/16) p (valance a E c u l)
   (B.trim g d U β):=
     latticeFieldEstimates g G (B.standard d U) β
def soldB(i:Axis)(w:Cover)(β:Bool):
 Flares (crossAnchor d w) u l r E (a/16) p (torsade a E c u l)
   (coinF g (B.streamer d U i w) β):=
     latticeFieldEstimates g G (B.streamer d U i w) β

def soldT:
 Flares (flagAnchor d) u l r E (a/16) p (nod a p*valance a E c u l)
   (B.trussEnd g d U):=
 plumeTail g G (B.standard d U)
def soldL(i:Axis)(w:Cover):
 Flares (crossAnchor d w) u l r E (a/16) p (nod a p*torsade a E c u l)
   (farF g (B.streamer d U i w)):=
 plumeTail g G (B.streamer d U i w)

lemma PE_buy {y:Site N}{k:ℝ}{A:Orbit N→OP N}
 (F:Flares y u l r E (a/16) p k A)(x:Orbit N): parce (A x) ≤ k:=
 (F.priceall x).trans (F.inall G.Epay (by linarith only [G.apos]))

lemma PE_fill(β:Bool)(x:Orbit N): parce (B.fill g d U β x) ≤ 8*torsade a E c u l:=
 PE_surplus _ _ (fun i=>⟨PE_buy G (B.soldB g G d U i _ β) x,
                           PE_buy G (B.soldB g G d U i _ β) x⟩)

lemma PE_fillEnd(x:Orbit N):
 parce (B.fillEnd g d U x) ≤ nod a p*(8*torsade a E c u l):=
   (PE_surplus u (fun i w=>farF g (B.streamer d U i w) x) (w:=nod a p*torsade a E c u l)
    (fun i=>⟨PE_buy G (B.soldL g G d U i _) x,
                           PE_buy G (B.soldL g G d U i _) x⟩)).trans_eq (mul_left_comm ..)


omit G in lemma weighing (A M:OP N){y z:ℝ}(t:parce A≤y)(r:parce M≤z):
 ‖weight d A M‖ ≤ y+2*z:=by
 rw [weight,two_mul,←add_assoc]
 refine (norm_add_le ..).trans (add_le_add ?_ ((PE_dg _).trans r))
 rw [norm_smul,norm_one,mul_one]
 exact (PE_tack ..).trans (add_le_add t r)

lemma PE_alarm(x:Orbit N):
 ‖B.alarm g d U x‖ ≤ Lint a E c u l:=
 weighing d _ _ (PE_buy G (B.soldA g G d U false) x) (B.PE_fill g G d U false x)
lemma PE_villa(x:Orbit N):
 ‖B.villa g d U x‖ ≤ Lint a E c u l + 2*hemPrice u :=by
   let H:=weighing d _ _ (PE_buy G (B.soldA g G d U true) x) (B.PE_fill g G d U true x)
   exact (norm_sub_le _ _).trans (add_le_add H (PE_gable (flagAnchor d) u)) 
lemma PE_pen(x:Orbit N):
 ‖B.pen g d U x‖≤ valance a E c u l+3*(8*torsade a E c u l):=by
  have h:=PE_buy G (B.soldA g G d U true) x
  have t:=B.PE_fill g G d U true x
  unfold pen portico thread
  rw [show (3:ℝ)=1+2 by norm_num, add_mul,one_mul, ←add_assoc]
  refine (norm_add_le ..).trans (add_le_add ?_ ?_)
  · rw [norm_smul,norm_one,mul_one]
    exact (PE_tack ..).trans (add_le_add h t)

  rw [touchP]
  exact (PE_serf ..).trans (by gcongr) 
lemma PE_quarry(x:Orbit N):
 ‖B.quarry g d U x‖ ≤ nod a p*Lint a E c u l:=
   (weighing d _ _ (PE_buy G (B.soldT g G d U) x) (B.PE_fillEnd g G d U x)).trans_eq (by rw [Lint];ring)

/-- Exact passing conditions. On lit consult replace each ping by disjoint from D. -/
def Sate (p:BudgetPoint)(u:Side)(d:Shape)(x:Orbit N):Prop:=
 pingS p.threshold (hoop (flagAnchor d) p.B) x.1 ∧
  ∀i,pingS p.threshold (hoop (crossAnchor d (advancePlus u i)) p.B) x.1 ∧
      pingS p.threshold (hoop (crossAnchor d (advanceNeg u i)) p.B) x.1
omit G
lemma quiet (x:Orbit N)(w:Sate p u d x):B.alarm g d U x=0:=by
  have t:B.trim g d U false x=0:= by simp [trim,coinF,silkcut,retina,
     w.1] -- maybe flagAnchor defeq
  have m:B.fill g d U false x=0:=by
    unfold fill surplus; apply Finset.sum_eq_zero; intro i _
    obtain ⟨z,n⟩:=w.2 i
    unfold crossAnchor at z n
    simp only [coinF,silkcut,retina,z,n,if_true,Bool.true_eq_false, if_false,sub_self]
  simp only [alarm,m,t,weight,tackfee,dg_zero,effect,ditch,Matrix.trace_zero,
   neg_zero,ite_self,zero_smul,add_zero]

#print axioms PE_quarry

