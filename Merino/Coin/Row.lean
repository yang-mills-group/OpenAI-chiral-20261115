import Merino.Coin.Shelf
import Merino.Brooch.Revenue

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Coin
open Function Finset Lattice Cube RG Scree Skye Fock
open scoped Topology Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Py Roots QuadClock Oise Mew Neon Waxy
open Vow TreasuryFog Dial Paige Vault
open scoped YM.CF.Mew
open NormedSpace Spire Stax Tulip
attribute [local instance] opCStarAlgebra
open Py Rate LocalLimit Preparation Yoke
open Next SectorNext.Remainder Graph
open Buffered Afterglow Vale Pressure Pressure.Worth Journey Scales
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable {I:Type}[Fintype I][LinearOrder I] {n:Side}
open MeasureTheory Papyrus Papyrus.Franc
open scoped InnerProductSpace

open Brooch

open Filter
def button(f: BProof.Obs n):Mark n:= fun x=> f x.1
def row (x:I→BProof.Obs n)(l:List I):Mark n:=(l.map fun i=>button (x i)).prod

lemma buttonEnv {f:BProof.Obs n}(e:Envelope f):Envelope (button f):=by
 obtain ⟨p,t,v⟩:=e
 exact ⟨p.comp measurable_fst,t,fun x=>v _⟩
lemma rowEnv (x:I→BProof.Obs n)(e:∀i,Envelope (x i))(l:List I):
 Envelope (row x l):=by
 induction l with
 | nil=> exact ⟨measurable_const,_,fun _=> le_rfl (a:=‖(1:FC (Single n))‖)⟩
 | cons a l ih=> exact Girt.kitE (button (x a)) (row x l) (·*·) (by fun_prop) (buttonEnv (e a)) ih
lemma row_eval (x:I→BProof.Obs n)(l:List I)(v:Fields n):
 row x l v=(l.map fun i=>x i v.1).prod:=by
 induction l with
 | nil=>rfl
 | cons a l ih=> exact congrArg (x a v.1 * ·) ih


variable (s i k:ℕ)
local notation "L"=> P.R.L
local notation "Ω"=> side Y i s
local notation "G0"=> RootBook Y i k s
local notation "K0"=> (Y.voyage i).CapeT s
local notation "A"=> P.U

/-- signed integrand for a word -/
abbrev actual (X:Mark Ω)(v:Orbit Ω) := letterRead (X (v.1,K0 v)) (denZ G0 A K0 v)

lemma roziInt (X:Mark Ω)(e:Envelope X)
  (v:Integrable (denZ G0 A K0) (city Ω)):Integrable (actual Y s i k X) (city Ω):=by
  have h:Measurable K0:=((Y.voyage i).ownership s).paid.bill
  obtain ⟨j,x,p⟩:=e
  exact Marks.read_int (fun v=> X (v.1,K0 v)) v ⟨j.comp (measurable_fst.prodMk h),x,fun _=> p _⟩

-- Any fleet reading via powered pressure.
structure Coffer (b:ℝ)(u:ℕ):Prop where
 gate:0<b
 bid:b≤1
 high:8≤ (G0).p.B
 desc:(G0).p.supportExponent=1
 grace:Nice_B (G0).p.B u (2*b⁻¹) (1/8)
 slip:wish_E (G0).p.B (Corolla.wovenV b u) ≤ slotFee P s

 fog:wish_E (G0).p.B b ≤ slotFee P s
 health:Rue.IsleB SU.group (G0).p.threshold
 fridge:Integrable (denZ G0 A K0) (city Ω)
 proper:∀v,IsStarProjection (spar P.K.j (G0).J.M (K0 v))
 shade:∃ c,ShelterCost c Y s i k

variable {u r:ℕ}{b e f:ℝ}{g:Side}

open Push.SectorMeasure


/--
Take a Fall on the Roster and receive the pressure price of each
fresh word. Same input marked arrays responsible for every bound
inside this estimate; dropping to sparse replacement here buys
as much even on the large Cauchy contour.
-/
theorem checks
 (h:Coffer Y s i k b u)(o:I→Site Ω)(X:I→BProof.Obs Ω)
 (v:Force_M (G0).p.B (node∘o) u)
 (x:Fall A G0 K0 o r P.h e f X g b u)
 (l:List I)(w:ψS (node∘o) l):
 ‖Journey.compass Y i k s (row X l)‖≤
 aroma P b s (Ω) (Fintype.card I) l.length:=by
 obtain ⟨T,G,D,F,a,d,z⟩:=x.cloth
 have he:=h.gate
 have hw:fuelled Y s i k b (reduce o D) (reduceK o F):=by
    unfold fuelled
    refine feasting (q:=Corolla.wovenV b u) (Y:=fun _=>0) d.plans
      (zero_lt_one.trans_le P.height) h.desc
      (fun i hi=> d.lease i (fun j=> (hill_i.mp hi j).trans one_le_two))
      v d.label ?_ h.grace h.high ?_ he.le h.slip h.fog ?_
    · nlinarith only [one_le_inv₀ he |>.mpr h.bid]
    · unfold Corolla.wovenV; positivity
    rw [mul_assoc,inv_mul_cancel₀ he.ne',mul_one]
 let y:=row X l
 let dd(j):=beamZ (Ω)
       (tipI (serum A G0 K0 (reduce o D) (reduceK o F) j) l)



 have ho:actual Y s i k y =ᵐ[city _] dd:=by
   have p0:∀ᵐ t:Orbit Ω∂city _,Rue.FleetS (G0).p.threshold t.1:=
    (Measure.quasiMeasurePreserving_fst (μ:=Wilson.prior SU.group (More _)) (ν:=depot _)).ae (h.health _)
   have p1:∀ᵐ t:Orbit Ω∂city _,Injective (priorP t.2):=
    (Measure.quasiMeasurePreserving_snd (μ:=Wilson.prior SU.group (More _)) (ν:=depot _)).ae sepT
   filter_upwards [p0,p1] with t h0 h1
   unfold dd actual y
   rw [blush (F:=F) (D:=D) A G0 K0 t (h.proper t) o d.plans l w,row_eval]
   exact (z t h0 h1 l w).symm

 have hI := (roziInt Y s i k y (rowEnv X (fun i=>(a i).badge.bounded) l) h.fridge).congr ho
 obtain ⟨_,S⟩:=h.shade
 change ‖(∫ t,actual Y s i k y t ∂city _) / coined Y i k s‖≤_
 rw [integral_congr_ae ho]
 exact invoice Y s i k S he h.bid _ _ hw o (news d.plans) l hI
end YM.CF.Merino.Coin

