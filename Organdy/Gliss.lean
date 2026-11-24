import Organdy.Ice
import Organdy.Captain
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU Tulip Lat
open Vale Buffered
open NormedSpace
open Swell Hom

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine) (i k t:ℕ)
local notation "Λ"=>P.par
local notation "x'"=> Vale.hat (Λ).R.L (Λ).x t
local notation "N'"=> age P.run i t
local notation "KL"=> (P.run.voyage i).CapeT t
local notation "R✤"=>RootBook P.run i k t
local notation "p'" => (R✤).p
local notation "q'" => (Λ).J.n
local notation "h'" => (Λ).h

variable (s:Sweep (age P.run i t))
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single N'
local notation "Fz"=> FC (Dwell N')
local notation "⚓"=> Spire.arum T B₁ D₁ (mateK N')
local notation "θ"=> sailQ B₁ D₁ T
local notation "ι₁"=> suit_Y s


structure Holidays (P:Spine)(i k t:ℕ):Prop where
 era:t≤P.run.uv k
 interest: Hom.InterestX P.par.W.C (age P.run i t) (RootBook P.run i k t).J
 fares: ∃ a b,IncX (fun _=>True) (RootBook P.run i k t).F (RootBook P.run i k t).p P.par.h a ∧
        Dark (fun _=>True) (RootBook P.run i k t).K (RootBook P.run i k t).p P.par.h b
 pureF: (RootBook P.run i k t).slip=0
lemma floats (q:t≤ P.run.uv k): Holidays P i k t:=by
 let F:=(P.run.voyage i).X (P.run.uv k)
 let XP:=F.pull
 have h:=XP.note t q
 have e:Hom.InterestX (Λ).W.C N' (R✤).J:= (XP.owns t q).taste ▸ (((Λ).W.arm ..).sound t)
 exact ⟨q,e,⟨_,_, h.buoy,h.nite⟩,h.tone⟩ -- nesting issue

variable (u:Holidays P i k t)(v:Orbit (age P.run i t))
variable (q:Injective (priorP v.2))
local notation "D₀"=> (projects_here P.run i k t v).1
local notation "v'"=> yellA s v
local notation "D₀'" => (projects_here P.run i k t v').1
local notation "πP" => spar (Λ).K.j (R✤).J.M
include q
lemma raiseTurn: (KL) v'=flashA s ((KL) v):=
 ((P.run.voyage i).ownership t).paid.move _ _ s q -- include

local notation "L₀"=>relV (Λ).U (R✤).J
include u in
lemma raiseSea : sings B₁ T (πP (KL v))=swapX D₁ (πP (KL v')) ∧
    ⚓ (L₀ (KL v))=L₀ (KL v'):=by
 rw [raiseTurn P i t s v q]
 let w:=castX s
 let z:=KL v
 let j:= spinU B₁ s.s
 have ht:JetS w.s B₁ (detX w.s) j:=spinZ ..
 have a:Guard z (Λ).d:=(((P.run.voyage i).ownership t).paid.paid v).shrink (Λ).J.hr.le
 have he:= (Λ).J.gran.trans ((P.run.voyage i).ownership t).size
 have b:1≤ (Λ).K.j:=by rw [(Λ).kJ];decide
 exact ⟨funde_f w (xtra _) j ht z _ b _ _ ((Λ).V.note.fields_one _ ((Λ).U.needed.trans he)) (a.shrink (Λ).U.gem),
       Hive.birds B₁ (Λ).W.pearl (Λ).V.note he b w j ht (R✤).J.P u.interest.leanJ.1 u.interest.ready z a⟩
omit q

abbrev Lcoat (z:Orbit N') : Cipher N' := exp (exponentL (R✤).p (R✤).F z.1+exponentL (R✤).p (R✤).slip z.1)
include u
lemma raisesCloth: Lcoat P i k t v'= ι₁ (Lcoat P i k t v):=by
  obtain ⟨a,d,e,_⟩:=u.fares
  have f: IncX (fun _=>True) (R✤).slip (R✤).p (Λ).h 0:=by rw [u.pureF]; exact (Vale.lye ..).1
  letI : NormedAlgebra ℚ (Cipher N'):=NormedAlgebra.restrictScalars ℚ ℝ _
  rw [Lcoat,Lcoat,map_exp ι₁ ((ι₁).toLinearMap.continuous_of_finiteDimensional),map_add]
  exact congrArg exp (congrArg₂ (·+·)
   (Window.turn_exponent s e trivial (spinZ ..) v.1)
   (Window.turn_exponent s f trivial (spinZ ..) v.1))
omit u
abbrev barefoot (z:Orbit N') (x:Wave (Dwell N')):=
  ballL (nursery _ (projects_here P.run i k t z).1) (L₀ (KL z))
    (acts (Lcoat P i k t z).val x)
lemma covered (z:Orbit N') (x:Wave (Dwell N')):
    curtain P i k t z x = Complex.exp ((R✤).betaL KL z) • barefoot P i k t z x:=rfl

include u q
lemma liftsStage (x:Wave (Dwell N')):
  ⚓ (barefoot P i k t v x)=barefoot P i k t v' (θ x):=by
 obtain ⟨e,r⟩:=raiseSea P i k t s u v q
 have h:=ballMoves D₀ D₀' B₁ D₁ T e (mateK N') (L₀ (KL v)) (acts (Lcoat P i k t v).val x)
 rw [sail_move,r] at h
 unfold barefoot;rw [h,raisesCloth P i k t s u v]; rfl
omit q u
end YM.CF.Organdy
