import Bay.C.Rook
import YM.CF.Ione.Lark
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks


open Salt Hive SU

section
variable {m:Type*}[LinearOrder m][Fintype m]
lemma lot_star (b r:Bool)(U:UNI m)(x:FC (LeanV m)) : lotY b r U (star x)=star (lotY b r U x):= Sault.handL .. 
end
variable {N:Side}(s:Sweep N)
def chosen (g:Seat N→E):= ((polarT s.charge ∘g) ∘ (castX s).anon N)
local notation "LM"=>lotY s.charge (detX s.s) (siteU (castX s) s.charge (spinU s.charge s.s) N)
abbrev LD(t:Seat N→E):= lotY false false (tradew N t)
lemma pantry(t:Seat N→E)(i:Dwell N):
  LM (LD t (put i))= LD (chosen s t) (LM (put i)):=by
   obtain ⟨b,i⟩:=i
   unfold LD
   rw [Ione.honey,Ione.honey,tr_s]
   simp only [site_ui,Bool.false_xor,Bool.xor_false,whiten,Bool.false_eq_true,↓reduceIte,Nacre.envoy,chosen,feeJ,Bool.false_and,Bool.and_false]

lemma aim_t (t:Seat N→ E) {X:Support (More N)}{a:Bool}{A:FC (Dwell N)} (p: Sector (camp X) a A) : LM (LD t A)= LD (chosen s t) (LM A):=by
 unfold LD
 induction p with
 | zero=> simp only [map_zero]
 | one=> simp only [map_one]
 | up i _ => exact pantry s t i
 | down i _ => simp only [takeF,lot_star];exact congrArg star (pantry s t i)
 | add _ _ ih j => rw [map_add,map_add,map_add,map_add,ih,j]
 | mul _ _ ih j => rw [map_mul,map_mul,map_mul,map_mul,ih,j]
 | scale _ c j=> rw [G_lot,G_lot,G_lot,G_lot,j];rfl

lemma body_t (X:Support (More N))(i:Dwell N)(p:i∈camp X):
 Sector (camp (actY s X)) true (LM (put i)):=by
 rw [Urn.mold]; refine Sector.sumS _ _ ?_
 intro j _
 by_cases k:(praise s).val j i=0
 · rw [show sewV _ _ i j=0 from k,zero_smul]; exact Sector.zero _
 refine (Sector.up j ?_).scale _
 have v:(boxA s) (cod_A j)∈X:= (price_Q s j i k).symm ▸ (show cod_A i∈X from (Finset.mem_filter.mp p).2) 
 exact mem_filter.mpr ⟨mem_univ _,mem_map_equiv.mpr v⟩

lemma active_t {X:Support (More N)}{a:Bool}{A:FC (Dwell N)} (p: Sector (camp X) a A) :
 Sector (camp (actY s X)) a (LM A):=by
 induction p with
 | zero=>rw [map_zero]; exact Sector.zero _
 | one=>rw [map_one]; exact Sector.one
 | up i h=>exact body_t s X i h
 | down i h =>rw [takeF,lot_star]; exact (body_t s X i h).contr
 | add _ _ q v=>rw [map_add]; exact q.add v
 | mul _ _ q v=>rw [map_mul]; exact q.mul v
 | scale _ z q=> rw [G_lot]; exact q.scale _
