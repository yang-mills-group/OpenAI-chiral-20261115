import YM.SU5.Registration.Rise.PadTransfer
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set TopologicalSpace Metric


/-!
# Even when we don't send the root

`P.stageH A` exactly from any finer issuance in a centered rectangle. This is
ALL weighted, on unprojected; also use for jets and fusing.
-/
variable (P: Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "H"=> P.ColorHil j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "S"=>P.physicalEnergy j x
local notation "T"=>timeMesh P.par
local notation "M" s:max n:max=> whenly T s n
variable (A:P.Apron)(s w:ℕ) (p:A.s≤ s)
local notation "a"=> A.zoom P s j
local notation "d"=> A.allowance P j
local notation "X'" w:max=> P.shifts j ((w:ℕ):ℤ) (A.full P s)


-- know `color` at every mark visited
include p
lemma Apron.anchored : P.InCase j s (a+a) (X' a) :=by
 obtain ⟨g,h,v⟩:= A.full_realizes P j s p; exact ⟨P.shifts_keep j _ (A.fullColor P s),g,h⟩
lemma Apron.retains : (A.anchored P j s p).charges x (add_pos (A.zoomP P j s) (A.zoomP P j s))=A.engine P j x:=by
 let v:= A.anchored P j s p; let g:= A.zoomP P j s; let hw:=add_pos g g
 obtain ⟨b,c,e⟩:= A.full_realizes P j s p; 
 let f:=P.door j A.s _ (add_pos (A.pos j) (A.pos j)) (A.cardB P j) (A.color P j)
 refine congrArg (fun u:P.Physical j=> P.colorSpace j x u) (show v.rations hw=f from ?_)
 rw [v.cases_eq_door hw b c]; exact Subtype.ext e.symm
lemma Apron.entrusted (t w:ℕ)(h:t≥A.zoom P s j)(e:A.zoom P s j≤w): P.InCase j s (t+w) (X' t) := by
 let v:= A.anchored P j s p; have g:= v.padIn (t-a) (w-a)
 rw [show (t-a)+(a+a)+(w-a)=t+w from by omega,P.shifts_sum,show (((t-a:ℕ):ℤ)+((a:ℕ):ℤ))=(t:ℤ) from by omega] at g; exact g
lemma zoomMoney : M s a=d:=matchR T A.s s (A.u j) p -- explicit proof p maybe
lemma Apron.entrusted_pays (l r:ℕ)(h:A.zoom P s j ≤ l)(g:A.zoom P s j ≤ r)(v:0<l+r): (A.entrusted P j s p l r h g).charges x v=P.stageH j x A (M s l) (M s r):= by
 let f:= A.anchored P j s p; let C₁:=A.entrusted P j s p l r h g; let l':=l-a; let r':=r-a; let V:=A.zoomP P j s; let T':= add_pos V V
 have hh:l+r=l'+(a+a)+r':= by unfold l' r'; omega
 have hx:P.shifts j l' (X' a)=X' l:=by rw [P.shifts_sum,show ((l':ℕ):ℤ)+((a:ℕ):ℤ)=(l:ℤ) from by unfold l'; omega]
 let f':= f.padIn l' r'
 refine (C₁.charges_eq x f' rfl hh hx.symm v).trans ((f.charges_pad x l' r' T').trans ?_)
 have hz(z:ℕ)(p':A.zoom P s j≤ z): M s (z-a)=M s z - (d) := by
    have he:(M s (z-a))+ d=M s z:=by rw [← P.zoomMoney j A s p,← when_add,tsub_add_cancel_of_le p']; -- need binder h
    rw [←he,add_tsub_cancel_right]
 unfold stageH; rw [show f.charges x _ = _ from A.retains P j x s p,hz _ h,hz _ g]
lemma Apron.consumes (l' r':ℕ){Z:P.Test}(x':P.InCase j s (l'+r') Z)(pL:A.zoom P s j≤l')(pR:A.zoom P s j≤r')(u:0<l'+r')(e:Z=X' l') : x'.charges x u=P.stageH j x A (M s l') (M s r'):=
 (InCase.charges_eq x' x (A.entrusted P j s p l' r' pL pR) rfl rfl e u).trans (A.entrusted_pays P j x s p l' r' pL pR u)

section summing
omit p
-- sum helpers: token charges scale, sum at width v; y argument explicit
variable {ι:Type*}
lemma InCase.collect (w:ℕ)(f:ι→P.Test)(Y:ι→(P.ColorHil j x).Op)(F:Finset ι)(g:0<w)(q:∀ i∈F,∃ u:P.InCase j s w (f i), u.charges x g=Y i) : ∃ u:P.InCase j s w (∑ i∈ F, f i), u.charges x g=∑ i∈F,Y i :=by
 classical
 induction F using Finset.induction_on with
 | empty=> -- zeros
    simp only [sum_empty]; exact ⟨InCase.zeros P j s w, (congrArg (P.colorSpace j x) (InCase.rations_zero (s:=s) g)).trans (map_zero _)⟩ -- implicit? 
 | @insert i F v ih=> obtain ⟨u,p'⟩:=ih (fun i h=> q _ (mem_insert_of_mem h)); obtain ⟨V,T'⟩:= q i (mem_insert_self ..); simp only [sum_insert v]; exact ⟨V.append u,by rw [V.charges_add x u,T',p']⟩
end summing
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Apron.consumes
#print axioms Spine.InCase.collect
