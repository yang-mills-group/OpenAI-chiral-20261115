import GaugeFieldConstruction.Cabrio4
import GaugeFieldConstruction.TeazelQ
import GaugeFieldConstruction.SesameCq
import GaugeFieldConstruction.QuiffMQ
import GaugeFieldConstruction.PhonicsQ
import GaugeFieldConstruction.Barrera4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n:Side}
variable (e:I↪J)(σ:I→Seat n)(σ':J→Seat n)
open Same4
local notation "Δ"=> PaintEV e
variable (F:XE I (InkD n) n)(K:KK I (Copy n) n) (F':XE J (InkD n) n)(K':KK J (Copy n) n)
variable (S:List I)
local notation "S'"=> List.map e S
variable (l m:ℕ)(a:l=m)(p:Hub n)
variable (P:List I)(Q:List J)(s:I→List I)(s':J→List J)(T:I→Hub n)(T':J→Hub n)(μ:I→ℝ)(μ':J→ℝ)
variable (i:I)(h:i∈P)(k:e i∈ Q)(hP:P.Nodup)(hQ:Q.Nodup)(hv:s' (e i)=List.map e (s i))(hi:T i=T' (e i))(t:μ i=μ' (e i))
local notation "Η"=> (ProgramL σ F K μ s T P)
local notation "Γ"=> (ProgramL σ' F' K' μ' s' T' Q)
local notation "S_"=>(s i).toFinset
variable (pI:∀ j∈ P,j∉ s i) (pJ:∀ j∈ Q,j∉ s' (e i))
variable (r:SpiritRQ e F F' (s i).toFinset) (b:SpiritFQ e K K' (s i).toFinset)
include r h k hP hQ hv hi t pI pJ
private lemma windQR (L:List I)(u:L⊆P)(L':List J)(v:L'⊆ Q): SpiritRQ e (RX F (ProgramL σ F K μ s T L)) (RX F' (ProgramL σ' F' K' μ' s' T' L')) (s i).toFinset:=by
 rintro ⟨R,p⟩ W; change R⊆ _ at W
 let Y:= ProgramL σ F K μ s T L; let Y':= ProgramL σ' F' K' μ' s' T' L'; let R':=R.image e
 have ht: R'⊆ (s' (e i)).toFinset:= by rw [hv,show (List.map (⇑e) (s i)).toFinset=image (⇑e) (s i).toFinset from (by ext; simp)]; exact Finset.image_subset_image W
 change F' (R',p)+Y'.pureX (R',p)= F (R,p)+Y.pureX (R,p)
 rw [show Y.pureX (R,p)= _ from (show Y.pureX (R,p)=0 from (unchanged F K σ μ s T L R (fun j t x=>pI j (u t) (List.mem_toFinset.mp (W x)))).1 p), show Y'.pureX (R',p)=0 from (unchanged F' K' σ' μ' s' T' L' R' (fun j t x=>pJ j (v t) (List.mem_toFinset.mp (ht x)))).1 p,add_zero,add_zero]; exact r (R,p) W
lemma RiseVocQ (j:Hub n): (ProgramL σ F K μ s T P).pureX ({i},j)=(ProgramL σ' F' K' μ' s' T' Q).pureX ({e i},j):=by
 obtain ⟨L,c,d,q,u⟩:= PrevR F K σ μ s T P i h ({i},j) rfl hP; obtain ⟨L',c',d',q',v⟩:= PrevR F' K' σ' μ' s' T' Q (e i) k ({e i},j) rfl hQ
 rw [u,v]; simp only[insertΦ]; rw[κpClip, κpClip]; rw [Finset.sum_apply,Finset.sum_apply,← hi,← t,hv]
 apply Fintype.sum_equiv (finCongr (poetQ e (s i))); intro j'
 exact RiseBQ e σ σ' _ _ _ _ (s i) (T i) i (windQR e σ σ' F K F' K' P Q s s' T T' μ μ' i h k hP hQ hv hi t pI pJ r _ c _ c') _ _ (poet_b _ _ (List.get_mem ..)) _ (songQ e (s i) j') (μ i) j -- tune order
include b
lemma BeamVocQ (j:Force n): (ProgramL σ F K μ s T P).B ({i},j)=(ProgramL σ' F' K' μ' s' T' Q).B ({e i},j):=by
 obtain ⟨L,c,d,u⟩:= PrevF F K σ μ s T P i h ({i},j) rfl hP; obtain ⟨L',c',d',v⟩:= PrevF F' K' σ' μ' s' T' Q (e i) k ({e i},j) rfl hQ
 let A:= ProgramL σ F K μ s T L; let B:=ProgramL σ' F' K' μ' s' T' L'; let Z:=FrameT (RX F A) (BX K A); let Z':=FrameT (RX F' B) (BX K' B)
 have p0:SpiritFQ e (BX K A) (BX K' B) (s i).toFinset:=by
    rintro ⟨Y,Pp⟩ W; change Y⊆_ at W; let Y':=Y.image e
    have ht: Y'⊆ (s' (e i)).toFinset:= by rw [hv,show (List.map (⇑e) (s i)).toFinset=image (⇑e) (s i).toFinset from (by ext; simp)]; exact Finset.image_subset_image W
    change K' (Y',Pp)+B.B (Y',Pp)=K (Y,Pp)+A.B (Y,Pp); rw [show B.B (Y',Pp)=0 from (unchanged _ _ _ _ _ _ L' Y' (fun j v x=>pJ _ (c' v) (List.mem_toFinset.mp (ht x)))).2 _,show A.B (Y,Pp)=0 from (unchanged _ _ _ _ _ _ L Y (fun j v x=>pI _ (c v) (List.mem_toFinset.mp (W x)))).2 _,add_zero,add_zero]; exact b (Y,Pp) W
 rw[u,v]; change (∑ k:Isle.Path (s i),Kinc σ (Z.altuQ (T i) (s i) (μ i) i k)) ({i},j)=(∑ k:Isle.Path (s' (e i)),Kinc σ' (Z'.altuQ (T' (e i)) (s' (e i)) (μ' (e i)) (e i) k)) ({e i},j); -- rw hv dependent motive issue.
 rw[Finset.sum_apply,Finset.sum_apply,←hi, ← t]; rw [hv]
 apply Fintype.sum_equiv (finCongr (poetQ e (s i))); intro j'
 exact BeamKQ e σ σ' _ _ _ _ (s i) (T i) i (windQR e σ σ' F K F' K' P Q s s' T T' μ μ' i h k hP hQ hv hi t pI pJ r _ c _ c') p0 _ _ (poet_b _ _ (List.get_mem ..)) _ (songQ e (s i) j') (μ i) j
omit r b hi
open Ione QuadClock Salt
variable (R:Sweep n)(hT:T' (e i)=moveHub R (T i))(pR:∀ x:Finset I,x⊆(s i).toFinset→ passingR n R (fun j=> F (x,j)) (fun j=>F' ((x.image e),j)))(pF:∀ x:Finset I,x ⊆ (s i).toFinset→ passingF n R (fun j=>K (x,j)) (fun j=> K' (x.image e,j)))
include pR pF hT
lemma SonantQ : passingR n R (fun j=> (ProgramL σ F K μ s T P).pureX ({i},j)) (fun j=>(ProgramL σ' F' K' μ' s' T' Q).pureX ({e i},j))∧ passingF n R (fun j=>(ProgramL σ F K μ s T P).B ({i},j)) (fun j=> (ProgramL σ' F' K' μ' s' T' Q).B ({e i},j)):=by
 let F'':XE I (InkD n) n:= squeezeD e F'; let K'':KK I (Copy n) n:=squeezeD e K'; let σ₀:= σ' ∘ e; let T₀:= T' ∘ e; let Y:= ProgramL σ F K μ s T P; let C:= ProgramL σ₀ F'' K'' μ s T₀ P
 have u:= courier4 R F F'' K K'' σ σ₀ μ μ s s T T₀ P P i h h hP hP rfl rfl hT pI pI pR pF -- order
 let Z:=ProgramL σ' F' K' μ' s' T' Q
 change passingR n R (fun j=>Y.pureX ({i},j)) (fun j=> Z.pureX ({e i},j)) ∧ passingF n R (fun j=>Y.B ({i},j)) (fun j=>Z.B ({e i},j))
 rw [show (fun j:Hub n => Z.pureX ({e i},j))= (fun j=> C.pureX ({i},j)) from funext fun j=> (RiseVocQ e σ₀ σ' F'' K'' F' K' P Q s s' T₀ T' μ μ' i h k hP hQ hv rfl t pI pJ (fun i _=>rfl) j).symm,show (fun j:Force n=>Z.B ({e i},j))=(fun j=>C.B ({i},j)) from funext fun j=>(BeamVocQ e σ₀ σ' F'' K'' F' K' P Q s s' T₀ T' μ μ' i h k hP hQ hv rfl t pI pJ (fun i _=>rfl) (fun i _=>rfl) j).symm]
 exact u
#print axioms SonantQ
end Iona
end YM.CF.Scree.Ing
end
