import YM.SU5.FiniteGaugeData.Trigonal.Plush
import YM.SU5.FiniteGaugeData.Lycan.Joy
import YM.SU5.FiniteGaugeData.CodaT.SummitB
import YM.SU5.FiniteGaugeData.CodaT.Swirl
/-! # Color-specific tilted contract. Arbitrary many-body. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
noncomputable abbrev projCard(n:ℕ):= Fintype.card (SU.Slot × Fin n)
noncomputable def collar(n:ℕ):Fin (projCard n)≃ SU.Slot × Fin n:=(Fintype.equivFin _).symm
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
abbrev quantum(N:Side){b:Bool}(i:Trigo.Chamber b)(p:SU.Slot):= basisC N i.1 i.2.val p
variable (f:Fin n→Trigo.Chamber true)(g':Fin n→Trigo.Chamber false)
abbrev Umo (N:Side)(j:Fin (projCard n)):= create (quantum N (f (collar n j).2) (collar n j).1)
abbrev Bmo (N:Side)(j:Fin (projCard n)):= Fock.remove (quantum N (g' (collar n j).2) (collar n j).1)
abbrev TextK(N:Side):= Plush.Tile (Umo f N) (Bmo g' N)
def Torte(K':Calibration): Buffered.Family K':= fun i u=> TextK f g' (K'.c i)
local notation "🟢"=> Trigo.Chamber true
variable {N:Side}
local notation "Z"=> quantum N
local notation "C"=> Umo f N
local notation "B₀"=> Bmo g' N
lemma highZ(i:Trigo.Chamber true)(p:SU.Slot): Lifted.index N i.1 i.2.val p∈ Tset N:= (grade_one ..).2 (by simpa [Trigo.Spins] using i.2.property)
lemma lowZ(i:Trigo.Chamber false)(p:SU.Slot): Lifted.index N i.1 i.2.val p∉ Tset N:= fun v=> (show i.2.val∉ plusHalf from mem_compl.mp i.2.property) ((grade_one ..).1 v)
lemma crossz(i:Trigo.Chamber true)(p:SU.Slot)(j:Trigo.Chamber false)(q:SU.Slot):inner ℂ (quantum N j q) (quantum N i p)=0:=by
 unfold quantum basisC; rw [inner_smul_left,inner_smul_right,basis_inner,basis_apply,if_neg (show Lifted.index N j.1 j.2.val q≠ Lifted.index N i.1 i.2.val p from fun v=> lowZ j q (v.symm ▸ highZ i p)),mul_zero,mul_zero] -- choose
lemma buzz: Plush.Cross (Umo f N) (Bmo g' N):=fun i j=> by unfold Umo Bmo; rw [antiB_comm, antiB,car,crossz,zero_smul]
lemma mojo: Plush.Cross (Umo f N) (Umo f N):= fun i j=> car_create ..
lemma djinn: Plush.Cross (Bmo g' N) (Bmo g' N):= fun i j=> eq_neg_iff_add_eq_zero.mp (Lycan.low_slide ..)
-- G action. full carrier, in any calendar including uncompared small phases.
lemma wheel_fe (G:Seat N→ SU.E) (x:Cover)(i:SpinIdx)(b:SU.Slot): acts (tradew N G).val (basisC N x i b)=∑ j:SU.Slot,(SU.matter (G (node (wrap N x)))).val j b • basisC N x i j:= by
  have he (x:Site N×SpinIdx):
      acts (tradew N G).val (basisKet (x,b))=∑ j:SU.Slot,(matter (G (node x.1))).val j b • basisKet (x,j):=by
    apply PiLp.ext; rintro ⟨y,c⟩; rw [basis_act]; simp only [WithLp.ofLp_sum,Finset.sum_apply,basis_apply,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul,mul_ite,mul_one,mul_zero]; rw [sum_eq_single c]; swap; · intro k _ e; rw [if_neg (fun w=>e (Prod.mk.inj w).2.symm)]
    swap; · simp
    change jump (Equiv.refl _) (fun p : Site N × SpinIdx=> (matter (G (node p.1))).val) (y,c) (x,b)=_; rw [jump_apply]; simp only [Equiv.refl_apply,Prod.mk.injEq,and_true]; split_ifs with h; · rw [h]
    rfl
  unfold basisC; rw [map_smul]; unfold Lifted.index; rw [he,smul_sum]; exact sum_congr rfl fun j _=>smul_comm ..
variable (G: Seat N→ SU.E)
def arcMo {b:Bool}(f:Fin n→Trigo.Chamber b)(p:Seat N→SU.E)(i:Fin n): Op SU.Slot:=(matter (p (node (wrap N (f i).1)))).val
noncomputable abbrev Cuter (A:Fin n→Op SU.Slot): Op (Fin (projCard n)) := (Matrix.blockDiagonal A).submatrix (collar n) (collar n)
private lemma bloque (A:Fin n→Op SU.Slot)(x:Fin n→SU.Slot→FC (Single N))(y:Δ): Reform (fun i:Δ=>x (collar n i).2 (collar n i).1) (Cuter A) y = ∑ j:SU.Slot,A (collar n y).2 (collar n y).1 j • x (collar n y).2 j:=by
 let k:= (collar n y); unfold Reform Cuter; rw [← Equiv.sum_comp (collar n).symm]; simp_rw [Matrix.submatrix_apply,Equiv.apply_symm_apply]; change ∑ x':Υ n,(Matrix.blockDiagonal A) k x' • _=_; rw [Fintype.sum_prod_type]; refine sum_congr rfl (fun s _=>?_); rw [sum_eq_single k.2]; · simp [Matrix.blockDiagonal_apply,k]
 · intro i _ l; rw [Matrix.blockDiagonal_apply]; simp [l,Ne.symm l]
 exact fun t=>(t (mem_univ _)).elim
lemma HBlade: (fun i=> twist (quantU (tradew N G)) ((Umo f N) i))= Reform (Umo f N) (Cuter fun i=> (arcMo f G i)ᵀ):=by
 funext y; rw [Umo,twist_create]; unfold quantum; rw [wheel_fe]; simp_rw [map_sum,map_smul]; exact (bloque (fun i=> (arcMo f G i)ᵀ) (fun i s=> create (quantum N (f i) s)) y).symm
lemma HBladeD: (fun i=> twist (quantU (tradew N G)) ((Bmo g' N) i))= Reform (Bmo g' N) (Cuter fun i=> star (arcMo g' G i)):=by
 funext y; rw [Bmo,twist_remove]; unfold quantum Fock.remove; rw [wheel_fe]; simp_rw [map_sum,map_smul,star_sum, star_smul]; exact (bloque (fun i=>star (arcMo g' G i)) (fun i s=> Fock.remove (quantum N (g' i) s)) y).symm
lemma arc_det {N:Side}(G:Seat N→ SU.E){b:Bool}(f:Fin n→Trigo.Chamber b)(i:Fin n):(arcMo f G i).det=1:=triple_det _
lemma inscribed : twist (quantU (tradew N G)) (TextK f g' N)= TextK f g' N:=by
 let L:=Cuter (fun i=>(arcMo f G i)ᵀ); let M:=Cuter (fun i=>star (arcMo g' G i)); have he:L.det =1:=by unfold L Cuter; rw [Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]; simp_rw [Matrix.det_transpose,arc_det,prod_const_one] -- tune
 have hp:M.det=1:=by unfold M Cuter; rw [Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]; simp_rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose,arc_det,star_one,prod_const_one]
 let t:= twist (quantU (tradew N G)); rw [show t (TextK f g' N)= Plush.Tile (Reform (Umo f N) L) (Reform (Bmo g' N) M) from ?_, Plush.Museum (Umo f N) (Bmo g' N) L M (mojo f) (djinn g') (buzz f g'), he,hp,mul_one,one_smul] -- t rw original transparency
 unfold TextK Plush.Tile rollF; rw [←HBlade,←HBladeD,map_list_prod];  unfold t; simp only  [List.map_ofFn,Function.comp_def,map_mul]; -- `unfold t`.Tune
#print axioms inscribed
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
