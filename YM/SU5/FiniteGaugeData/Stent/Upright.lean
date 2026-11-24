import YM.SU5.FiniteGaugeData.Stent.Ream
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
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
variable {N P: Side}(R:Patch)
local notation "ℱ"=> FC (Single N)
abbrev rayW : Finset Cover:= {nodeC 0}
abbrev reamW(R:Patch)(d:ℕ) := Satin.liner (rayW.image (fun a=> R.L.val • a)) (clothRadius R.L d)
abbrev starlit (t:Cover):X:= (t,⟨0,by decide⟩)
abbrev reedW (t:Cover):Y₀:=(t,⟨2,by decide⟩)
local notation "η"=> specialM R.L
variable (G:Ratio N P)(p:G.count=R.L)(h:4≤R.L.val){d:ℕ} (q:LaurentRadius R.J G.count d) (t:2*d < N.val) (e:Odd G.count.val)
variable (Q:Op SU.Slot)(M:Male)(u':Nom N P)
abbrev Warp (x:Cover)(K:Calibration): W K:= Base (roseone (starlit x)) (roseone (reedW x)) K
abbrev Whip (N:Side)(x:Cover): FC (Single N):= TextK (roseone (starlit x)) (roseone (reedW x)) N
abbrev QuestU (Q:Op SU.Slot)(b:SU.Slot):= byMode G R.J Q M u' true (quantum N (starlit 0) b)
abbrev QuestL (Q:Op SU.Slot)(b:SU.Slot):= byMode G R.J Q M u' false (quantum N (reedW 0) b)
-- note parameter order from lean; section R then G M u' BEFORE Q.
local notation "A"=> QuestU R G M u' Q
local notation "B"=> QuestL R G M u' Q
local notation "K"=> subF G R.J Q M e u'
local notation "c₁" i:max => (collar 1 i).1
include e
lemma weightU(b:SU.Slot):withinM (Tset P) (QuestU R G M u' Q b):= carried_up G R.J Q M e u' _ (wageH _ _)
lemma weightL(b:SU.Slot):withinM (Tset P)ᶜ (QuestL R G M u' Q b):= carried_down G R.J Q M e u' _ (wageL _ _)
include p q
private lemma windowQ : padded G (region rayW N) (clothRadius G.count d) ⊆ region (reamW R d) P:=by unfold reamW; rw [←p]; exact Satin.next_contains .. -- `rw ←p` dependent? in reamF,D.R.'
lemma areaU (b:SU.Slot) : withinM (modesIn P (region (reamW R d) P)) (QuestU R G M u' Q b):= (within_test ..).mpr fun i v=> (within_test ..).1 (mode_support G R.J Q M e _ q (z:=u') (show withinM (modesIn N (region rayW N)) (quantum N (starlit 0) b) from costO _ _ (mem_singleton.mpr rfl)) true) i (mt ((modes_monotone (windowQ R G p q e)) · ) v)
lemma areaL (b:SU.Slot) : withinM (modesIn P (region (reamW R d) P)) (QuestL R G M u' Q b):= (within_test ..).mpr fun i v=> (within_test ..).1 (mode_support G R.J Q M e _ q (z:=u') (show withinM (modesIn N (region rayW N)) (quantum N (reedW 0) b) from costO _ _ (mem_singleton.mpr rfl)) false) i (mt ((modes_monotone (windowQ R G p q e)) · ) v)
omit p q
private lemma plume (f:Fin n→ FC (Single N))(v:∀ i,f i∈TF N false): K (rollF f)=rollF (K ∘ f) := by
 induction n with
 | zero=> simp only [rollF,List.ofFn_zero,List.prod_nil,sub_one]
 | succ n ih=>
     unfold rollF; rw [List.ofFn_succ,List.ofFn_succ,List.prod_cons,List.prod_cons]; let g:= f ∘ Fin.succ; change K (f 0* rollF g)= _; rw [sub_mul _ _ _ _ _ _ (show Fine .. from v 0) (show Fine .. from Tprod g (fun i=> v i.succ)),ih g]; · rfl
                                                                                                    -- indentation likely issue
     exact fun i=> v i.succ -- better change
lemma shorn : K (Whip N 0)= Tile (fun i:Fin (projCard 1)=> create (A (c₁ i))) (fun i=>Fock.remove (B (c₁ i))):=by
 let f:= Umo (roseone (starlit 0)) N; let g:= Bmo (roseone (reedW 0)) N; change K (rollF (fun i=>f i*g i))=_; rw [plume R G e Q M u' _ (fun i=> BlendP ..)]; apply congrArg rollF; funext i; change K (create (quantum N (starlit 0) _)* Fock.remove (quantum N (reedW 0) _))= _; let b:SU.Slot:=c₁ i
 rw [sub_mul _ _ _ _ _ _ (show Fine _ _ true _ from Upper (N:=N) (starlit 0) b) (show Fine _ _ true _ from Lower (N:=N) (reedW 0) b), sub_create _ _ _ _ _ _ (wageH ..), sub_remove _ _ _ _ _ _ (wageL ..)] -- variables tune. maybe `change` terms.
#print axioms shorn
section
omit e
lemma scaleOne (P:Op SU.Slot)(x:SU.Slot→FC (Single N))(y:Fin (projCard 1)) : Reform (fun i:Fin (projCard 1)=> x (c₁ i)) (Cuter (roseone P)) y =∑ j:SU.Slot,P (c₁ y) j • x j:=by
 let k:= collar 1 y; unfold Reform Cuter; rw [←Equiv.sum_comp (collar 1).symm]; simp_rw [Matrix.submatrix_apply,Equiv.apply_symm_apply]; change ∑ i:SU.Slot × Fin 1, (Matrix.blockDiagonal (roseone P)) k i • _=_; rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_one]; refine sum_congr rfl (fun x hx=>?_); rw [Matrix.blockDiagonal_apply,if_pos (by subsingleton)]
-- transport det factor including phase. no infinite convergence of Q yet . transfer later.
local notation "z"=> Lifted.winding N 0 / Lifted.winding P (specialM R.L)
abbrev driftW (R:Patch)(N P:Side):ℂ:= Lifted.winding N 0 / Lifted.winding P (specialM R.L)
lemma driftN : driftW R N P*star (driftW R N P)=1:=by
 have he:‖z‖=1:=by rw [norm_div,RollSelf,RollSelf,div_self one_ne_zero]; -- fine
 unfold driftW; rw [Complex.star_def,Complex.mul_conj,← Complex.sq_norm, he, one_pow, Complex.ofReal_one] -- tune lean
noncomputable abbrev Tiller (b:Bool)(i:SpinIdx)(W:LinksC):= IssueP R Q b i W
abbrev portionA(N P:Side)(R:Patch)(Q:Op SU.Slot)(W:LinksC): Op (Fin (projCard 1)):= Cuter (roseone (driftW R N P • IssueP R Q true 0 W)ᵀ)
abbrev portionB(N P:Side)(R:Patch)(Q:Op SU.Slot)(W:LinksC):Op (Fin (projCard 1)):= Cuter (roseone (star (driftW R N P • IssueP R Q false 2 W)))
-- monetary factor
noncomputable def PaceLock(R:Patch)(Q:Op SU.Slot):ℂ:= (Bliss R^ (Fintype.card SU.Slot)*(Lock Q true 0).det) * star (Bliss R^ (Fintype.card SU.Slot)*(Lock Q false 2).det)
noncomputable def Nylon(R:Patch)(W:LinksC):ℂ:=(Louvre R W).det * star (Louvre R W).det
private lemma landscapeφ (p q a b c d u v:ℂ): p*(a*(u*c))*(d*v*b*q)=(p*q)*(a*c*(d*b))*(u*v):=by ring

lemma pacezone (W:LinksC): (portionA N P R Q W).det * (portionB N P R Q W).det =PaceLock R Q * Nylon R W:=by
 unfold portionA portionB Cuter PaceLock Nylon roseone IssueP; simp_rw [Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal,Fin.prod_univ_one, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_smul, Matrix.det_mul,star_mul,star_pow];
 let n:=Fintype.card SU.Slot; let k:= (Louvre R W).det ; let d:ℂ:= Bliss R; let φ:ℂ:=driftW R N P; let u:ℂ:= (Lock Q true 0).det; let v:= (Lock Q false 2).det
 have ht:φ^n*star φ^n=1:=by rw [←mul_pow, driftN,one_pow]
 calc
  _=(φ^n*star φ^n)*(d^n*u*(star v* star d^n))*(k* star k):=by exact landscapeφ (φ^n) (star φ^n) (d^n) (star d^n) u (star v) k (star k)
  _=_:=by rw [ht,one_mul]
#print axioms pacezone
end
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
