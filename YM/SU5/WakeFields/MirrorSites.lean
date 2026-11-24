import YM.SU5.WakeFields.CP2
--! purchasing the mirror stamps
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxRecDepth 2500
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.EmberWind
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Lifted Hiro
open Py.Rate.LocalLimit.Papal
open Afterglow Afterglow.Tower
open Afterglow.Tower.VacuumSelection
namespace Glare
variable (z:ℤ)(ρ:ℝ)(t:ℝ)
variable (n:Side)
local notation "λq" => ((3:Axis))
local notation "Ρ" => (plane (3:Axis) z)
-- adapted from Thin/Camp/Gated
section gauge
variable (g:Signed)(o b:Site n)
lemma spaceglow (u:ℕ) : (halo u {o}).image (affine g b)=halo u {affine g b o}:=by
 let f:=affine g b; have ht:Injective f:=fun i j p=> g.act_injective (add_right_cancel p)
 ext i; obtain ⟨j,rfl⟩:= (Finite.injective_iff_surjective.mp ht) i
 have hp : f j ∈ (halo u {o}).image f ↔ j∈halo u {o}:=by simp [ht.eq_iff]
 change _ ↔ f j∈_; rw [hp]; simp only [halo_spec,mem_singleton,exists_eq_left]; simp [f,affine]
lemma wingbright (u:ℕ)(X:Config SU.group n) : pingS t (halo u {o}) (Lattice.pull g b X) ↔ pingS t (halo u {affine g b o}) X:=by
 let f:= affine g b; have ht: Injective f:=fun i j p=> g.act_injective (add_right_cancel p)
 rw [←spaceglow]; have hq(i:Face (Per n)):= Face.send_price X i g b SU.group.chord SU.group.chord_inv fun k G=> SU.group.chord_conj G k
 constructor
 · intro p i v; obtain ⟨i,rfl⟩:= (Finite.injective_iff_surjective.mp (Face.injective_send g b)) i; exact (hq i) ▸ p i (fun j=> v (by rw [Work.H03.touched_send]; exact (Finset.disjoint_image ht).mpr j))
 intro p i v; exact (hq i).symm ▸ p _ (fun z => by rw [Work.H03.touched_send] at z; exact v ((Finset.disjoint_image ht).mp z))
end gauge

local notation "F" => Resolving.primary
local notation "K" => Spine.pairMood
local notation "S" i:max=> Resolving.adjacent i F K
local notation "ι" i:max => (plane (3:Axis) z).flee i
lemma motion_here (u: Cover) : (Ρ).motion (nodeC u)=nodeC (ι u):= by exact (Ρ).mote u
lemma nearBank (u: Cover) : (Ρ).anon n (wrap (More n) (nodeC u))= wrap (More n) (nodeC (ι u)):= (Shape.anno ..).trans (congrArg (wrap _) (motion_here z u))
lemma coinBank (U:Pane n) (u: Cover)(r:ℕ): (S u).pearl ρ n r t (fling 3 z n U)= (S (ι u)).pearl ρ n r t U:=by
 let s:= Signed.mirror 3; let b: Seat n:= wrap (More n) (2 • (z • step 3)); let K':= wrap (More n); let h:= nodeC u; let u₀:=ι u; let v:=nodeC u₀
 have he: affine s b (K' h)=K' v := nearBank z n u
 have hv:pingS t ((S u).gateS r n) (fling 3 z n U) ↔ pingS t ((S u₀).gateS r n) U:=by
     change _ ↔ pingS t (halo r {K' v}) U; rw [fling_eq,←he]; exact wingbright ..
 have ht: faceValue (fling 3 z n U) ((S u).localFace n) = faceValue U ((S u₀).localFace n):=by
     let W:= square 0 1; change Lattice.travel _ _ W = Lattice.travel U _ W
     rw [fling_eq,travel_pull]; exact congrArg₂ (Lattice.travel U) he rfl
 unfold Staff.pearl; rw [hv]; split; swap; · rfl
 unfold Staff.edgeBudget; rw [ht]; rfl

-- polar reflection basis sign; adapted from SitSpin.q_reflect
open Mir
lemma spin_00 (j: SpinIdx) : pin 3 j 0=(if j=(2:SpinIdx) then 1 else 0) ∧ pin 3 j 2=(if j=0 then -1 else 0):=by
 fin_cases j
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (1*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (1*(-1) + (0*(0) + 0)))) :ℂ)= -1; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (0*(0) + (1*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (0*(-1) + (1*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((1*(1)+ (0*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=1 ∧ ((1*(0)+ (0*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (1*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (1*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
lemma reverse_slots (p q:SU.Slot)(u: Cover) :
    theta (carR 3 z n) (Fock.create (basisC n u 0 p)*Fock.remove (basisC n u 2 q))=
       Fock.create (basisC n (ι u) 0 q)*Fock.remove (basisC n (ι u) 2 p):=by
 let v:= ι u; let f:= basisC n v 2 p; let g:=basisC n v 0 q
 rw [theta_mul, (Lifted.flips_basisC 3 z n u 0 p).1,(Lifted.flips_basisC 3 z n u 2 q).2]
 simp_rw [(spin_00 _).1,(spin_00 _).2,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,one_smul,neg_one_smul]
 rw [map_neg]; change (-Complex.I • Fock.remove f)*(Complex.I • -Fock.create g)= _;
 have h: Fock.remove f * create g= -(create g * Fock.remove f):=SitSpin.cr_swap 0 0 v v p q;
 rw [smul_neg, mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,h, neg_neg]; try rfl

lemma staple (u: Cover)(r:ℕ)(X:Fields n) :
    reflMark (n:=n) 3 z ((S u).rungWeave ρ r t n) X= (S (ι u)).rungWeave ρ r t n X := by
  unfold reflMark; rw [Staff.spear,Staff.spear]
  let A:= (S (ι u)).pearl ρ n r t X.1
  have he: (S u).pearl ρ n r t (reflFields 3 z X).1= A := coinBank ..
  let w:= walkC A
  have hp(i j:SU.Slot): star (-Complex.I * dMatter (SU.group.colorMat A) i j) = -Complex.I*dMatter (SU.group.colorMat A) j i:= by
    have ht:star w=w:= walk_star A; exact congrFun (congrFun ht j) i
  simp_rw [theta_sum,he,theta_smul,hp]
  rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; exact congrArg ((-Complex.I * dMatter (SU.group.colorMat A) i j) • ·) (reverse_slots z n ..)
open MixedCards
open Lamour.Bridge.Celeste
lemma wingMirror(u: Cover)(r:ℕ)(τ:MixedCards.Ticket) : fluent 3 z (MixedCards.actor (S u) τ ρ r t)=MixedCards.actor (S (ι u)) τ ρ r t:=by
  funext n; cases τ with
  | none=> exact funext (fun X=> staple z ρ t n u r X)
  | some a=> exact SitSpin.q_reflect a u n z
#print axioms wingMirror
end Glare
end YM.CF.Buffered.EmberWind
