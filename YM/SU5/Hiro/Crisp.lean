import YM.SU5.Diva.Balm
import YM.SU5.Hiro.Fresh
import YM.SU5.Hiro.Harvest
/-! # Local Herm color-current-grasp. Uses Wick signs at t>0 and canonical node.
Still on *resolution* theory. Adaptation of `Bilinear.Word`. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Fock Finset Cube Spire Scroll MeasureTheory Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree Gloss Branch RP Reflect Wilson Lat Rush SU Lat Lattice Precision Tree Tenant Push.SectorMeasure Peaks Tulip Buffered Afterglow Lifted Heat Advance Vale Window -- adjust
open Reed (Fine)
open Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder ContDiff
attribute [local instance] opCStarAlgebra
open Ballad
variable {N:Side}
private def film (x y : Site N × SpinIdx) (V: Op Slot) : Op (Single N):= Matrix.of fun i k=> if i.1=x∧ k.1=y then V i.2 k.2 else 0
private lemma reel(x y:Site N×SpinIdx)(V:Op Slot)(g: Seat N→ E): twist (tradew N g) (film x y V)=film x y ((matter (g (node x.1))).val*V*star (matter (g (node y.1))).val):=by
 let H := tradew N g; let W:=(matter (g (node x.1))).val*V*star (matter (g (node y.1))).val
 have he(V:Op Slot)(a b:Site N × SpinIdx) : tap (film x y V) a b= if a=x ∧ b=y then V else 0:= by ext i j; by_cases p:a=x∧ b=y <;> simp [film,tap,p]
 have hp (a b: Site N × SpinIdx) : tap (sings false H (film x y V)) a b=tap (film x y W) a b := by
    change tap (sings false (portX (Equiv.refl (Site N × SpinIdx)) (fun i=> matter (g (node i.1)))) _) _ _= _; rw [tap_sg (p:=Equiv.refl (Site N × SpinIdx)) (F:=fun i=> matter (g (node i.1))),he,he]
    by_cases h:a=x ∧ b=y; swap; · simp only [Equiv.refl_apply,if_neg h,win_z,mul_zero,zero_mul]
    obtain ⟨rfl,rfl⟩:= h; simp only [Equiv.refl_apply, true_and, if_true]; rfl
 ext ⟨x,a⟩ ⟨y,b⟩; exact congr_fun (congr_fun (hp x y) a) b
private lemma frame (x y : Site N × SpinIdx) (V:Op Slot) : dg (film x y V)=∑ i:Slot, ∑ j:Slot,V i j • (put (x,i)*takeF (y,j)) := by
 let f(i j:Single N):= (film x y V) i j • (put i * takeF j); change ∑ i,∑ j, f i j=_
 have hp (a : Site N × SpinIdx) (i : SU.Slot) : ∑ t : Single N, f (a,i) t= ∑ j:SU.Slot, f (a,i) (y,j):=by
    rw [show (∑ t : Single N, f (a,i) t)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> f (a,i) k), sum_eq_single y]
    · intro i hi k; apply sum_eq_zero; intro j _; unfold f film; rw [Matrix.of_apply,if_neg (fun z=>k z.2),zero_smul]
    simp
 rw [show (∑ i,∑ j,f i j)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> ∑ j, f k j)]; simp_rw [hp]
 rw [sum_eq_single x]; swap; · intro a _ t; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; unfold f film; rw [Matrix.of_apply,if_neg (fun z=>t z.1),zero_smul]
 swap; · simp
 exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>by unfold f film; rw [Matrix.of_apply, if_pos (show x=x∧ y=y from ⟨rfl,rfl⟩)]
variable (o:Cover)(L:Ballad.Twah.DirSpin)(R:ℕ) (A:ColorL)
-- p in creators
abbrev unifyT : Twah:= ⟨o,o,L.1,L.2,[],rfl⟩
def colorEntry (p q: SU.Slot) : ColorL →ₗ[ℝ] ℂ:= ({toFun:=fun x: Op Slot=> x p q, map_add':=by intros; rfl,map_smul':=by intros; rfl} : Op Slot→ₗ[ℝ]ℂ).comp walkC
def wrapCurrent (N:Side): ColorL →ₗ[ℝ] FC (Single N) where
 toFun A:=∑ p:Slot,∑ q:Slot, colorEntry p q A • (Twah.gold R • Gemini.trailC (unifyT o L) p q N (1,1))
 map_add' a b:=by simp_rw [map_add,add_smul,Finset.sum_add_distrib] -- defeq
 map_smul' t x:=by simp_rw [map_smul, smul_assoc, ← Finset.smul_sum, RingHom.id_apply] -- possible issue

def holdC : Weaver:= fun N _=> wrapCurrent o L R N A
lemma hold_apply (Y:Fields N): holdC o L R A N Y=wrapCurrent o L R N A:=rfl
lemma hold_sum : wrapCurrent o L R N A =∑ p:Slot,∑ q:Slot, walkC A p q • (Twah.gold R • Gemini.trailC (unifyT o L) p q N (1,1)):=rfl
lemma hold_form : holdC o L R A=∑ p:Slot, ∑ q:Slot, colorEntry p q A • (Twah.gold R • Gemini.trailC (unifyT o L) p q):=by
 funext N x; let c:=wrapCurrent o L R N A; simp only [Finset.sum_apply,Pi.smul_apply,hold_apply]; rfl
lemma dgC : wrapCurrent o L R N A=(R:ℂ)^3 • dg (film (wrap N o, upSpin L.1) (wrap N o,dnSpin L.2) (walkC A)):=by
 let T:= unifyT o L; rw [hold_sum,frame]; simp_rw [smul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_; unfold Gemini.trailC Ballad.Twah.lower Ballad.Twah.upper basisC Fock.remove; rw [map_smul,map_smul,star_smul, create_put,create_put]; let U:= put ((wrap N o,upSpin L.1),i); let V:=takeF ((wrap N o,dnSpin L.2),j); let q:=Lifted.winding N o; let W:=walkC A i j; let x:ℂ:=(R:ℂ)^3
 change W • (-x • ((star q • V)*(q • U)))=x • (W • (U*V)); rw [Matrix.smul_mul, Matrix.mul_smul,smul_smul (star q) q, show star q * q=1 from ?_, one_smul]
 · have he:V*U= -(U*V):= (eq_neg_of_add_eq_zero_left ((mixed ((wrap N o,dnSpin L.2),j) ((wrap N o,upSpin L.1),i)).trans (if_neg (fun v=> dn_half L.2 (by rw [show dnSpin L.2=upSpin L.1 from congrArg (fun k:Single N=> k.1.2) v]; exact up_half _)))))
   simp only [he,neg_smul,smul_neg,neg_neg]; exact smul_comm ..
 have he: ‖q‖=1:=Rush.fee_norm _; rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,he,one_pow,Complex.ofReal_one]
lemma current_cov (Y:Fields N)(g:Seat N→SU.E): holdC o L R (SU.group.adjoint (g (wrap (More N) (nodeC o))) A) N (simultaneous g Y)= twist (quantU (tradew N g)) (holdC o L R A N Y):=by
 rw [hold_apply,hold_apply,dgC,dgC,twist_scalar,dg_cov,reel,node_of,walk_rotate]; rfl
lemma holdPass : Passion (holdC o L R A) ({nodeC o}:Finset Cover) false:=by
 let T:=unifyT o L; have hv: T.patio= {nodeC o}:=by simp [T,Twah.patio,unifyT, visits]; -- tune
 rw [←hv,hold_form]; exact Passion.weaveSum _ _ (fun i _=> Passion.weaveSum _ _ (fun j _=> ((Gemini.trail_pass T i j).haze _).haze _))
end YM.CF.Hiro
#print axioms YM.CF.Hiro.wrapCurrent
#print axioms YM.CF.Hiro.current_cov
