import YM.CF.BProof.Charge.Lamp
import YM.CF.BProof.Moment.Comb

/-! Split exactly the `inChannels` under exp. Combine heavy terms and weak tail before
choosing the Mark charges. Equivariant for all the history budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Push.AbsoluteSums Work Micro Moment MeasureTheory ConnectedActivityE6.Raw Next.SectorChange Real AnalyticBridge.SectorAffine -- clashes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}{G:Gauge} (c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(σ: Signed)(β:ℝ)(U : Config G s){t W C Λ:ℝ}(h:T.Bounds c W C Λ)(k:ValidR c p M)
lemma direct_spin : ∑ x:Pressure.Cell s,directQ c p β (pull σ 0 U) x=∑ x:Pressure.Cell s,directQ c p β U x:=by
 let e:= Equiv.ofBijective (Face.send σ (0:Site s)) ⟨Face.injective_send ..,Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩ -- tune namespace
 unfold directQ; simp_rw [Face.send_price U _ σ 0 G.chord G.chord_inv (fun g h=> G.chord_conj h g)]; exact Equiv.sum_comp e (fun x=> β*PathData.clipped c p.threshold (G.chord (faceValue U x)))
-- one channel bill (Loop Ready)
def mates := Bill.kit Finset.univ fun a:PlaqAxes=> ((pairBook (s:=s) c p T M σ (β*share) a h k).charge)
def loopP := ((atomBook (s:=s) p σ T.loop share h.two (fun i=>(h.invariant i).1) h.width).charge)
def cubicP := ((atomBook (s:=s) p σ T.cubic (β*share) h.three (fun i=>(h.invariant i).2.1) h.width).charge)
def quarticP := ((atomBook (s:=s) p σ T.quartic (β*share) h.four (fun i=>(h.invariant i).2.2) h.width).charge)
def trail := (mates (s:=s) c p T M σ β h k).combine ((loopP c p T σ h).combine ((cubicP c p T σ β h).combine (quarticP c p T σ β h)))
def weak := Bill.kit Finset.univ fun σ=> trail (s:=s) c p T M σ β h k
lemma trail_eq : share * T.principal c p β (pull σ 0 U)=share*(∑ x,directQ c p β U x)+(∑ x:PlaqAxes,∑ y:Site s,higher c p T M β U (σ,x,y))+(trail c p T M σ β h k).price U := by
 let q:=pull σ 0 U; rw [trail,Bill.combine_price,Bill.combine_price,Bill.combine_price, ← direct_spin c p σ β]; unfold mates loopP cubicP quarticP; rw [Bill.kit_price]; simp_rw [atom_bookpay,pair_paid]
 have he(x): (∑ y,higher c p T M β U (σ,x,y))=β*share*∑ y:Site s, Pressure.trunk T c M 1 p.threshold q (y,x):=by
   unfold higher ref lRead; dsimp only [Lam.center]; rw [← mul_sum]; exact congrArg (β*share*·) (Equiv.sum_comp (Micro.equiv (s:=s) σ).symm (fun y=>Pressure.trunk T c M 1 p.threshold q (y,x)))
 let H:= Pressure.trunk T c M 1 p.threshold q; let Q:= fun x:Pressure.Cell s=>tails T c M 1 p.threshold x q; let P:=fun x:Pressure.Cell s=>PathData.clipped c p.threshold (G.chord (faceValue q x))
 have ht(x:Pressure.Cell s) : T.baseTerm c p q x=P x+ Q x+H x:= by unfold Q P H; rw [← cuff_tails]; unfold Pressure.cuff Pressure.crown; ring
 have hh (f:Pressure.Cell s→ℝ) : ∑ x:PlaqAxes,∑ y:Site s,f (y,x) =∑ i,f i:=by rw [Fintype.sum_prod_type,sum_comm]
 change share*(β*((∑ x,T.baseTerm c p q x)+_)+_) = _; simp_rw [ht,he]; simp_rw [directQ,← mul_sum]; change _= share*(β*∑ x,P x)+(β*share* ∑ a:PlaqAxes,∑ x:Site s,H (x,a)) +(β*share*∑ a:PlaqAxes,∑ x:Site s,Q (x,a)+( _ : ℝ)) -- parentheses tune
 rw [hh,hh]; simp only [sum_add_distrib]; ring
lemma exact_channels : T.inChannels c p β U=(∑ x:Pressure.Cell s,directQ c p β U x)+(∑ a:Lam s,higher c p T M β U a)+(weak c p T M β h k).price U:=by
 change share*(∑ a,T.principal c p β (pull a 0 U))=_; rw [Finset.mul_sum]; simp_rw [trail_eq c p T M _ β U h k]; rw [sum_add_distrib,sum_add_distrib]; simp only [weak,Bill.kit_price,Lam,Fintype.sum_prod_type,sum_const, card_univ,nsmul_eq_mul, share, ←mul_assoc, mul_inv_cancel₀ (by positivity : (↑(Fintype.card Signed):ℝ)≠0),one_mul]

abbrev uPull (W:ℝ)(M:ℕ):= min (ann W) (pairRate W M)
def trailRate (t β W C Λ:ℝ)(M:ℕ):= (Fintype.card PlaqAxes:ℝ)* (|β*share| *pairUnit W C M) + (atomUnit W Λ*(|share| *t^2)+(atomUnit W C*(|β*share| *t^3)+atomUnit W C*(|β*share| *t^4)))
def rate (t β W C Λ:ℝ)(M:ℕ):= (Fintype.card Signed:ℝ)* trailRate t β W C Λ M
lemma trail_p (s:Side): (trail (s:=s) c p T M σ β h k).fine (uPull W M) (trailRate p.threshold β W C Λ M):=by
 have hh {i:ℕ}(A:ℕ→Atom G i){δ:ℝ}(b:SumBudget (fun x=>(A x).budget W) δ) (e:∀ x,(A x).Invariant)(a:ℝ) : ((atomBook (s:=s) p σ A a b e h.width).charge).fine (uPull W M) (atomUnit W δ*(|a| *p.threshold^i)):= by
    refine Letters.fine _ (Toll.weaken (aFoot (s:=s) σ A) (aSize p A a) ?_ (min_le_left ..) le_rfl); exact atom_p p σ A b h.width a s
 apply Bill.combine_fine
 · let E:=|β*share| * pairUnit W C M
   have v(i:PlaqAxes): ((pairBook (s:=s) c p T M σ (β*share) i h k).charge).fine (uPull W M) E := by
     apply Letters.fine; exact Toll.weaken (pairF (s:=s) T M σ i) (pairS T M (β*share) i) (pair_p c T M σ (β*share) i h s) (min_le_right ..) le_rfl -- tune
   simpa only [mates,sum_const,card_univ,nsmul_eq_mul] using Bill.kit_fine Finset.univ (fun a=> (pairBook (s:=s) c p T M σ (β*share) a h k).charge) (fun i hi=>v i) -- tune univ
 exact Bill.combine_fine _ _ (hh T.loop _ _ _) (Bill.combine_fine _ _ (hh T.cubic _ _ _) (hh T.quartic _ _ _))
lemma weak_p (s:Side) : (weak (s:=s) c p T M β h k).fine (uPull W M) (rate p.threshold β W C Λ M):= by unfold rate; simpa only [weak,sum_const,card_univ,nsmul_eq_mul] using Bill.kit_fine univ (fun σ=>trail (s:=s) c p T M σ β h k) (fun σ _=> trail_p c p T M σ β h k s)
end YM.CF.BProof.Charge
