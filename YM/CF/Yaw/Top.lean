import YM.CF.Yaw.Saran
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B)) (e:ℝ)(X: Meter TailB G e)(V: Meter Grave G e)
variable (HX:TailB→Support (Domain P B)→Toll (Iota G))(HY:Grave→Support (Domain P B)→Toll (Iota G))
local notation "α'"=> Scion.tinOre (switchG G).symm
local notation "H'"=> Eire.Ride S
local notation "W'"=> LeanV (Single (mid N B))
local notation "τ"=> Urn.Twig (Single (mid P B))
variable {ι:Type*}{n B0 s:ℕ}{a A A' U:ℝ}(k d:ℕ)
variable (x:∀ i Y, Suite (badge _) (pinH G e true) (pinH G e false) Y (HX i Y) (X i Y))
variable (u:∀ i Y, Suite (badge _) (pinH G e true) (pinH G e true) Y (HY i Y) (heal G e V i Y)) (q:Raid (LeanV (Single (mid N B))))(h: Turner q)
variable (b:B0>0)(p:k ≤ s*B0)(y:0≤a)(t: a*2*χ s ≤ B0*A)(t':a*2*χ s≤ B0*A')(b':0≤A)(y':0≤A')
local notation "L'"=> Domain P B
local notation "V_"=> Domain N B
local notation "£"=> (Real.exp (a*(χ s:ℝ)))
def ξH (q:Raid (LeanV (Single (mid N B))))(i:τ): Track H' ℝ:= ownH ℝ H'+(rateT q (sign_l G S k d HX i) + ∑ j:τ, rateT q (sign_z G S k d HY i j))
include x h u
lemma firm_p: OfferS q (ξH G S HX HY k d q) (sign_l G S k d HX) (sign_z G S k d HY):=by
 have ht:=X_pos G S _ X HX k d x; have hg :=Z_pos G S _ V HY k d u; refine ⟨h,fun i=> le_add_of_nonneg_right (add_nonneg (Turn_up h (ht i)) (sum_nonneg fun j _=> Turn_up h (hg i j))),ht,hg,fun i=> le_add_of_nonneg_left coinH⟩
variable {R c' d' Z R':ℝ}
omit x h u
abbrev twinN(i:τ) (b:Bool)(r:Bool)(j:Iota G):τ:= (α').symm (tellX b (r,j))
-- `ℝ+` prices currency.S
lemma split_r (F:τ→ℝ):(∑ i:τ,F i)=∑ b:Bool,∑ r:Bool,∑ j:Iota G, F ((α').symm (tellX b (r,j))):=by
 let V : Bool × Bool × Iota G≃ τ:={toFun:=fun ⟨b,x⟩=> (α').symm (tellX b x),invFun:=fun i=> (tallC (α' i),twigS (α' i)),left_inv:=fun ⟨i,j⟩=>by simp only [Equiv.apply_symm_apply,(tellY ..).1, (tellY ..).2],right_inv:=fun i=>by dsimp only; rw [tellU,Equiv.symm_apply_apply] }; rw [← Equiv.sum_comp V F,Fintype.sum_prod_type]; exact sum_congr rfl fun i _=> Fintype.sum_prod_type .. -- tune
lemma fee_r(i j:τ): ‖due_z G i j‖ ≤ if (twigS (α' j)).2=(twigS (α' i)).2 then (1:ℝ) else 0:=by
 unfold due_z Urn.soar oakN; let x:= (twigS (α' i)).2; let y:= (twigS (α' j)).2; dsimp only; split_ifs
 · next hv he => rw [norm_zero]; norm_num
 · next hv he=> rw [norm_zero]
 · next hv he =>
      unfold feeX; split; · simp_rw [he, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,mul_one]; unfold cSignX; split <;> norm_num
      simp [cSignX]
 next hv he=> unfold feeX; split; simp [Matrix.smul_apply,Matrix.one_apply_ne (Ne.symm he),cSignX]; simp [cSignX]
abbrev stepV (v c:ℝ)(k:ℕ)(i j:Iota G):=(1+c* separation (lookM G i) (lookM G j):ℝ)^k*v
include x
lemma regal(r:ℝ)(i:τ)(v:0≤ R)(g:∀ j, incline (hall G e) n R (fun _=>r) A (HX j))(z:0≤Z)(w:∀ j:LeanV (Single (mid N B)),q {j} ≤ stepV G Z R n (twigS (α' i)).2 (patchQ G j.2)): (∑ Y:Support L',Branch.rent A Y * call G HX d Y i q) ≤ 2*(lip d*(Z*r)):=by
 let m:=(twigS (α' i)).2; let M:= (tallC (α' i), (twigS (α' i)).1); let F(T:Iota G):= (1+R*separation (lookM G m) (lookM G T):ℝ)^n
 let K(j):= saleM A (HX M) m j; have hp(t:Iota G):0 ≤ F t:=by unfold F; positivity
 have hh(t:Iota G):0≤ K t := sale_nn (fun S=>(x M S).nonn) ..
 unfold call; simp_rw [Finset.mul_sum]; rw [sum_comm]; change (∑ j:Bool × (Single (mid N B)),_)≤_; rw [Fintype.sum_prod_type];
 have hl (b:Bool): ∑ j:Single (mid N B), (∑ Y: Support L', Branch.rent A Y * (q {(b,j)} * payK G d HX Y i (b,j))) ≤ lip d*(Z*r):=by
    have hx (j: Single (mid N B)):0 ≤ q {(b,j)}∨ q {(b,j)}<0:=le_or_gt ..
    let D(j: Single (mid N B)):= F (patchQ G j)* K (patchQ G j); have hz:∑ j,D j≤ r:=by
       apply le_trans _ (g M m); apply le_trans (Eq.le (show (∑ j,D j)=∑ j∈ Finset.univ.map (patchQ G),F j*K j from ?_)) ?_; swap; · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _=> mul_nonneg (hp j) (hh j)
       rw [sum_map] -- patchQ type ↪
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz z) (richP d)); rw [Finset.mul_sum,Finset.mul_sum]; apply sum_le_sum; intro j _; unfold payK D K saleM; simp_rw [Finset.mul_sum]; refine sum_le_sum fun Y _=>?_; let p':= patchQ G j; let y:=HX M Y m p'; have vt:= w (b,j); change q {(b,j)} ≤ F p'*Z at vt; let Rq:= Branch.rent A Y; change Rq*(q {(b,j)}*(lip d*y)) ≤ lip d*(Z*(F p'*(Rq*y))); refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right vt (mul_nonneg (richP d) ((x M Y).nonn m p'))) (rent_pos ..).le).trans ?_; exact le_of_eq (by ring) -- type
 apply (sum_le_sum (fun i (_:i∈(univ: Finset Bool))=> hl i)).trans; simp
omit x
include u
lemma repay_h (i:τ)(g:∀ j, Branch.Ledger A' (HY j) R')(a:ℝ)(s:ℕ): (∑ j:τ,(Real.exp (a*(χ s:ℝ))*(∑ Y:Support L',Branch.rent A' Y*payZ G d HY Y i j) + ‖due_z G i j‖)) ≤ 4*(Real.exp (a*χ s)*lip d*R'+1):=by
 let Z:= Real.exp (a*(χ s:ℝ)); rw [split_r G]; have hp(b t:Bool) :
    let X(x:Iota G):= (α').symm (tellX b (t,x)); (∑ j:Iota G,(Z*(∑ Y:Support L',Branch.rent A' Y*payZ G d HY Y i (X j))+‖due_z G i (X j)‖)) ≤ Z*lip d*R'+1:=by
    intro X; let V(Y:Support L')(x:Iota G):= HY (tallC (α' i),b,(twigS (α' i)).1,t) Y (twigS (α' i)).2 x; let y:=(twigS (α' i)).2; rw [sum_add_distrib]; apply add_le_add; swap; · refine (sum_le_sum (fun j (_:j∈(univ:Finset _))=>fee_r G i (X j))).trans ?_; simp [X, Equiv.apply_symm_apply,(tellY ..).2]
    have ht := (g ((tallC (α' i),b,(twigS (α' i)).1,t))).rows y; refine le_trans ?_ (mul_le_mul_of_nonneg_left ht (mul_nonneg (Real.exp_pos _).le (richP d))); change (∑ j,_)≤ (Z*lip d)* (∑ j:Iota G,∑ Y:Support L',Branch.rent A' Y* V Y j); rw [Finset.mul_sum]; apply sum_le_sum; intro j _; simp_rw [Finset.mul_sum]; apply sum_le_sum; intro Y v; dsimp only [payZ]; simp only [X,Equiv.apply_symm_apply,(tellY b _).1,(tellY b _).2]; unfold V; exact le_of_eq (by ring)
 have hz(t:Bool): ∑ r:Bool, (∑ j:Iota G,(Z*(∑ Y:Support L',Branch.rent A' Y*payZ G d HY Y i ((α').symm (tellX t (r,j))))+ ‖due_z G i ((α').symm (tellX t (r,j)))‖)) ≤ 2*(Z*lip d*R'+1):=by refine (sum_le_sum (fun r (_:r∈(univ:Finset Bool))=>hp t r)).trans ?_; simp; linarith
 exact (sum_le_sum (fun t (_:t∈(univ:Finset Bool))=>hz t)).trans (by simp [Z]; linarith)
include x h b p y t t' b' y'
lemma token_h(i:τ)(D:Support V_)(c:Eire.mint S (twigS i).2∈D)(v:0≤ R)(g:∀ j, incline (hall G e) n R (fun _=>U) A (HX j))(u':∀ j, Branch.Ledger A' (HY j) R')(z:0≤Z)(w:∀ j:LeanV (Single (mid N B)),q {j}≤ stepV G Z R n (twigS (α' i)).2 (patchQ G j.2)) : KeepsP D (ξH G S HX HY k d q i) B0 a (1+(£*(2*(lip d*(Z*U))) + 4*(£*lip d* R'+1))):=by
 refine Kings_add (Kings_bot _ _ _ zero_le_one) (Kings_add ?_ (Kings_budget (Kings_sum _ _ fun j _=> pair_k G S e V HY k d u q h b p y t' y' i j D c) (repay_h G e V HY d u i u' a s)))
 exact Kings_budget (sail_k G S e X HX k d x q h b p y t b' i D c) (mul_le_mul_of_nonneg_left (regal G e X HX d x q U i v g z w) (Real.exp_pos _).le)
end YM.CF.Yaw
