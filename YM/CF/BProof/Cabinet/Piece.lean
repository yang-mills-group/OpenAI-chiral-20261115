import YM.CF.BProof.Cabinet.Revere
/- per-core currency. k=B.halo size payment from `sober_size`. Unnormalized positive arrays. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Cabinet
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Pods Posts Brick
open scoped Topology BigOperators Classical
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)
local notation "mH"=> Y.yard
local notation "g₀"=> Y.g
local notation "B"=>Y.Block
local notation "wB"=>House.Season mH Y.c'
local notation "π'"=> PadTotal mH g₀
namespace Mint
abbrev factorK : ℕ:= House.fourBill hNear
structure Mode where
 cost : ℝ -- income per actual bad
 burn : ℝ -- payment when any severe
 bias : ℝ -- paid pressure
namespace Mode
variable (F:Mode)
def cold (k χ:ℝ) := -((Mint.factorK:ℝ)*(k+χ+2)) -- tune coercion
variable (χ k:ℝ)
structure Buy (M d:ℕ)(y:ℝ): Prop where
  burn : Brick.Act.pocket M F.cost F.burn (raw_bill d y*(M^3:ℕ)) ≤ Real.exp (cold k χ)
  bulk : Brick.Act.costL M ≤ Real.exp k
  small : 10*Real.exp (-F.bias) ≤ Real.exp (-(χ+2))
  nonneg : 0≤k
  pressure : 0≤χ
end Mode
variable (r:ℕ)(F:Mode)(p:Brick.Solid y Y.yard.short Y.g.count.val)(χ k:ℝ)(Q:Cores Y r)(A:Finset (House.Block Y.yard Y.c'))(x:Pod Y)
def localM (b:B)(v: PadTotal mH g₀ b) : ℝ:= if b∈ A then Brick.Act.prud mH g₀ y b F.cost F.burn v else if b∈ sober Y r Q A then Brick.Act.spare mH g₀ b F.bias v else 1
def ſ := ∏ i:House.Block Y.yard Y.c',localM Y r F Q A i (x i)
def payB(b:B) := if b∈ A then Mode.cold k χ else if b∈ sober Y r Q A then -(χ+2) else if b∈ Q.val then k else 0
lemma ſ₀(b:B)(v: PadTotal mH g₀ b) : 0≤localM Y r F Q A b v:=by unfold localM; split; exact Brick.Act.prud_p ..; split; exact Brick.Act.spare_p ..; exact zero_le_one
lemma ſ_e(A:Finset B) : Envelope (ſ Y r F Q A):=by unfold ſ; generalize e:(univ:Finset (House.Block Y.yard Y.c'))=V; clear e; induction V using Finset.induction_on with|empty=>simp_rw [prod_empty]; exact Envelope.const _|insert i a p ih=> simp_rw [prod_insert p]; apply Envelope.mul _ ih; unfold localM; split; exact Law.pull (Brick.Act.prud_m ..) (measurable_pi_apply i); split; exact Law.pull (Brick.Act.spare_m ..) (measurable_pi_apply i); exact Envelope.const 1 -- tune x_
lemma ſ_pos:0≤ ſ Y r F Q A x:= prod_nonneg (fun i _=> ſ₀ Y r F Q A i (x i))
lemma ſ_on (U: Finset B)(V:Finset B)(h:V⊆Q.val)(g:U⊇ Q.val): Contour.reads (π') (ſ Y r F Q V) U:=by
 intro x y p; unfold ſ; apply Finset.prod_congr rfl; intro i _; by_cases k:i∈ Q.val; rw [p i (g k)]; exact (by unfold localM; rw [if_neg (fun v=> k (h v)),if_neg (fun v=> k (h v)),if_neg (fun (v:i∈sober Y r Q V)=> k (Finset.mem_sdiff.mp v).1),if_neg (fun (v:i∈sober Y r Q V)=> k (Finset.mem_sdiff.mp v).1)])
-- integral upper
abbrev fire(U:Finset B):= let X:=prep mH g₀ y p; px π' X.μ X.ν U
variable (u:A ⊆ Q.val)(h:F.Buy χ k Y.g.count.val Y.yard.short y)
include u h
lemma worth (b:B) : (∫ x,localM Y r F Q A b x ∂fire Y p Q.val b) ≤ Real.exp (payB Y r χ k Q A b):=by
 unfold localM fire px payB; by_cases v:b∈ A; · simp only [v,u v,if_true]; exact le_trans (Brick.Act.prud_est mH g₀ y p b F.cost F.burn) h.burn
 by_cases g:b∈ sober Y r Q A; · simp only [v,if_false,g,(show b∈Q.val from (Finset.mem_sdiff.mp g).1),if_true]; exact le_trans (Brick.Act.spare_est mH g₀ y p b F.bias) h.small
 simp only [g,v,if_false]; split; next t=> rw [integral_const,smul_eq_mul,mul_one]; exact (Brick.Act.bulk_cost mH g₀ y p b).trans h.bulk
 next t=> rw [integral_const,probReal_univ, Real.exp_zero, one_smul]
def storm := Q.val \ sober Y r Q A
lemma sum_pay : ∑ b:House.Block Y.yard Y.c',payB Y r χ k Q A b ≤ -(χ+2) * Q.val.card:=by
 let f := payB Y r χ k Q A; let X:=Q.val; let T:=storm Y r Q A; let Z:=sober Y r Q A; have hp : Z⊆X:=sdiff_subset
 have hv:X.card=Z.card+T.card:= by unfold T storm; change X.card=_+(X \ Z).card; rw [add_comm,card_sdiff_add_card_eq_card hp]
 have hu:A⊆T:= faulty_cost Y r Q u
 have hw : ∑ i∈ T,f i ≤ A.card*Mode.cold k χ+ T.card*k:=by
    rw [← sum_sdiff hu]; -- tune sum_sdiff args
    have hx : ∀ i∈T \ A,f i=k:=by
       intro i p; obtain ⟨b,t⟩:=Finset.mem_sdiff.mp p; obtain ⟨c,v⟩:= Finset.mem_sdiff.mp b; unfold f payB; rw [if_neg t,if_neg v,if_pos c]
    have hh(i)(v:i∈A): f i=Mode.cold k χ:= if_pos v; rw [sum_congr rfl hx,sum_congr rfl hh,sum_const,sum_const]; simp_rw [nsmul_eq_mul,add_comm (↑(T \ A).card * k)]; exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card sdiff_subset)) h.nonneg) _
 have hx : ∀ i∈Z,f i= -(χ+2):=by
    intro i p; have he:i∉A:=fun v=> (Finset.mem_sdiff.mp (hu v)).2 p; unfold f payB; rw [if_neg he,if_pos p]
 have hh:f=f:=rfl
 change (∑ b:B,f b) ≤ _; rw [← sum_subset (subset_univ X) (fun i _ hi=>?_), ← sum_sdiff hp]; swap; · unfold f payB; rw [if_neg (fun v=>hi (u v)), if_neg (fun v=>hi (hp v)),if_neg hi]
 change (∑ i∈T, f i) + ∑ i∈Z, f i ≤ _; apply (add_le_add_left hw (∑ i∈ Z,f i)).trans; rw [sum_congr rfl hx,sum_const,nsmul_eq_mul]; have eh : (T.card:ℝ) ≤ A.card * (Mint.factorK:ℝ):= by exact_mod_cast sober_size Y r (A:=A) Q
 change _ ≤ -(χ+2)* (X.card:ℝ); rw [hv,Nat.cast_add]; unfold Mode.cold; nlinarith [mul_le_mul_of_nonneg_right eh (show 0≤ k+χ+2 by linarith [h.nonneg,h.pressure])]
lemma gold : (∫ x,ſ Y r F Q A x ∂πμ π' (prep mH g₀ y p).μ (prep mH g₀ y p).ν Q.val) ≤ Real.exp (-(χ+2)*(Q.val.card:ℝ)) :=by
 let μ:= fire Y p Q.val; haveI(i:B): IsFiniteMeasure (μ i):=px_fin ..; change (∫ x,ſ Y r F Q A x ∂Measure.pi μ) ≤_; unfold ſ; rw [integral_fintype_prod_eq_prod]; refine le_trans (prod_le_prod (fun i _=> integral_nonneg (ſ₀ Y r F Q A i)) (fun i _=> worth Y r F p χ k Q A u h i)) ?_; rw [←Real.exp_sum]; exact Real.exp_monotone (sum_pay Y r F χ k Q A u h)
end Mint
end YM.CF.BProof.Cabinet
