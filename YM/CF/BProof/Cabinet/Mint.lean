import YM.CF.BProof.Cabinet.Piece

/- collect from subsets bad. Bronze upper interface on accepted. Requires: log priced Q for paid,
any small weights; cost F.Slot and f. Strong & weak compatibility. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
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
variable (r:ℕ)(F:Mode)(p:Brick.Solid y Y.yard.short Y.g.count.val)(χ k:ℝ)(h:F.Buy χ k Y.g.count.val Y.yard.short y)(Q:Cores Y r)(x:Pod Y)
def mintF := ∑ V∈ Q.val.powerset, ſ Y r F Q V x
lemma mint_m : Envelope (mintF Y r F Q):= Envelope.sum _ _ fun _=> ſ_e ..
lemma mint_0 : 0≤ mintF Y r F Q x:= sum_nonneg fun i _=> ſ_pos ..
lemma mint_here : reads π' (mintF Y r F Q) (plate Y r Q):= fun x y p=> sum_congr rfl fun i ht=> ſ_on Y r F Q _ i (mem_powerset.mp ht) ((plan wB r).sub Q) _ _ p
abbrev tip := -(χ+2)* Q.val.card -- cast? ℝ
include h
lemma mint_est : (∫ x,mintF Y r F Q x ∂πμ π' (prep mH g₀ y p).μ (prep mH g₀ y p).ν Q.val) ≤Tower.χwage wB r χ Q:=by
 unfold mintF; set μ:= πμ π' (prep mH g₀ y p).μ (prep mH g₀ y p).ν Q.val; haveI:IsFiniteMeasure μ:=by unfold μ; infer_instance
 rw [integral_finsetSum]; swap; · intro i _; exact Law.pay (ſ_e ..)
 apply (sum_le_sum fun i t=> gold Y r F p χ k Q i (mem_powerset.mp t) h).trans; rw [sum_const,card_powerset,nsmul_eq_mul]
 unfold Tower.χwage; refine le_trans (b:= (Real.exp 2)^Q.val.card*Real.exp (tip Y r χ Q)) ?_ ?_
 · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; push_cast; gcongr; linarith [Real.add_one_le_exp 2]
 rw [←Real.exp_nat_mul,← Real.exp_add]; unfold tip; ring_nf; exact le_rfl
variable (P:Entice S L a d y)(T:PathData SU.group)(θ:ℝ)(H:T.Bounds c w R v)(e:θ∈Set.Icc (1/2) 2)(v₀:200≤r)
abbrev GoldB := ore P Y T θ H e (r:=r) (show 5≤r by omega) -- ar. check
abbrev Title:=Battery.Night r (prep mH g₀ y p) (bitL Y) (Cabinet.Ready P Y T θ) (lid Y) (GoldB Y r P T θ H e v₀) (Tower.χwage wB r χ)
def brave : Title Y r p χ P T θ H e v₀:= ⟨mintF Y r F,mint_m Y r F,mint_here Y r F,mint_0 Y r F,mint_est Y r F p χ k h⟩ -- implicit function issue
omit h
include H e v₀
-- interface
variable (t: Cabinet.Ready P Y T θ x)(hQ: Q∈ recital Y r x)
abbrev grey(x:Static mH g₀):= fault Y r x Q
abbrev paid(x:Static mH g₀):= sober Y r Q (fault Y r x Q)
def fare(b:B):= Brick.Act.sniff mH g₀ b F.cost F.burn (x b)
def settle := (∑ b∈ grey Y r Q x,fare Y F x b)-(paid Y r Q x).card*F.bias
-- natural form log with indicator rough severity
abbrev trueG(b:B):= Act.SevereTag mH g₀ b (x b)
def stripe:= (grey Y r Q x).filter (trueG Y x)
include hQ
omit H e
lemma paid_far (b:B)(u:b∈paid Y r Q x): b∉ nearL Y x:=by
 obtain ⟨g,k⟩:= Finset.mem_sdiff.mp u; exact fun t=> k ((fault_near Y r Q hQ g (le_trans (by unfold hNear; omega) v₀)).2 t) -- header include hQ?
omit v₀ hQ
lemma settle_eq: settle Y r F Q x=(grey Y r Q x).card*F.cost - (stripe Y r Q x).card * F.burn - (paid Y r Q x).card* F.bias:=by
 let f:= trueG Y x; unfold settle; congr 1; unfold stripe; rw [← nsmul_eq_mul,← nsmul_eq_mul, ← sum_const (s:=grey Y r Q x),← sum_const (s:=(grey Y r Q x).filter _),sum_filter, ← sum_sub_distrib]; apply sum_congr rfl; intro i v; by_cases p:f i; · rw [if_pos (show trueG Y x i from p)]; exact if_pos p
 rw [if_neg (show ¬ trueG Y x i from p),sub_zero]; exact if_neg p
include H e v₀ hQ t
lemma payable : Real.exp (settle Y r F Q x)≤ mintF Y r F Q x:=by
 let A:=grey Y r Q x; let U:=paid Y r Q x; have hu : A ⊆ Q.val:= inter_subset_right; apply le_trans _ (single_le_sum (fun i _=> ſ_pos Y r F Q i x) (mem_powerset.mpr (show A⊆Q.val from hu))); unfold ſ; let f(i:B):= if i∈A then fare Y F x i else if i∈U then -F.bias else 0; have he : Disjoint A U:= Finset.disjoint_left.mpr (fun i p v=> (Finset.mem_sdiff.mp (faulty_cost Y r Q hu p)).2 v)
 have hf(i:B): localM Y r F Q A i (x i)= Real.exp (f i):=by
    unfold f localM; split; next g=> exact if_pos ((sick_c Y x i).1 (Finset.mem_inter.mp (show i∈ sick Y x ∩ Q.val from g)).1)
    next g=>
      split; next u=> exact if_pos (stand_bill P Y T θ x i H e t (paid_far Y r Q x v₀ hQ i u)) -- tune paid_far
      next u=> rw [Real.exp_zero]
 simp_rw [hf,←Real.exp_sum]; apply le_of_eq; apply congrArg Real.exp; unfold settle; change _-_=∑ i:B,f i; unfold f; rw [sum_ite,show univ.filter (· ∈ A)=A from (by ext; simp),←sum_filter,show (univ.filter (· ∉ A)).filter (· ∈ U)=U from ?_,sum_const,nsmul_eq_mul]; change _- (U.card:ℝ)*F.bias=(∑ b∈ A,fare Y F x b)+_; rw [mul_neg,←sub_eq_add_neg]; ext i; simp; exact fun t l=> Finset.disjoint_left.mp he l t
include h
structure Freight (G:Cores Y r → Pod Y→ℂ):Prop where
 bill : ∀ i:Cores Y r,Measurable (G i)
 cost : ∀ (x:Pod Y)(q:Cores Y r), Cabinet.Ready P Y T θ x→ q∈ recital Y r x→ ‖G q x‖≤ Real.exp (settle Y r F q x)
 stay : ∀ (x y': Pod Y)(q:Cores Y r), Cabinet.Ready P Y T θ x → Cabinet.Ready P Y T θ y'→ q∈ recital Y r x→ q∈ recital Y r y'→ Spiced Y (plate Y r q) x y'→ G q x= G q y'
omit hQ t
lemma grant (G:Cores Y r→Pod Y→ℂ)(z:Freight Y r F P T θ G): Bronze r (prep mH g₀ y p) (bitL Y) (Cabinet.Ready P Y T θ) (lid Y) G (brave Y r F p χ k h P T θ H e v₀):=⟨z.bill,fun i x y h p q v t=>z.stay x y i p q v t h,fun i x p q=> (z.cost x i p q).trans (payable Y r F i x P T θ H e v₀ p q)⟩
end Mint
end YM.CF.BProof.Cabinet
