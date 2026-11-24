import YM.CF.Lich.Word
import YM.CF.Lich.Lune
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
variable{M:Monk SU.group S}{X:Support (Domain N B)}(H:Duo SU.group S U M X)(p:Ready T x)(hv:1000≤radiusB x)
variable(o:Site (Domain N B))(n':ℕ)(hp:Beat.shadows (o:=o) X n')
local notation "b₀"=> radiusB x
local notation "P0"=> M.sent x T q θ l β
local notation "B1"=> l+76
local notation "D1"=> Cay.horn x l
local notation "Vt"=> (j*b₀)
variable (t:(A.post+100)*radiusB x ≤ n')(v:A.loft*radiusB x ≤ n')
open Rel Work.E03
local notation "Ta"=> Domain N B
include H p hv hp t
lemma flickerB : Virt S (fun M=> dua T x q θ l β A.vita A.rota o M) X:=by
 intro Yw Ww u; let z(Mu: Monk SU.group S):= gate x Mu o; let T'(N:Monk SU.group S)(i:N.zoo x):= ansC (S:=S) o i.val.val* Corne.flare T x q θ l β A.vita A.rota N i; have he(N:Monk SU.group S) : dua T x q θ l β A.vita A.rota o N=∑ i∈z N,T' N i:=Eq.symm (Finset.sum_subset (subset_univ (z N)) fun i p v =>show T' N i=0 from by unfold T' ansC; rw [if_neg (fun a=>v (mem_filter.mpr ⟨mem_univ _,a⟩)),zero_mul])
 dsimp only; rw [he,he]
 have h'(Yw Ww:Monk SU.group S)(u:Beat Yw Ww X)(i:Yw.zoo x)(h:i∈z Yw):∃ k∈z Ww, i.val.val=k.val.val:=by
    have hQ:= Tarn.innZ _ _ (mem_filter.mp h).2; obtain ⟨V,H⟩:= (u.scope (x:=x) (r:=1) (by simp_rw [Nat.add_mul] at t; omega) hp).switch i hQ; exact ⟨V,mem_filter.mpr ⟨mem_univ _,H ▸ (mem_filter.mp h).2⟩,H⟩
 choose f g Q using h' Yw Ww u -- order
 refine Finset.sum_bij f g (fun i hi z hz h=>Subtype.ext (Subtype.ext ((Q i hi).trans ((congrArg (fun v:Ww.zoo x=> v.val.val) h).trans (Q z hz).symm)))) ?_ ?_
 · intro k hz; obtain ⟨i,hx,u⟩:=h' _ _ u.sym k hz; exact ⟨i,hx,Subtype.ext (Subtype.ext ((Q i hx).symm.trans u.symm))⟩
 intro i v; have hQ:separation o (S.ratio.parent i.val.val.1) ≤ 1:= Tarn.innZ _ _ (mem_filter.mp v).2; have hv':=u.reflected («q»:=q) («β»:=β) (d:=θ) («l»:=l) p hv (Q i v) (aroundBk X hp (by simp only [Nat.add_mul] at *; omega)); exact congrArg₂ (·*·) (congrArg (ansC (S:=S) o) (Q i v)) (congrArg (logGuard q A.vita A.rota) hv')
lemma ivory(s:Signed)(i: Along S)(v: herald S s i=o): Virt S (fle T x q θ (α+γ) l β s i) X:=by
 intro Yw Ww u; let f(U: Monk SU.group S):= pull s 0 U.V; let g(U:Monk SU.group S):= pull s 0 (U.sent x T q θ l β)
 subst o; have ht: Stores.till x≤ b₀:= Nat.div_le_self ..; have hx:Hors.cart x S.patch.L ≤ Stores.till x:= Nat.div_le_self ..
 rcases i with (i | i | i|i)|i|i
 · rfl
 · rfl
 · refine congrArg (- (α+γ)*·) (agreeKing _ _ _ S.patch.L.property _ _ _ _ _ _ (coarse_turn (u.scope (x:=x) (r:=Stores.till x+4+1) ?_ hp).outer)); simp_rw [Nat.add_mul] at *; omega
 · rfl
 · refine gpot S.ratio.parent (Work.E03.parent_step S) _ _ ?_; apply pulled_near; intro e w; exact u.backF p hv e (aroundBk X hp (by change separation (herald S s (.inr (.inl i))) (S.ratio.parent e.1) ≤ Stores.till x+4+1 at w; simp only [Nat.add_mul] at *; omega))
 refine congrArg Neg.neg (gpot id Work.E01.sep_step_le _ _ (coarse_turn ((u.scope (r:=Hors.cart x S.patch.L+4+1) (x:=x) ?_ hp).outer))); simp_rw [Nat.add_mul] at *; omega
lemma zenB : zenA T x q θ (α+γ) l U β A.vita A.rota o=zenA T x q θ (α+γ) l M β A.vita A.rota o:=by
 have hu :Beat (rough U 0) (rough M 0) X:= Cay.coat H.toBeat fun _ _=>rfl; have h:=flickerB A U H p hv o n' hp t; have g{P Q:Monk SU.group S}(p':Beat P Q X): ink T x q θ (α+γ) l β o P=ink T x q θ (α+γ) l β o Q:=congrArg averaged (funext fun i=>sum_congr rfl fun k h=>(ivory A U H p hv o n' hp t i k (mem_filter.mp h).2) p')
 let K':=Beat_k U H.toBeat; unfold zenA flat_w kite; rw [g H.toBeat, g hu, g K',show dua _ _ _ _ _ _ _ _ _ _=_ from h H.toBeat,show dua _ _ _ _ _ _ _ _ _ _= _ from h hu,show dua _ _ _ _ _ _ _ _ _ _=_ from h K']
lemma artB : artU T x q θ l U o=artU T x q θ l M o:=by
 let M1:=kist U; let M2:=kist M; have ht:Beat M1 M2 X:=Beat_k U H.toBeat
 unfold artU porry; refine congrArg₂ (·-·) (Quill_r o p hv (?_) ht) ?_; · exact aroundBk X hp (by rw [separation_self]; simp only [Nat.add_mul] at *; omega)
 apply sum_congr rfl; intro k v; rw [spitB _ _ _ p hv,spitB _ _ _ p hv]; refine sum_congr rfl fun i u=>?_ ; refine congrArg (plant S o i*·) (stencil T A i p hv (fun w=> ?_) ht)
 obtain ⟨hy,hz⟩:= (mem_filter.mp u).2; have hQ:= latticeFieldEstimatesC hz hy w; refine aroundBk X hp ?_; have hh:k<3:= mem_range.mp v; have hk:w.val ≤ 3:=by omega
 have ht':= Nat.mul_le_mul_right (3*b₀) hk; simp only [Nat.add_mul] at *; omega
include v
lemma bluntB : blunt A U o=blunt A M o:=by
 unfold blunt; simp only [gateL U H o n' hp (d:=Vt) (i:=o) (by rwa [separation_self,zero_add])]; split
 next u=>
    have he:Beat.shadows (o:=o) X ((l+68)*b₀):= aroundBk X hp (by rw [separation_self]; simp only [Nat.add_mul] at *; omega); exact congrArg₂ (·+·) (flickerB A U H p hv o n' hp t H.toBeat) (congrArg₂ (·-·) (Quill_r o p hv he H.toBeat) (Quill_r o p hv he (Beat_k U H.toBeat)))
 next u=>exact zenB A U H p hv o n' hp t
end Muster
end YM.CF.Lich
