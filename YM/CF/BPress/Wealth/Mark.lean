import YM.CF.BPress.Lantern
import YM.CF.BPress.Wealth.Signs
/-!
Apply the base price decomposition on the numerator, after making the authorized Mark scalar extra factor. Keep before-change and after-change function identities, including for any S argument on the debit formula. Leaves ALL non-inChannels factors, with rescaleOffset when used on true stopped history. This is not a noncancellation theorem.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Wealth
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Tunnel Finset RG Wilson
open Law Push.SectorMeasure Env
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
open Tulip Fixed Fock Scree Skye Girt Net Bands Paige Dial
variable {T : Sheet.Atlas}{C C' Lf y : ℝ}{b : ℕ}
section algebra
variable {N : Side}{B : BandWidth}(X:Bands (More N) B)(F:Net (More N) T Lf y C C' b) (s:List X.Index)(A:X.Index→ Theatre N) {K:X.Index→ℝ} (H:∀ i,Extends F X i (A i) (K i))(t:T.Coasts y) {σ c Λ:ℝ}
variable (f:Orbit N→ Phys N) (M:ℕ)(R:PathData group)(d:Clip)(p:BudgetPoint)(β:ℝ)
-- White uses TRUE levy. No overcompensating by adding offsets on `E`. (cost uniform supplied for ledger here, can use Thinner wrapped). Real base account.
def white (i:X.Index) : Theatre N:= fun i'=> ((Real.exp (levy X R d p β M i i'.1)):ℂ) • A i i'
def costW (C D:ℝ)(i:X.Index):= Real.exp (priceMark X d β C D i)*(K i)
variable (D:R.Bounds d σ c Λ){q k:ℝ}
def charged : Prop:= Checks M p d ∧ (Thinner (s:=More N) (totalWeak d R p β M) (fullWeak R p β M) q k ∧ 1≤ M) ∧ 0≤ q∧0≤ β -- X omitted, explicit
include H D
lemma whiteMark (x:charged (N:=N) M R d p β (q:=q) (k:=k))(i:X.Index): Extends F X i (white X A M R d p β i) (costW X (K:=K) d β c k i):=by
 let g:= Real.exp ∘ levy X R d p β M i; have t:= realMarks X R d p β M x.2.1.1 x.1 D x.2.2.1 x.2.1.2 x.2.2.2 i; refine ⟨fun j=> IsMark.factor (c:=fun U=> ↑(g U)) ((H i).mark j) (fun _ _ p=> congrArg (fun r:ℝ=>(Real.exp r:ℂ)) (t.loc _ _ p)) ((Complex.continuous_ofReal.comp Real.continuous_exp).measurable.comp t.meas) (fun U=>?_ ), ((Complex.continuous_ofReal.comp Real.continuous_exp).measurable.comp (t.meas.comp measurable_fst)).smul (H i).meas,fun w U p e h a=>?_⟩ -- tune
 · rw [Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (show 0≤g U from (Real.exp_pos _).le)]; exact Real.exp_monotone ((le_abs_self _).trans (t.price _))
 unfold white; dsimp only; rw [(H i).moves w U p e h, t.inv _ _, twist_scalar]
omit H D

def relieve (x:Orbit N) : Phys N:= ((Real.exp (R.inChannels d p β x.1)):ℂ) • f x
-- retain weak-gauge pieces exactly
variable (S:Finset X.Hcols)(w:Directions group (More N))
def weighM (U:Micro (More N)) := -debtH X M R d p β y -(∑ i ∈ Θ X M S,(second R d M β i w+error M R d p β y w U i)) + (∑ i∈ S,pays X M R d p β y S w U i) - ∑ i, weakRest X R d p β M i U
include D
lemma levy_omit (x:charged (N:=N) M R d p β (q:=q) (k:=k))(U:Micro (More N))(h:R.inChannels d p β U=(∑ x:Face _, hide d p β U x)+(∑ t:Signed, ∑ x, kept d p R β M t U x) + ∑ i,totalWeak d R p β M i U):
 (∑ i:X.Index, levy X R d p β M i U) - R.inChannels d p β U= weighM (y:=y) X M R d p β S w U := by
 unfold weighM; rw [←debit X M R d p β y S w D U, sum_neg_distrib]; rw [balance X R d p β M x.2.1.2 x.2.1.1 U h]; unfold outer; abel
-- apply local inside *and* any exponent debit representation.
lemma white_eq (x:charged (N:=N) M R d p β (q:=q) (k:=k))(u:Orbit N) (h:R.inChannels d p β u.1=(∑ x:Face _, hide d p β u.1 x)+(∑ t:Signed, ∑ x, kept d p R β M t u.1 x) + ∑ i,totalWeak d R p β M i u.1)(v:X.Slates)(he:s.Nodup)(t:∀ i,i∈s):
    encore (T:=T) (y:=y) X s (white X A M R d p β) f v u=(Real.exp (weighM (y:=y) X M R d p β S w u.1):ℂ)* encore (T:=T) (y:=y) X s A (relieve f R d p β) v u:=by
 let B:= R.inChannels d p β u.1; let g:= A; let M' := readout (T:=T) (y:=y) X s A v u.1; let L :=fun i=> levy X R d p β M i u.1; let W:= weighM (y:=y) X M R d p β S w u.1; have ht:= levy_omit (y:=y) X M R d p β D S w x u.1 h -- tune y implicit
 have hz : (( (∏ i:X.Index, ((Real.exp (L i)):ℂ))):ℂ) = (Real.exp W:ℂ)*(Real.exp B:ℂ):=by rw [← Complex.ofReal_prod,←Complex.ofReal_mul,←Real.exp_sum,←Real.exp_add]; congr; change (∑ i,L i)-B=W at ht; linarith -- tune
 have ht: readout (T:=T) (y:=y) X s (white X A M R d p β) v u.1= (∏ i:X.Index,((Real.exp (L i)):ℂ)) • M':=by unfold readout white; simp only; rw [walk_scalar,walk_prod s he t]; rfl
 unfold encore integrand; rw [ht,act_smul]; change inner ℂ _ _ = _ * inner ℂ _ (acts M' ( (Real.exp B:ℂ) • f u)); rw [map_smul,inner_smul_right,inner_smul_right,hz,mul_assoc]
end algebra

-- true label/beta application B History. intermediate, reported with all front hypotheses as lemmas earlier, to be applied after next sector prefactors.
open Vale Vale.Grace Pressure Precision Py Vault
variable {B M s : Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {N0 : ℕ}
  {Mstar : Side}{J:Robes Mstar V W}{q:Push.SectorMeasure.Chi}{h:ℝ}{R0 δ:ℝ→ℝ}{x : ℝ}{j n : ℕ}
local notation "N[" j "]" => cell M B R.L j
variable (u:History V N0 J q h R0 δ x M n)(k:j ≤ n) (G: GapSize)
-- first integration law before giving T powers; exact residual simpler formula no β matching needed yet. Eq:E. use ANY subtraction directions and bad selection (B_T bias window next). integrals well-defined already use full input.
-- can postpone actual statement restructure, but compile now.
include k
theorem first_integral (X:Bands (More N[j]) (G.select (hat R.L x j))) (p:0 < hat R.L x j) (p':xi (hat R.L x j) ≤ 1)(q1:T.Coasts (hat R.L x j))(F: Net (More N[j]) T Lf (hat R.L x j) C C' b)(s:List X.Index)(A : X.Index→ Theatre N[j])(H:X.Index→ℝ)(f:∀ i,Extends F X i (A i) (H i))(t:s.Nodup)(v:∀ i,i∈s)(κ a' C0:ℝ)(l:ℕ)
    (Hp:let r:=u.E j; charged (N:=N[j]) l r.path r.funds r.p r.beta (q:=a') (k:=C0) ∧
    ∀ U:Micro (More N[j]), r.path.inChannels r.funds r.p r.beta U=(∑ x:Face _, hide r.funds r.p r.beta U x)+ (∑ t:Signed, ∑ x, kept r.funds r.p r.path r.beta l t U x)+ ∑ i,totalWeak r.funds r.path r.p r.beta l i U):
    let r:=u.E j; let d:=r.funds; let R':=r.path; let β:=r.beta; let p:=r.p; let A':= white X A l R' d p β; let y:=hat R.L x j
    (∀ i,Extends F X i (A' i) (costW X (K:=H) d β K.top.paths C0 i)) ∧
    reading U r (u.Y j) (F.shows X s A')=∫ x:X.Sky, (∑ i∈X.permit T y (X.atmospheric x), (∫ u':Micro (More N[j]),(∫ t:Ids N[j], (Real.exp (weighM (y:=y) X l R' d p β (chosen X κ y x) (perturb T X κ y x) (F.roll X i x u')):ℂ)*encore (T:=T) (y:=y) X s A (relieve (rescaleOffset U r (u.Y j)) R' d p β) i (F.roll X i x u',t)∂Skye.depot _)∂ Rivet N[j] y))∂X.Rain:=by
 intro r c R' β p'' A' y; obtain ⟨h,w⟩:= Hp; let m:= mantel u k; let q:= m.work; have hc(i):= whiteMark (X:=X) F A f l R' c p'' β q h i -- tune order
 refine ⟨hc, (gate_history u k G X p p' q1 F s A' _ hc t v).2.2.trans ?_⟩; unfold Net.lantern; apply integral_congr_ae; apply Eventually.of_forall; intro x; apply sum_congr rfl; intro i _; refine integral_congr_ae (Eventually.of_forall fun u'=> ?_); refine integral_congr_ae (Eventually.of_forall fun t'=>?_); exact white_eq X s A (rescaleOffset U r (u.Y j)) l R' c p'' β q _ _ h _ (w _) i t v -- tune
end YM.CF.BPress.Wealth
#print axioms YM.CF.BPress.Wealth.first_integral
#print axioms YM.CF.BPress.Wealth.sign_result
#print axioms YM.CF.BPress.Wealth.poise
#print axioms YM.CF.BPress.Wealth.book_cost
#print axioms YM.CF.BPress.Wealth.reg_error
#print axioms YM.CF.BPress.Wealth.mass_lower
#print axioms YM.CF.BPress.Wealth.pay_upper
#print axioms YM.CF.BPress.Wealth.hessian_plan
#print axioms YM.CF.BPress.Wealth.storm_at
#print axioms YM.CF.BPress.Wealth.weak_purchase
#print axioms YM.CF.BPress.Wealth.income
