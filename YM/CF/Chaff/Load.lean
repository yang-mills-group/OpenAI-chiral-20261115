import YM.CF.Chaff.Scent
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
variable {r Y V:ℝ}
private abbrev Tun:= Bool × (SpinIdx × SU.Slot)
def mealz:= Fintype.card Tun
lemma foot_M(X: Stamp m B) : (camp (n:=Λ) X).card ≤ X.card*mealz:=by
 let f (i:Dwell Λ): Site ξ × Tun := (node i.2.1.1, i.1,i.2.1.2,i.2.2); have he:Injective f:=by
    rintro ⟨b,⟨⟨x,p⟩,i⟩⟩ ⟨c,⟨⟨y,q⟩,j⟩⟩ v; change (_,_)=(_,_ ) at v; have h:node x=node y:= (Prod.mk.inj v).1; have hv:x=y:=(assembly Λ).embed_injective (add_right_cancel h); simpa only [f,Prod.mk.injEq,hv,true_and] using v -- h.
 rw [← Finset.card_image_of_injective (camp X) he]; let A:= X ×ˢ (univ:Finset Tun); have ht:A.card=X.card*mealz:=by simp [A,mealz]
 refine (card_le_card ?_).trans_eq ht; intro j z; obtain ⟨i,y,rfl⟩:=mem_image.mp z; exact mem_product.mpr ⟨(mem_filter.mp y).2,mem_univ _⟩
lemma paceZ {μ:ℝ}(X:Stamp m B)(T:ℝ)(u:μ*mealz ≤ T)(p:0≤ μ):
 ∑ i∈ (camp (n:=Λ) X).powerset,μ^i.card ≤ rent T X:=by
 let S:=camp (n:=Λ) X; let P:= μ+1; have hp:1≤P:= le_add_of_nonneg_left p
 rw [show ∑ i∈ S.powerset,μ^i.card=P^S.card from ?_]; swap; · simpa only [prod_const] using (Finset.prod_add_one (f:=fun _=>μ) S).symm
 apply ((pow_le_pow_left₀ (zero_le_one.trans hp) (Real.add_one_le_exp μ) _).trans (pow_le_pow_right₀ (Real.one_le_exp p) (foot_M X))).trans
 rw [←Real.exp_nat_mul]; unfold rent; apply Real.exp_monotone; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) X.card] -- tune
private lemma expense_x {T:Finset (Dwell Λ)}(e: T⊆ camp (n:=Λ) S)(P:BudgetPoint)(V:ℝ)(p:0 ≤ V)(u:o∈ S)(q: Grove (terr _) S) : tariff P o V T ≤ (1+ S.card:ℝ)^P.power*V^T.card:=by
 have he:endL o T ≤ S.card:= Finset.sup_le fun i v=> (q.lim _ u _ (mem_filter.mp (e v)).2).le; unfold Scree.tariff; gcongr
def taxH (P:BudgetPoint)(m:ℕ)(C κ:ℝ):ℝ:= if m≤ P.B then composeCost P.order (2*(C+C)*κ^2) 1 else composeCost P.order C (riseH P m)+ C
def buyT (P:BudgetPoint)(m:ℕ)(C H:ℝ)(k:ℕ):ℝ:= composeCost P.order (H⁻¹^k*C) (riseH P m)
abbrev levyP (m B:Side)(P:BudgetPoint)(S:Stamp m B)(C H κ:ℝ)(i:Finset (Dwell (CSide m B))):= if i=∅ then taxH P S.card C κ else if i⊆ camp S then buyT P S.card C H i.card else 0
lemma ψtax (P:BudgetPoint)(n:ℕ)(u:0≤C)(b:ℝ):0 ≤ taxH P n C b:=by
 have he:= P.threshold_pos; unfold taxH; split<;>unfold composeCost<;> try unfold riseH
 all_goals positivity
lemma levy_pos (P:BudgetPoint)(U:Stamp m B)(u:0 ≤ C)(l:0<H)(b:ℝ) :∀ i, 0 ≤ levyP m B P U C H b i:=by
 intro i; unfold levyP; have hp:=P.threshold_pos; split; exact ψtax _ _ u _; split; unfold buyT composeCost riseH; positivity
 exact le_rfl
lemma kernelL {I:Type*}[Fintype I][DecidableEq I]{N:Finset I→ℝ}{P:Finset I}{f:Finset I→ ℝ}(h:∀ i:Finset I, f i≠0 → i⊆P) (u:∀ i⊆P, i≠∅ → f i ≤ N i)(g:0 ≤N ∅): (∑ i:Finset I,f i)≤ f ∅ + ∑ i∈ P.powerset,N i:=by
 let T:=P.powerset; have he:(∅:Finset I)∈T:=by simp [T]
 rw [← sum_subset T.subset_univ (fun x _ g=>by_contra fun i=>g (mem_powerset.mpr (h x i))), ←add_sum_erase _ _ he]; apply add_le_add_right; exact (sum_le_sum (fun i p=>u i (mem_powerset.mp (mem_of_mem_erase p)) (ne_of_mem_erase p))).trans (sum_le_sum_of_subset_of_nonneg (erase_subset ..) (fun i _ g'=>by rw [show i=∅ by contrapose! g'; exact mem_erase_of_ne_of_mem g'.ne_empty ‹_›]; exact g))
def payP(P:BudgetPoint)(u:ℕ):ℝ:= (1+u:ℝ)^P.power
lemma shootB (S:Stamp m B)(p':0≤Y)(k:H>0)(V:ℝ)(hv:0≤V)(pT:0≤r)(ht:r≤1)(l:Y* H⁻¹ ≤ r*V)(u:0≤C)(M:ℕ)(b q:ℝ)(v:V*mealz≤b)(o:Seat Λ)(z:o∈S)(h:Grove (terr _) S):
 (∑ i:Finset (Dwell Λ), Scree.tariff P o Y i * levyP m B P S C H q i) ≤ taxH P S.card C q + r* (rent b S* (payP P S.card * composeCost P.order C (riseH P S.card))):=by
 let α:=composeCost P.order C (riseH P S.card); let Z:=payP P S.card; let L(i:Finset (Dwell Λ)):=Scree.tariff P o Y i*levyP m B P S C H q i
 have hp:0≤α:=by unfold α riseH composeCost; have he:=P.threshold_pos; positivity
 have hZ:0≤ Z:=by unfold Z payP; positivity
 let F(i:Finset (Dwell Λ)):=r* (V^i.card*(Z*α))
 have hf(i:Finset (Dwell Λ))(g:i ⊆ camp S)(hA:i ≠∅): L i≤ F i:=by
    let X:= i.card; have he: H⁻¹^i.card *α = levyP m B P S C H q i:=by unfold levyP buyT; rw [if_neg hA,if_pos g]; unfold α composeCost; ring
    have hw:0 ≤ H⁻¹:= (inv_pos.mpr k).le
    have hy: Y^i.card * H⁻¹ ^i.card ≤ r*V^i.card:=by rw [←mul_pow]; apply (pow_le_pow_left₀ (mul_nonneg p' hw) l _).trans; rw [mul_pow]; exact mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one pT ht (show 1 ≤ i.card from card_pos.mpr (nonempty_iff_ne_empty.mpr hA))).trans_eq (pow_one _)) (pow_nonneg hv _)
    have hh:= expense_x (m:=m) o g P Y p' z h -- B implicit tune args
    unfold L; rw [←he]; calc
     _ ≤ (Z*Y^X)*(H⁻¹^X*α):=mul_le_mul_of_nonneg_right hh (by positivity)
     _ = (Y^X*H⁻¹^X)*(Z*α):=by ring
     _ ≤ _:= (mul_le_mul_of_nonneg_right hy (mul_nonneg hZ hp)).trans_eq (mul_assoc ..) -- assoc
 have hm:= kernelL (P:=camp (n:=Λ) S) (f:=L) (N:=F) (fun i u=>?_) hf (by simp only [F]; positivity); swap; · by_cases h:i=∅; simp [h]; by_contra p; unfold L at u; rw [levyP,if_neg h,if_neg p,mul_zero] at u; exact u rfl
 have he: L ∅ = taxH P S.card C q:=by unfold L Scree.tariff endL; simp [levyP]
 change ∑ i:Finset (Dwell Λ),L i≤ taxH _ _ _ _+r* (rent b S* (Z*α)); rw [he] at hm; refine hm.trans (add_le_add_right ?_ _); unfold F; rw [←mul_sum, ←sum_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (paceZ S b v hv) (mul_nonneg hZ hp)) pT
