import Merino.Corolla.Change
import YM.CF.Roots.Hat
import YM.Next.SCHEDULE.Support

set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog

open Roots Lattice.Corona Next.Scheduling
/-- Savings from support to incidence at a prescribed place. -/
abbrev eighth(k:ℕ) := (1:ℝ)+8/(k:ℝ)
abbrev ringSize(b:ℕ):= 8*b*b
def visits(t b:ℕ):ℝ:= (pearl (ringSize b)*t:ℕ)*(∑' j,decay 4 1 j)
variable {n:Side}{I:Type}[Fintype I][LinearOrder I]
variable (P:BudgetPoint)(σ:I→Seat n){t:ℕ}(h:Force_M P.B σ t)
local notation "B"=> P.B
local notation "A"=> ringSize B
variable (y:Seat n)
def ringCount (i:I) := separation y (σ i) / A
local notation "k"=> ringCount P σ y
local notation "fibZ" f:max j:max => Finset.univ.filter fun x=> f x=j
include h in
lemma holdCount(v:Seat n): (fibZ σ v).card ≤ t:=by
 refine le_trans ?_ (h.2 v)
 apply Finset.card_le_card
 intro i u
 obtain ⟨u,e⟩:=mem_filter.mp u
 simp [reach_B,e]


lemma loopPos:0 < ringSize B:=by have := P.B_pos; unfold ringSize; positivity
lemma ringBound(i:I)(X:Aura n)(e:σ i∈X.val)(v:y∈X.val): k i * B ≤ coverNumber B X.val :=by
  have hB:=P.B_pos
  have hu:1 ≤ coverNumber B X.val := by
    exact_mod_cast (vigor n B).pos X
  have hx:= extent _ B v e
  have hw:=Nat.div_mul_le_self (separation y (σ i)) A
  have hh0:2*B ≤ coverNumber B X.val*(2*B):=Nat.le_mul_of_pos_left _ hu
  have hh1:=Nat.mul_le_mul_left (coverNumber B X.val) (show 6*B+2≤8*B by omega)
  refine Nat.le_of_mul_le_mul_right ?_ (show 0<8*B by positivity)
  unfold ringCount
  have hh:∀ z, z*B*(8*B)=z*A:= by intros; unfold ringSize; ring
  rw [hh]
  exact hw.trans (hx.trans (by nlinarith only [hh0,hh1]))

include h
lemma priceRing(j:ℕ):
   (fibZ k j).card ≤ (pearl A*t)*(j+1)^4:=by
 let S:=Lattice.halo ((j+1)*A) {y}
 have hp:(fibZ k j) ⊆ S.biUnion (fun v=> fibZ σ v):=by
   intro i e; apply mem_biUnion.mpr
   refine ⟨σ i,halo_spec.mpr ⟨y,mem_singleton_self _,?_⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
   have hm: k i < j+1:= ((mem_filter.mp e).2: k i=j) ▸ Nat.lt_succ_self _
   exact ((Nat.div_lt_iff_lt_mul (loopPos P)).mp hm).le

 have hm:=sum_le_sum (s:=S) (g:=fun _=> t) (fun x _=>holdCount P σ h x)
 refine ((card_le_card hp).trans card_biUnion_le).trans ?_
 rw [sum_const,smul_eq_mul] at hm
 have hx: S.card ≤ ( ((j+1)*A)+ ((j+1)*A)+1)^4 := ball_v .. 
 refine hm.trans ((Nat.mul_le_mul_right t hx).trans ?_)
 rw [mul_right_comm,pearl,← mul_pow]
 exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by nlinarith) _)
lemma rings: (∑ i:I,Real.exp (- (k i:ℝ))) ≤ visits t B :=by
 let S:= univ.image k
 rw [←sum_fiberwise_of_maps_to (t:=S) (g:=k) (fun i w=>mem_image_of_mem _ w)]
 unfold visits
 refine le_trans ?_ (mul_le_mul_of_nonneg_left ((decay_summable 4 1 one_pos).sum_le_tsum S
      (fun j _=>by unfold decay; positivity)) (by positivity : 0≤ ((pearl A*t:ℕ):ℝ)))
 rw [mul_sum]; refine sum_le_sum fun j _=> ?_
 let Z := (fibZ k j)
 rw [show (∑ i∈Z, Real.exp (- (k i:ℝ)))= (∑ _i∈Z, Real.exp (- (j:ℝ))) from
        sum_congr rfl fun i e=>by rw [(mem_filter.mp e).2],
      sum_const,nsmul_eq_mul]
 refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (priceRing P σ h y j)) (Real.exp_pos _).le).trans_eq ?_
 unfold decay; push_cast; ring_nf


variable (Q:I→Aura n→ℝ) (u:ℝ)
lemma richVisits (hp:0≤u)(hn:∀ i,0 ≤ Q i)
    (hw:∀ i X, Q i X≠0→σ i∈X.val)
    (ht:∀ i,voyageB (Q i) B (eighth B) ≤u):
    nook ((∑ i,Q i)*tact (satin B) B) y ≤ visits t B *u:=by
 refine le_trans ?_ (mul_le_mul_of_nonneg_right (rings P σ h y) hp)
 unfold nook; simp_rw [Pi.mul_apply,Finset.sum_apply,sum_mul]; rw [sum_comm]
 refine sum_le_sum fun i _=>le_trans ?_ (mul_le_mul_of_nonneg_left (ht i) (Real.exp_pos _).le)
 rw [voyageB,mul_sum]
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ (spark y)) (fun X _ _=>
      mul_nonneg (Real.exp_pos _).le (mul_nonneg (hn i X) (Real.exp_pos _).le)))
 refine sum_le_sum fun X e=>?_
 by_cases w:Q i X=0
 · simp [w]
 have hc:y∈X.val:= (mem_filter.mp e).2
 have hR:(k i:ℝ)*P.B ≤ widthK n B X:= by exact_mod_cast ringBound P σ y i X (hw i X w) hc
 rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (hn i _)
 unfold tact; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr
 have he:(k i:ℝ) ≤ widthK n B X / B:= (le_div_iff₀ (bpos P)).mpr hR
 unfold satin eighth; simp_rw [div_eq_mul_inv] at he ⊢; linarith only [he]

end YM.CF.Merino.Corolla

