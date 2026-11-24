import Bay.C.Rook
import YM.CF.Ione.Lark
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks


section
variable {n:Type*}[DecidableEq n][Fintype n]
lemma saucePair (p:Bool)(U:UNI n)(e:Equiv.Perm n)(h:∀ i j,j≠e i→U.val j i=0)(v:Op n)(i j:n):
  sings p U v (e i) (e j)=(U.val (e i) i * star (U.val (e j) j)) * cSignX p (v i j):=by
 rw [singT,twist_formula]
 rw [Matrix.mul_apply,Finset.sum_eq_single j]
 · rw [Matrix.mul_apply,Finset.sum_eq_single i]
   · have c: windX p v i j=cSignX p (v i j):=by cases p<;>rfl
     rw [c,Matrix.star_apply];ring
   · intro x _ d; rw [h _ _ (e.injective.ne d.symm), zero_mul]
   simp
 · intro x _ d; rw [Matrix.star_apply,h x (e j) (e.injective.ne d.symm),star_zero,mul_zero]
 simp
end

def tender (a:ℂ)(p:Bool):ℂ→L[ℝ]ℂ:=if p then a • Complex.conjCLE.toContinuousLinearMap
 else a • ContinuousLinearMap.id ℝ ℂ
lemma tender_t (a:ℂ)(p:Bool)(b:ℂ):tender a p b=a * cSignX p b:=by cases p <;> rfl
lemma tendering {a:ℂ}(t:‖a‖=1)(p:Bool):‖tender a p‖≤1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
 intro b; rw [tender_t,norm_mul,t]
 cases p
 · exact le_rfl
 rw [show cSignX true b=star b from rfl,norm_star]

lemma lensP {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {f:E→ℂ}{k:ℕ}{c:ℝ}(h:Pence k f 0 c)
 (D:E→L[ℝ]E)(Q:ℂ→L[ℝ]ℂ)(p:‖D‖≤1)(q:‖Q‖≤1):
 Pence k (Q ∘ f ∘ D) 0 c:= by
 have ht:ContDiffAt ℝ k f (D 0):= by rw [map_zero];exact h.smooth
 have hk := ht.comp 0 D.contDiff.contDiffAt
 refine ⟨Q.contDiff.contDiffAt.comp 0 hk,
  le_trans (Finset.sum_le_sum fun i j=>mul_le_mul_of_nonneg_left ?_ (by positivity)) h.earned⟩
 have r:(i:ℕ∞ω) ≤ k:=by exact_mod_cast (Nat.lt_succ_iff.mp (mem_range.mp j))
 rw [Q.iteratedFDeriv_comp_left hk r,Push.Uniform.iter_lin_at (ht.of_le r),map_zero]
 exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) q).trans ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=>p)))))

variable {N:Side}
abbrev jersey (s:Sweep N):=sauce s.charge (detX s.s) (socks s)

lemma kitten {n:Type}[DecidableEq n][Fintype n]{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (Q:UNI n)
 (p:Equiv.Perm n)(h:∀ i j, j≠p i→Q.val j i=0) (r:Bool)(D:E→L[ℝ]E)(f:E→Op n)
 (x:ℕ)(c:ℝ)(i j:n)(d:‖D‖≤1)(hp:Pence x (fun y=>f y i j) 0 c):
 Pence x (fun y=>sings r Q (f (D y)) (p i) (p j)) 0 c:=by
 let b:=Q.val (p i) i * star (Q.val (p j) j)
 have a:‖b‖=1:=by unfold b; rw [norm_mul,norm_star,one_fase (h i),one_fase (h j),mul_one]
 apply (lensP (f:=fun y=>f y i j) hp D (tender b r) d (tendering a r)).germ
 exact Filter.Eventually.of_forall fun y=> ((tender_t b r _).trans
  (saucePair r Q p h (f (D y)) i j).symm)

lemma loose {n:Type}[LinearOrder n][Fintype n] (U:UNI n)(w:Rook U.val)(r:Bool): ∃ e:Equiv.Perm (Finset n),
 (∀ i,(e i).card=i.card) ∧ ∀ (D:tangD N→L[ℝ] tangD N)(f:tangD N→FC n)
 (x:ℕ)(c:ℝ)(i j), ‖D‖≤1 → Pence x (fun y=>f y i j) 0 c →
 Pence x (fun y=> sings r (quantU U) (f (D y)) (e i) (e j)) 0 c :=by
 let Q:= quantU U
 obtain ⟨p,g⟩:=Rook.walk w
 have h:∀ i j, j ≠ p.finsetCongr i → Q.val j i=0:=fun i j d=> throne g i j d
 refine ⟨p.finsetCongr,fun i=>card_map _,?_⟩
 intro D f x c i j d hp
 exact kitten (n:=Finset n) (E:=tangD N) Q p.finsetCongr h r D f x c i j d hp

lemma lace (s:Sweep N)(v:Velvet s): ∃ e:Equiv.Perm (Finset (Dwell N)),
 (∀ i,(e i).card=i.card) ∧ ∀ (D:tangD N→L[ℝ] tangD N)(f:tangD N→FC (Dwell N))
 (x:ℕ)(c:ℝ)(i j), ‖D‖≤1 → Pence x (fun y=>f y i j) 0 c →
 Pence x (fun y=> jersey s (f (D y)) (e i) (e j)) 0 c :=by

 exact loose (N:=N) _ ((rook_socks s v).spiced (detX s.s)) _
