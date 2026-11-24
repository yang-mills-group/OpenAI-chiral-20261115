import Merino.Plume.Murky
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}


variable {o: Seat n} {k:ℕ} {a b d:ℝ} {X:SOp n}

private lemma trench (W:Sa n→Toll I) (p:∑ S:Sa n,rent a S*ledgerV (W S) ≤ b)
    (h:∀ S i j,0≤ W S i j) (ha:0≤a): ∑ S:Sa n,ledgerV (W S) ≤ b:=by
 refine le_trans (sum_le_sum fun S _=>?_) p
 refine le_mul_of_one_le_left (sum_nonneg fun i _=>sum_nonneg fun j _=> h S i j) (Branch.rent_one ha _)
private lemma grove_space {S:Sa n}(l:Grove (terr (More n)) S)(m:o∈S)(g:S.card<k):
    S⊆purse k o:=by
 intro i r
 exact halo_spec.mpr ⟨o,mem_singleton_self _,((l.lim o m i r).trans g).le⟩

lemma ribbon_lip (p:Trunk o X k a b d)(ha:0≤a)(x y:↥(Openc (More n) d)):
   (∑ i:I,∑ j:I,‖X x.val i j-X y.val i j‖) ≤ b*(fare (purse k o) x.val y.val/|d|):=by
 obtain ⟨F,W,h,l,u,v⟩:=p.home
 let δ:=fare (purse k o) x.val y.val/|d|
 have g:0≤δ:=div_nonneg (fare_t ..) (abs_nonneg _)
 apply le_trans _ (mul_le_mul_of_nonneg_right (trench W u (fun S=> (h S).nonn) ha) g)


 calc
  _≤ ∑ i:I,∑ j:I,(∑ S:Sa n,W S i j)*δ:=by
   apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
   rw [v,v,Matrix.sum_apply,Matrix.sum_apply,←sum_sub_distrib,sum_mul]
   refine (norm_sum_le ..).trans (sum_le_sum fun S _=>le_trans (((h S).expo i j).variation x y) ?_)
   by_cases hp: W S=0
   · simp [hp]
   obtain ⟨hu,hv⟩:=l S hp
   apply mul_le_mul_of_nonneg_left _ ((h S).nonn i j)
   exact div_le_div_of_nonneg_right (fare_inc (grove_space (f_then (h S) hp) hu hv) _ _) (abs_nonneg d)
  _ = _:= by
   simp_rw [← Finset.sum_mul,ledgerV,sum_comm (f:=fun (j:I) (S:Sa n)=> _)]

variable {K:Scree.Loom n}{B:BudgetPoint}
lemma joins {V U:Pane n}(r:Skylit B d K)(ha:0≤a)(h:Trunk o X (B.B/10) a b d)
   (v:V∈pass B o)(u:U∈pass B o):
   (∑ i:I,∑ j:I,‖masked K B o X V i j-masked K B o X U i j‖)
    ≤ b*(fare (purse (B.B/10) o) (profile V) (profile U) / |d|):=by
 let τ:=fixedTags n
 rw [masked,Set.indicator_of_mem v,Set.indicator_of_mem u,←fare_local (r.lit v τ) (r.lit u τ)]
 exact ribbon_lip h ha (r.slot _) (r.slot _)


def cable (m:ℕ)(b d:ℝ):=b*capacity m/|d|
lemma cable_pos (m:ℕ)(p:0≤b)(d:ℝ):0≤cable m b d:=
 div_nonneg (mul_nonneg p (cap_pos _)) (abs_nonneg _)
lemma joins_dark {x y:LinksC}{τ:ℝ}
 (r:Skylit B d K)(ha:0≤a)(h:Trunk o X (B.B/10) a b d)(g:B.threshold=τ)
 (v:quiz m τ x=quiz m τ y):
  (∑ i:I,∑ j:I,‖masked K B o X (dark n m x) i j-masked K B o X (dark n m y) i j‖)
    ≤ cable m b d * dist (echoC m x) (echoC m y):=by
 have z:0≤b:=(norm_nonneg _).trans (norm_U h.pay ha (r.slot (1,fixedTags n)))
 by_cases a:dark n m x∈pass B o
 · have u:=lit_dark v B g o a
   refine (joins r ha h a u).trans ((mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (milk _ _) (abs_nonneg d)) z).trans_eq ?_)
   unfold cable; ring
 have u:=mt (lit_dark v.symm B g o) a
 rw [masked,Set.indicator_of_notMem a, Set.indicator_of_notMem u]
 simpa using (mul_nonneg (cable_pos m z d) (dist_nonneg :
       0≤dist (echoC m x) (echoC m y)))

abbrev takeDark (K:Scree.Loom n)(B:BudgetPoint)(o:Seat n)(X:SOp n)(m:ℕ):=
   traceCost K B o X ∘ dark n m


lemma joins_trace {x y:LinksC}{τ:ℝ}
 (r:Skylit B d K)(ha:0≤a)(h:Trunk o X (B.B/10) a b d)(g:B.threshold=τ)
 (v:quiz m τ x=quiz m τ y):
 dist (takeDark K B o X m x) (takeDark K B o X m y)≤
 cable m b d * dist (echoC m x) (echoC m y):=by
 unfold takeDark traceCost
 rw [Function.comp_apply,Function.comp_apply,dist_eq_norm,Matrix.trace,Matrix.trace,← sum_sub_distrib]
 refine (norm_sum_le ..).trans ((sum_le_sum ?_).trans (joins_dark r ha h g v))
 intro i _
 exact single_le_sum (f:=fun j=>‖masked K B o X (dark n m x) i j-masked K B o X (dark n m y) i j‖) (fun _ _=>norm_nonneg _) (mem_univ i)

