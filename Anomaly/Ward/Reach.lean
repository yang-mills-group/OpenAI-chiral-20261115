import Anomaly.Ward.Coin
import Anomaly.Ward.Spindle
import YM.Next.RANK.LineBox
/-!
Categorial rooted quadratic slots. Assign at exponent absorbed in
small support cost. Need true pings too even on Lease of Reg.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Next.Rank.Spindle.LampP
open Function Set Filter Metric Lattice Wilson RG Exterior Precision Push Finset
open scoped Topology ContDiff BigOperators Classical
-- Council for all $G$. Also along other valuations not anchored to turn need true Log fields.
variable {b : ℕ} {G:Gauge} {n:Side} (o:Site n) {V:Space G o b}
local notation "Πp" => Directions G n
local notation "Y" => fieldDir G n 1

abbrev rowLine (h:2*(b+1)<n.val): (Turn b→G.Color)→L[ℝ] Πp := (paneExtendLin o).comp (LinearMap.toContinuousLinearMap {
 toFun:=rows 1 h
 map_add':=fun x y=> funext (fun i=>by unfold rows; rw [addstage]; simp only [smul_add]; rfl)
 map_smul':=fun x y=>funext (fun i=>by unfold rows; rw [smulStage,inv_one,one_smul]; simp only [RingHom.id_apply,Pi.smul_apply,one_smul]) })
where addstage (x y : Turn b→G.Color) (l:Word b):stage l (x+y)=stage l x+stage l y:=by
       induction l with
       | nil=> simp [stage]
       | cons a l ih=> simp only [stage,List.map_cons,List.sum_cons] at ih ⊢; rw [ih]; split <;> simp only [*, Pi.add_apply,ite_false,ite_true, ↓reduceIte,neg_add] <;> rw [add_add_add_comm] -- tune
      smulStage (x:ℝ) (y : Turn b→G.Color)(l: Word b):stage l (x • y)=x • stage l y :=by
       induction l with
       | nil=> simp [stage]
       | cons a l ih=> simp only [stage,List.map_cons,List.sum_cons] at ih ⊢; rw [ih]; split <;> simp [*,smul_add]
private lemma stage_fee (p:Word b) (u:Turn b→ G.Color) : ‖stage p u‖ ≤ p.length*‖u‖:=by
 induction p with
 | nil=> simp [stage]
 | cons a l h =>
   have hu : ‖(if a.2 then -u a.1 else u a.1)‖ ≤ ‖u‖:= by split <;> simpa using norm_le_pi_norm u a.1
   exact (norm_add_le _ (stage l u)).trans ((add_le_add hu h).trans_eq (by rw [List.length_cons]; push_cast; ring))
lemma row_fee(h:2*(b+1)<n.val):‖rowLine o (G:=G) h‖ ≤ 4*b := by
 refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun i=>?_
 change ‖paneExtendLin o (rows 1 h i)‖≤_; refine ((paneExtendLin o).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (feeE o) (norm_nonneg _)).trans ?_); rw [one_mul]
 refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j=>?_ ; unfold rows; rw [inv_one,one_smul]; exact (stage_fee _ i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast lengths_word G h j) (norm_nonneg _))
lemma halo_souls (b:ℕ):Fintype.card (Turn b) ≤ (b+b+1)^4 * Fintype.card PlaqAxes:=by
 rw [Fintype.card_coe]; apply le_trans (Finset.card_le_card (Finset.filter_subset _ _)); rw [card_product, Corona.box_size, card_univ]; -- tune
lemma survey (A:Y)(t:ℝ) : represent (t • A)= increment 1 (t • collect G A):=rfl
lemma treeCost{β:ℝ}{U:Config G n}(r: Rules G)(h:0<β)(hv:4*(b:ℝ)*β≤r.c)(he:2*(b+1)<n.val)(hg:Healthy β (halo b {o}) U):
 ∃ (y:Πp), ‖y‖≤ 8*(b:ℝ)*β ∧ Agrees (halo b {o}) (increment 1 y) (spine U o):=by -- tune γ binder erase
 let v:=wired 1 o b U; obtain ⟨p,b',s⟩:= closer r he U hg 1 zero_lt_one h hv; refine ⟨paneExtendLin o v,((paneExtendLin o).le_opNorm v).trans ((mul_le_mul_of_nonneg_right (feeE o) (norm_nonneg _)).trans (?_)),?_⟩; rw [one_mul]; exact p.trans_eq (by ring)
 intro i hv hw; let j:Dim o b:=⟨i,mem_filter.mpr ⟨mem_univ _,hv,hw⟩⟩; change G.lieExp (paneExtendLin o v j.val)*1=_; rw [evaluateE,mul_one]; simpa only [one_smul] using b' j
end YM.Next.Rank.Spindle.LampP
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill
open Nacre Next.Rank.Spindle LampP Exterior Precision
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
variable {b:ℕ}{n:Side}{m:ℕ}{d a w α C:ℝ}{S:Sa n}{W:Toll (Single n)}{F:Raw (Openc (More n) d) (Single n)} (u:Seat n)
local notation "G"=>SU.group
local notation "Πp" => tangD n
local notation "Y" => fieldDir G (More n) 1
variable (p:0<d) (h:Suite (badge _) (bail n d) (bail n d) S W F) (K:mintQ α C d m)(q:2 ≤ m)
include h K q
abbrev fluxJet(p:0<d) (F:Raw (Openc (More n) d) (Single n)):Πp → ℂ:=fun y=>soloQ p F (increment 1 y)-soloQ p F 1
lemma riseN (A:Y) (g:S⊆ halo b {u}) (T:2*(b+1)<(More n).val): trim 2 (fluxJet p F) (collect G A)=trim 2 (fluxJet p F) (rowLine u T (rayFace u A)) :=by
 let B(t:ℝ):= runP A t; let L := rolledZero u A (b:=b)
 let V := collect G A
 let f:= fluxJet p F; let l:=fun x:Πp=>soloQ p F (increment 1 x)
 have hw:= ((penchant p h K (show ‖(0:Πp)‖<α from (show ‖(0:Πp)‖=0 from norm_zero).trans_lt K.1)).order q).smooth
 have hv:ContDiffAt ℝ (2:ℕ) f 0:= hw.sub contDiffAt_const
 have hz: cFoot 2 f:=by
    have hp: fderiv ℝ f 0=0:=by change fderiv ℝ (fun y=> l y - soloQ p F 1) _=_; rw [fderiv_sub_const]; exact zeroD p h (hw.differentiableAt (by norm_num)) K -- tune
    intro i hi; interval_cases i
    · ext1 x; rw [iteratedFDeriv_zero_apply]; change f 0=0; unfold f fluxJet; simp [show increment 1 (0:Πp)=(1:Pane n) from (by funext i; simp [increment])]
    ext1 x; rw [iteratedFDeriv_one_apply,hp]; rfl
 obtain ⟨a,kH,E,w⟩:= rollsBill u A b T
 rw [← show paneExtendLin u (rows 1 T (rayFace u A))=rowLine u T (rayFace u A) from rfl] -- tune
 apply tendsto_nhds_unique_of_eventuallyEq ((argent hv).mp hz V) (flares L hv (kH.of_le le_top) _ a E hz)
 have pα: ∀ᶠ t:ℝ in 𝓝 0, ‖t • V‖<α:=by
    have hv:Tendsto (fun t:ℝ=>t • V) (𝓝 0) (𝓝 0):=by simpa using! (show Continuous (fun t:ℝ=>t • V) from (by fun_prop)).tendsto 0
    exact hv.norm.eventually (gt_mem_nhds (by rw [norm_zero]; exact K.1))
 have pL:∀ᶠ t in 𝓝 0, ‖L t‖<α:=by
    refine kH.continuousAt.norm.eventually (gt_mem_nhds (by dsimp; rw [a,norm_zero]; exact K.1))
 apply Filter.Eventually.filter_mono nhdsWithin_le_nhds; filter_upwards [pα,pL,w] with t hp ht he; unfold f fluxJet; rw [show increment 1 (t • V)=B t from (survey A t).symm]
 let g':= fingers (B t) u; let D:fenceP n d:=⟨B t, (by change Guard (represent (t • A)) d; rw [survey]; exact K.2.2.2.1 _ hp)⟩; let z:fenceP n d:=⟨increment 1 (L t),K.2.2.2.1 _ ht⟩; let X:fenceP n d:=⟨gauge g' D.val,(show Guard D.val d from D.property).cov g'⟩
 rw [show soloQ p F (B t)=soloQ p F X.val from (taxLocal p h D g').symm, show soloQ p F X.val=soloQ p F z.val from ?_]
 exact congrArg Matrix.trace (coinLocal p h (agrees_mono he (coe_subset.mpr g))).symm -- implicit u v
end YM.CF.Swell.Sonar
