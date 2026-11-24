import YM.CF.Hope.Log
import GaugeFieldConstruction.Trebuchet
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hope
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione Beau
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
variable {F G:InkD n}{X₀:Scree.Hub n}
local notation "sR"=> X₀.val.2
local notation "sO"=> X₀.val.1
local notation "Fη"=> (Scree.tariff P sO h)
variable(p:PressB P X₀ F h a)(q:PressB P X₀ G h b)(hv:0 ≤ h)
open Larch
open Py
local notation "ξ"=> (P.order.factorial:ℝ)
local notation "oar"=> (↑N+1:ℝ)
-- Pay tail of log, OFF ping do not pretend it's total exp. Press permits ping override with same copper.
lemma PressExchange (p:PressB P X₀ F h a)(t:PressB P X₀ G h b)(e:∀ U:Pane n,pingS P.threshold sR U → F U=G U): PressB P X₀ F h b:=by
 obtain ⟨w,x,v,c⟩:=t.worth; refine ⟨p.term,p.fitted,p.measureV,p.gaugeV,w,x,fun U t i=>Prism.mint (v U t i) ?_,c⟩
 let K:= Vow.tick (Y:=∅) (X:=sR) (D:=∅) (P:=P) (U:=U) (by simpa only [sdiff_empty] using t)
 let L:= P.threshold⁻¹ • ContinuousLinearMap.id ℝ DN; have hx: Tendsto L (𝓝 0) (𝓝 0):=by simpa only [map_zero] using L.continuous.tendsto 0
 filter_upwards [hx.eventually K] with y t
 have he : pingS P.threshold sR (RG.increment U y):=by change pingS _ (sR\∅) (pressQ P ∅ U _) at t; rwa [sdiff_empty,ploy, show P.threshold • L y= y from smul_inv_smul₀ P.threshold_pos.ne' _] at t
 exact congrArg (fun x:Cipher n=> crumb x.val i) (e _ he).symm
include p in
lemma warp_log (u:1≤h)(s:oar*a ≤1/4) : PressB P X₀ (linen P X₀ F -F) h (2*ξ*(oar*a)^2):=by
 have ht:0 ≤ a:= (Taxi.eraF _ _ p (zero_le_one.trans u) _ (ping_f P _)).grade
 let x:=oar*a; have hz:0≤ x:=by unfold x; positivity
 have hl:x<1:=lt_of_le_of_lt s (by linarith)
 let K(i:ℕ):=fun x'=> bixE (F x') i
 have hf(i):PressB P X₀ (K i) h (ξ*x^(i+1)):=by
    let J:= -F
    have hv:= powerF (ν_P p (zero_le_one.trans u)) (zero_le_one.trans u) (i+1)
    let k:ℝ:=-((1+(i:ℝ))⁻¹); have hp:|k| ≤ 1:=by unfold k; rw [abs_neg,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i])
    rw [show K i=k • (J ^(i+1)) from (by funext x; unfold k K J bixE; rw [neg_smul]; simp)]
    exact hi_p (Ione.scale_E P hv k) (mul_le_of_le_one_left (show 0 ≤ ξ*x^(i+1) by positivity) hp)
 let T':= (fun i:ℕ=> ξ*x^(i+1)); have hh: Summable T':= ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hz hl)).mul_left _
 have hx:∑' i,T' i=ξ *x*(1-x)⁻¹:=by unfold T'; rw [tsum_mul_left]; simp_rw [pow_succ]; rw [tsum_mul_right,tsum_geometric_of_lt_one hz hl]; ring
 let L i:= K (i+1); have hm: Summable fun i:ℕ=>T' (i+1):=(summable_nat_add_iff 1).mpr hh
 have he: PressB P X₀ (caj P _ L) h (∑' i:ℕ,T' (i+1)):= shunt (fun i=>hf (i+1)) u hm
 rw [sub_eq_add_neg]; refine hi_p (PressExchange (Larch.prop_add P X₀ (coy_P p u s).1 (ν_P p (zero_le_one.trans u))) he ?_) ?_
 · intro U i; have hu:visible P sR ∅ U:= hates (by simpa using i)
   unfold linen; rw [Pi.add_apply, pale_p _ hu,pale_p _ hu]; let Z k:=K k U; have hK:Z 0= F U:=by unfold Z K bixE; simp
   change (∑' k,Z k) + -(F U)= (∑' k,Z (k+1)); have hx:Summable Z:= pile_q (u:=T') hf u hh U hu; rw [← hx.sum_add_tsum_nat_add 1, Finset.sum_range_one,hK]; abel
 have hx:∑' i:ℕ,T' (i+1) = ξ *(1-x)⁻¹*x^2:=by change (∑' i:ℕ, ξ*x^(i+1+1))=_; simp_rw [pow_succ]; rw [tsum_mul_left,tsum_mul_right,tsum_mul_right,tsum_geometric_of_lt_one hz hl]; ring
 rw [hx]; have hv:(1-x)⁻¹ ≤ 2:=by rw [inv_le_comm₀ (by linarith only [hl]) (by positivity)]; linarith
 change _ ≤ 2*ξ*x^2; gcongr ?_*_; exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (mul_comm ..)
abbrev snack(p:BudgetPoint)(c:ℝ): ℝ:=p.order.factorial*(Real.exp (((p.order:ℝ)+1)*c)*(((p.order:ℝ)+1)*c))
abbrev turnsP(p:BudgetPoint)(a b:ℝ):ℝ:=p.order.factorial*(((p.order:ℝ)+1)*a*(((p.order:ℝ)+1)*b))
abbrev skewCost(p:BudgetPoint)(a:ℝ):ℝ:= (2:ℝ)*p.order.factorial*(((p.order:ℝ)+1)*a)
-- stencil difference allowance. applies any supports, prices scalar errors ∼x²; no local conditions needed at gauge not on chart. Keep whole F marked.
abbrev ζMark (F G: InkD n)(P:BudgetPoint)(X:Scree.Hub n): InkD n:=linen P X (G+G*(fun u=> NormedSpace.exp (F u)-1 : InkD n))
include p q
lemma ζlemma (u:1≤h)(t:P.order=6)(x b₀:ℝ)(v:turnsP P b (snack P a)≤x)(hp:b+x≤ b₀)(s:7*b₀≤1/4) : let H:=ζMark F G P X₀; PressB P X₀ H h (skewCost P b₀) ∧ PressB P X₀ (H-G) h ((2:ℝ)*ξ*(7*b₀)^2+x) ∧ ∀ U,pingS P.threshold sR U→exp (H U)-1= G U*exp (F U):=by
 intro H;
 let D:= G*(fun u=>NormedSpace.exp (F u)-1:InkD n); let A:=G+D; have hV:0 ≤ h:=zero_le_one.trans u; have hf: PressB P X₀ D h x:=hi_p (peer_P q (ε_P p hV) hV) v; have hh:= hi_p (Larch.prop_add P X₀ q hf) hp; have hz:oar*b₀≤1/4:=by rw [show oar=(7:ℝ) from (by rw [t]; norm_num)]; exact s
 obtain ⟨M,Z⟩:=coy_P hh u hz; refine ⟨M,?_,fun U g=>(Z U g).trans (by change G U+G U*(_-1)=_; ring)⟩
 rw [show H-G= (linen P X₀ A-A)+D from (by unfold H ζMark A D; abel), show (7:ℝ)=oar from (by rw [t]; norm_num)]
 exact Larch.prop_add P X₀ (warp_log hh u hz) hf
omit p q
-- Paths powers auxiliary norms
abbrev reel (o:ℕ)(X:Support (More n)): ℕ:= coverNumber o X*(4*o+2)+2*o
lemma signs3 {f:tangD n→ℂ}(g:Signs P sO f c)(M:ℕ)(p:P.power=2)(u: (f ∘ Mom.screen (G:=E') sR)=ᶠ[𝓝 0] f) : Signs (KeyUp P) sO f ((1+ (reel M sR:ℝ))^P.order*c):=by
 let w:=1+ (reel M sR:ℝ); have hw:1≤w:=by exact le_add_of_nonneg_right (by positivity)
 let A':= Mom.screen (G:=E') sR
 have hh:0≤c:=g.grade; refine ⟨by positivity,g.paid,fun i h V t=> ?_⟩
 rw [← (u.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; change ‖iteratedFDeriv ℝ i (f ∘ A') _ _‖≤_
 rw [jets_linear A' (f:=f) (g.paid.of_le (Nat.cast_le.mpr h))];
 let y(j:Fin i):= A' (V j); change ‖iteratedFDeriv ℝ i f 0 y‖ ≤ _
 apply (Siete.seals g y (fun _=>w) h fun i=>?_ ).trans
 · simp only [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw h) hh
 refine ⟨zero_le_one.trans hw,fun j=>?_⟩; unfold y A'; rw [Mom.screen_at]; split
 next hv =>
    have hu: (1+(separation j.1 sO:ℝ)) ≤ w:= by have ht:separation j.1 sO ≤ reel M sR:= Corona.extent _ _ hv.1 X₀.property; exact add_le_add_right (Nat.cast_le.mpr ht) (1:ℝ)
    apply (t _ _).trans; change P.threshold*(1+_)^3 ≤ w* Lyre.width P sO j; unfold Lyre.width; rw [p]; have hp:=P.threshold_pos; rw [pow_succ]; have he:0 ≤ 1+(separation j.1 X₀.val.1:ℝ):= by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hu (show 0 ≤ P.threshold*(1+(separation j.1 X₀.val.1:ℝ))^2 from mul_nonneg hp.le (pow_nonneg he _))]
 rw [norm_zero]; unfold Lyre.width; have hp:=P.threshold_pos; exact mul_nonneg (zero_le_one.trans hw) (by positivity)
lemma bill3 (t:P.power=2)(M:ℕ)(b:Finset (Dwell n))(u:b∈ Wheat (camp sR))(w:0≤h): Scree.tariff (KeyUp P) sO h b ≤ (1+(reel M sR:ℝ))*Fη b:=by
 let s:=reel M sR; have ht:b⊆ camp sR:= mem_powerset.mp (mem_filter.mp u).1
 have hk:endL sO b ≤ s:= by refine Finset.sup_le fun a g=>?_ ; exact Corona.extent _ _ X₀.property ((mem_filter.mp (ht g)).2)
 unfold Scree.tariff; rw [t,show (KeyUp P).power=3 from rfl, pow_succ, mul_comm (_^2),mul_assoc _ (_^2)]; -- tune
 exact mul_le_mul_of_nonneg_right (add_le_add_right (Nat.cast_le.mpr hk) _) (by positivity)
lemma smallerP (t:P.power=2)(v:PressB (KeyUp P) X₀ F h a)(e:0 ≤ h): PressB P X₀ F h a:=by
 obtain ⟨b,g,y,m⟩:= v.worth; refine ⟨v.term,v.fitted,v.measureV,v.gaugeV,b,g,fun U p i=>?_,(sum_le_sum ?_).trans m⟩
 · let B:=y U p i; refine ⟨g i,B.paid,fun j k z l=> B.3 j k z fun i w=> ?_⟩
   apply (l i w).trans ; change _ ≤ P.threshold*(1+_)^3; rw [t]; gcongr <;> first | exact P.threshold_pos.le | exact (KeyUp P).power_ge | simp
 · intro b _; apply mul_le_mul_of_nonneg_right _ (g _); unfold Scree.tariff; rw [t]; gcongr <;> first | exact P.threshold_pos.le | exact (KeyUp P).power_ge | simp
lemma longer3 (t:P.power=2)(v:PressB P X₀ F h a)(e:0 ≤ h) (M:ℕ) : PressB (KeyUp P) X₀ F h ((1+(reel M sR:ℝ))^(P.order+1)*a):=by
 let D:=(1+(reel M sR:ℝ)); have ht:1≤D:=by exact le_add_of_nonneg_right (by positivity)
 obtain ⟨b,g,y,m⟩:= v.worth; let f:= fun i=> if i∈ Wheat (camp sR) then D^P.order*b i else 0
 refine ⟨v.term,v.fitted,v.measureV,v.gaugeV,f,(fun i=>by unfold f; split; exact mul_nonneg (pow_nonneg (zero_le_one.trans ht) _) (g _); rfl),fun U u i=>?_, le_trans (b:=D^(P.order+1)*(∑ i:Finset (Dwell n),Fη i*b i)) ?_ (mul_le_mul_of_nonneg_left m (by positivity))⟩ -- tune rfl = 0 ≤0
 · unfold f; split
   next h=>
     apply signs3 (y U u _) M t; apply Eventually.of_forall; intro k; simp only [Function.comp_apply]; rw [v.term (RG.increment U _) (RG.increment U k)]; intro i hi hi'; rw [RG.increment,RG.increment,Mom.screen_at, if_pos (show Mom.needed sR i from ⟨hi,hi'⟩)]
   next h => exact Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 from norm_zero.le)) (Eventually.of_forall fun k=> ((v.fitted _).door h).symm)
 rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=> ?_; unfold f; split
 next u=> exact (mul_le_mul_of_nonneg_right (bill3 t M i u e) (mul_nonneg (pow_nonneg (zero_le_one.trans ht) _) (g _))).trans_eq (by unfold D; ring)
 rw [mul_zero]; apply mul_nonneg (by positivity); apply mul_nonneg _ (g _); unfold Scree.tariff; positivity
end YM.CF.Hope
end
