import GaugeFieldConstruction.Reweave
/-!
# Paw scaled stream (may choose infinite reference lifts)
-/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
abbrev Lane := Kt × Cover
abbrev Dove := Kt → Cover→ Mill→ℂ
def journey (M:Male)(b:Bool)(f:Dove)(x:Cover)(i:Kt)(k:Lane)(t:Mill):ℂ:= Paw 4 M b k.2 i k.1 * f k.1 (x+k.2) t
def streamsW(M:Male)(b:Bool)(f:Dove)(x:Cover)(i:Kt)(t:Mill):ℂ:= ∑' v:Lane,journey M b f x i v t
variable {c f:Side}{G:Ratio c f}{M:Male}{n:ℕ}{b:Bool}
variable {C γ U:ℝ}
def PawnCharge(b:Bool)(n:ℕ):ℝ:= (pawn_p 4 n (by decide) b).choose
lemma PC_pos(k:Bool): 0<PawnCharge k n:= (pawn_p 4 n (by decide) k).choose_spec.1
lemma PC_pay(k:Bool)(i j:Kt): chime (fun x:Cover=>Ladder x^n) (fun x:Cover=>Paw 4 M k x i j) (PawnCharge k n):= (pawn_p 4 n (by decide) k).choose_spec.2 M i j
-- uniform local envelope in shifts; abstract direction P_weight
variable (M b)
def Grove (k:ℕ) (A:ℝ):ℝ:= (Fintype.card Kt:ℝ)*PawnCharge b k*A -- M omit automatic
lemma GroL (k:ℕ)(u:ℝ)(p:0<u):0 < Grove b k u:=by unfold Grove; have hx := PC_pos (n:=k) b; positivity
lemma geo_coin (Y:Dove)(x:Cover)(i:Kt)(n k:ℕ)(a:ℝ)(p:0≤a)(q: ∀ j d, chime (wagN n) (Y j (x+d)) (a*Ladder d^k)) : SumBudget (fun u:Lane×Mill=> wagN n u.2*‖journey M b Y x i u.1 u.2‖) (Grove b k a):=by
 let J(r:Lane)(v:Mill):= wagN n v* ‖journey M b Y x i r v‖; let P (r:Lane):= Paw 4 M b r.2 i r.1; let Vv(r:Lane):= a*(Ladder r.2^k*‖P r‖)
 apply SBprod J (f:=Vv) (fun l=>?_) ?_; swap
 · let Q:=Y l.1 (x+l.2); have he : J l=fun i'=> ‖P l‖*(wagN n i'*‖Q i'‖):=by funext j; change wagN n j* ‖P l * Q j‖=_; rw [norm_mul,mul_left_comm]; -- tune
   rw [he, show Vv l=‖P l‖*(a*Ladder l.2^k) from (by unfold Vv; ring)]; exact SBscale (q ..) (norm_nonneg _)
 let A:= a * PawnCharge b k
 have h(i:Kt) : SumBudget (fun x=> Vv (i,x)) A := SBscale (PC_pay (M:=M) b _ _) p
 have hv:= SBprod (fun i x=> Vv (i,x)) h (show SumBudget (fun _i:Kt=> A) (∑ _i:Kt,A) from ⟨fun i=>SBgoed (h i), (hasSum_fintype _).summable,(tsum_fintype _).le⟩);
 refine SBmono hv (le_of_eq ?_); unfold Grove A; rw [sum_const,card_univ,nsmul_eq_mul]; ring
lemma sum_coin {a:ℝ}(Y:Dove)(x:Cover)(i:Kt)(n:ℕ)(p: SumBudget (fun u:Lane × Mill => wagN n u.2*‖journey M b Y x i u.1 u.2‖) a): Summable (fun u:Lane ×Mill=> ‖journey M b Y x i u.1 u.2‖):= p.2.1.of_nonneg_of_le (fun i=> norm_nonneg _) (fun v=>le_mul_of_one_le_left (norm_nonneg _) (wagE ..)) -- binder a autoImplicit tune
lemma sum_oneF (Y:Dove)(x:Cover)(i:Kt)(n k:ℕ)(a:ℝ)(p:0≤a)(q:∀ j d, chime (wagN n) (Y j (x+d)) (a*Ladder d^k)) (v:Mill) : Summable (fun u:Lane=>‖journey M b Y x i u v‖):= (sum_coin M b Y x i n (geo_coin M b Y x i n k a p q)).prod_symm.prod_factor v
lemma TicketX (Y:Dove)(x:Cover)(i:Kt)(n:ℕ){a:ℝ}(p: SumBudget (fun u:Lane × Mill => wagN n u.2*‖journey M b Y x i u.1 u.2‖) a): chime (wagN n) (streamsW M b Y x i) a:= by
 let g(u:Mill) r:= wagN n u*‖journey M b Y x i r u‖; apply SBqual (SBfold (F:=g) (SBflip p)) (fun x=> mul_nonneg (zero_le_one.trans (wagE ..)) (norm_nonneg _)); intro v; unfold g; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ((sum_coin M b Y x i n p).prod_symm.prod_factor v)) (zero_le_one.trans (wagE ..))

variable {M b}{σ:ℝ}
lemma usb_G (G:Ratio c f) (x d:Cover) : usingF G (x+d) ≤ usingF G x* Ladder d:=by
 let v:=αN G.count; have he:0 ≤ v:= (α_pos _).le; have hp:v≤1:= αsmall _
 have hx:(lateral (x+d):ℝ) ≤ (lateral x:ℝ)+(lateral d:ℝ):= by exact_mod_cast lateral_add x d
 unfold usingF Ladder
 apply le_trans (b:= 1+v*(lateral x + (lateral d:ℝ))) (add_le_add_right (mul_le_mul_of_nonneg_left hx he) _)
 change 1+v*_ ≤(1+v*lateral x)*_; rw [mul_add]; have hc:v*(lateral d:ℝ)≤ lateral d:=mul_le_of_le_one_left (by positivity) hp; nlinarith only [hc,show 0 ≤ v*(lateral x:ℝ)*(lateral d:ℝ) from by positivity]
variable (p:Honed G.count M b U σ)(h:0<U)(u:0<σ)(e:Odd G.count.val) (A:Site f)
abbrev EraM (b:Bool)(n:ℕ)(G:Ratio c f)(U σ:ℝ)(k:ℕ):= Grove b k (BudgetX G σ U n)
lemma EP_V (b:Bool)(n:ℕ)(G:Ratio c f)(U σ:ℝ)(k:ℕ)(v:0<U)(u:0<σ): 0 < EraM b n G U σ k:=GroL b k _ (Bux_pos G U σ v u n)
def sill (M:Male)(G:Ratio c f)(b:Bool)(A:Site f):Dove:=Ytab M G A b
abbrev Sister (M:Male)(G:Ratio c f)(b:Bool)(A:Site f)(x: Cover):= streamsW M b (sill M G b A) x
abbrev SorTex(M:Male)(G:Ratio c f)(b:Bool)(A:Site f)(x: Cover) (i:Kt): Mill→ℂ:= Sister M G b A x i
include p h u
lemma SpringB(x:Cover)(i:Kt)(n:ℕ):SumBudget (fun r:Lane×Mill=> wagN n r.2*‖journey M b (sill M G b A) x i r.1 r.2‖) (EraM b n G U σ n * usingF G x ^ n):=by
 let Q:= BudgetX G σ U n; have he:0 ≤ Q:= (Bux_pos G U σ h u n).le; let R:= usingF G x; have hf:1 ≤ R:=using_v ..; apply SBmono (geo_coin M b (sill M G b A) x i n n (Q* R^n) (by positivity) _); · exact le_of_eq (by unfold EraM Grove Q R; ring)
 intro j d; apply SBmono (slate p h u _ _ _ _); change Q*usingF G (x+d)^n≤ _; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (using_v ..)) (usb_G G x d) n) he).trans_eq (by rw [mul_pow,← mul_assoc])
lemma SB_paws(x:Cover)(i:Kt)(n:ℕ): chime (wagN n) (Sister M G b A x i) (EraM b n G U σ n * usingF G x ^ n):= TicketX _ _ _ _ _ _ (SpringB p h u _ _ _ _)
-- periodize after these estimates
variable (T:Script Male)(Ht:Use 4 G.count T)
include e Ht
lemma naive (x:Cover)(i:Kt)(z:Single c) : flute G e T 4 b M A i x z=∑' t:Cover, (if endLoc G A t=z.1.1 then Rush.wind (deckLoc G A) t*Sister M G b A x i (t,portB z) else 0):=by
 let B:=deckLoc G A; let j:=z.1.1; let a:= portB z -- tune
 let Q(r:Lane)(t:Cover):ℂ:= Paw 4 M b r.2 i r.1 * (if endLoc G A t=z.1.1 then Rush.wind B t*ware G A M b [] (x+r.2) r.1 (t,a) else 0)
 let F(r:Lane)(t:Mill):=journey M b (sill M G b A) x i r t
 have he: Summable (fun r: Lane×Mill=> ‖F r.1 r.2‖):= sum_coin M b _ _ _ 3 (SpringB p h u _ _ _ _)
 have hx(r:Lane)(i:Cover): Q r i= if endLoc G A i=j then Rush.wind B i *F r (i,a) else 0:=by
    unfold Q; split
    next v=>exact mul_left_comm ..  -- tune opacity
    next v=> rw [mul_zero]
 have ht:Summable (Function.uncurry Q):= by
    let L: Lane ×Cover → Lane × Mill:=fun z=>(z.1,(z.2,a)); have hf:=he.comp_injective (i:=L) (show Injective L from (fun i j h=>by simpa [L, ←Prod.ext_iff] using h))
    refine Summable.of_norm_bounded hf fun i=> ?_ ; change ‖Q i.1 i.2‖≤ ‖F i.1 (i.2,a)‖; rw [hx]; split; · rw [norm_mul,show ‖Rush.wind B _‖=1 from Rush.fee_norm _,one_mul]
    rw [norm_zero]; exact norm_nonneg _
 rw [boatT G e T _ b M A (by decide)]; -- denote Paw* tone after shift; rearrange via ht
 let X' (v:Lane):=∑' y,Q v y
 have hv(s:Kt)(y:Cover): Paw 4 M b y i s * toneT G e T 4 b M A s [] (x+y) z=X' (s,y):=by rw [parchment G e A M T Ht]; unfold X'; rw [tsum_mul_left] -- tune
 simp_rw [hv]; rw [show ∑ s:Kt,∑' x:Cover, X' (s,x) = (∑' r:Lane,X' r) from (((show Summable (fun x: Lane=> X' x) from ht.prod).tsum_prod).trans (tsum_fintype _)).symm] -- syntax tune
 rw [show ∑' r,X' r= ∑' v:Cover,∑' r:Lane,Q r v from ht.tsum_comm.symm]
 apply tsum_congr; intro v; simp_rw [hx]; by_cases t:endLoc G A v=j
 · simp_rw [if_pos t]; exact (tsum_mul_left).trans ((if_pos t).symm)
 simp_rw [if_neg t]; unfold j at t; simp [t]
end Boom
end YM.CF.TableF
end
