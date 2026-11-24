import YM.SU5.LitCurrent.Source
import YM.SU5.LitCurrent.Puff
import YM.SU5.SatinWard.Resolution.Carmel
-- developments after Puff (spec-lift)
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Leaf Buffered
/-!
 Pay Y^circ (pairing-identical to the instrument for harmonized disjoint products).
 Split by subtracting the tails and the failures from the full algebraic expression;
 the latter has zero birth, also *piecewise possible* in this symbol frame since
 using `coinZ` (`-derail`). `ProbeFence` goes before any conjugation through
 the unmarked exponent. For each failed-mask term we only need to pay full, never
 birth at unflagged consultation. `Z'` of (130) which is also in the formula is
 NOT getting an inexpensive standalone payment from this comparison.
-/
variable {P T:SOp N} {p:BudgetPoint}{K:Scree.Loom N}{t u s H:ℝ}{k q l:ℕ}
variable (bI:Chamber.Division)(w:ℝ)(z:Checked p K t d a k q)(x:Site N)(E:Pattern P T r d a v)

variable (CV: DockPulse p K t d a H s l q)(C:Permission P T d)
variable (Yp:Solo a b P d)(Yv:Solo a b T d)
variable {S:SOp N}

local notation "UA"=> (tickA N)
-- perimeter.Sync needs move coupon. support purchases uniformly on ± hits.
local notation "Λ"=> grooveB l p (node x)
local notation "Roof0"=> offsetMask p.B x
local notation "ℒ"=>Fence P T K p q l (node x) H s
variable (hm:p.B+2*r ≤ l*p.B)
-- contact payment/truncation and failures
local notation "S1" x:max=>E.A x
local notation "ω"=>cometPrice l p s H a b r
namespace Chamber
local notation "Ξ"=>legOut l p s H w a b r
abbrev cometKφ(N:Side)(bI:Chamber.Division)(x:Site N)(r:ℕ)(b:Orbit N): FC (Single N):= dg ((hall bI (roomW x r)))-Matrix.trace (tickA _* (hall bI (roomW x r))) • 1
include CV Yp Yv
lemma excessFee : ℒ (cometKφ N bI x r) ω ω:=by
 let h:=soak bI x (room_bill (d:=d) x r CV.hint.le); exact (trimQ H CV Yp Yv h).sub (glowTrace H CV (aura_Y h (Tap.soil_tick a d) CV.hint.le))

lemma gateFee : ℒ (fun U=>kerLocal (P (profile (K U))) (tickA N) ((hall bI (roomW x r))) (T (profile (K U)))) (seaFront l p s H a b r) 0:= spinPlasma H CV Yp Yv ((hall bI (roomW x r))) (soak bI x (room_bill (d:=d) x r CV.hint.le))

local notation "Bc0"=> expiry (4*a) v
local notation "Bc1"=> Real.exp (-a*k)*expiry (4*a) v
local notation "A0"=>blazePlate K (beforePing (grantA bI E x) k)
local notation "A1"=>blazePlate K (beyond (grantA bI E x) k)
abbrev legBeforeφ {v:ℝ}(K:Scree.Loom N)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)(k:ℕ)(i:FaceDir):phy N:=let y:=destSite x r i; heavy w K (beforePing (grantJ bI E (y,i)) k)
local notation "J0"=>legBeforeφ bI K w x E k
abbrev legBeyondφ {v:ℝ}(K:Scree.Loom N)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)(k:ℕ)(i:FaceDir):phy N:=let y:=destSite x r i; heavy w K (beyond (grantJ bI E (y,i)) k)
local notation "J1"=>legBeyondφ bI K w x E k
omit CV Yp Yv
include z
lemma actual_clock : (fun i:Orbit N=> jewelT bI x E K p k w (i.1,K i))=houseK p Roof0 A0+∑ e:FaceDir,houseK p (offsetMask p.B (destSite x r e)) (J0 e)-houseK p Roof0 (cometKφ N bI x r):=by
 funext i; have hu: jewelExcess bI x p r (i.1,K i)=houseK p Roof0 (cometKφ N bI x r) i:=by
   unfold jewelExcess houseK; split
   · rename_i h; rw [Set.indicator_of_mem (show i∈pingMask p Roof0 from h)]
   rename_i h; rw [Set.indicator_of_notMem (show i∉ pingMask p Roof0 from h)]
 have ht: jewelY bI x E K p k (i.1,K i)=houseK p Roof0 A0 i:=by
    unfold jewelY skyHat; dsimp only; rw [noTag x (grantA bI E x) z (E.moorA _)]; unfold houseK; split; next g=> rw [Set.indicator_of_mem (show i∈pingMask p Roof0 from g)]
    next g=> rw [Set.indicator_of_notMem (show i∉ _ from g),Matrix.trace_zero,zero_smul]
 rw [jewelT]; simp only [Pi.sub_apply,Pi.add_apply,Finset.sum_apply,hu,ht]; apply congrArg (·-_); apply congrArg₂ (·+·) rfl; apply sum_congr rfl; intro e _; let y:=destSite x r e; unfold jewelLeg centHat; dsimp only; rw [noTag y (grantJ bI E (y,e)) z (E.moorJ (y,e))]; unfold houseK; split; next g=> rw [Set.indicator_of_mem (show i∈_ from g)]; rfl
 next g=> rw [Set.indicator_of_notMem (show i∉_ from g)]; simp [liftHalf,dg,dyad]
include Yp Yv C
lemma untruncated : A0+A1+ (∑ i:FaceDir,(J0 i+ J1 i))-cometKφ N bI x r=(fun U=>kerLocal (P (profile (K U))) (tickA N) ((hall bI (roomW x r))) (T (profile (K U)))):=by
 funext U; let Z:=roller z.angle z.roof U
 let Y:=P Z.val; let D:= T Z.val; let A := (hall bI (roomW x r)); let O:=Sault.inward Y A D; let M(e:FaceDir):=sky (grantJ bI E (destSite x r e,e)) Z
 have ho : ∑ i:FaceDir,M i=O:= salaryC bI x E Z _ (z.roof.paid U) rfl Yp Yv
 have hp: IsStarProjection Y:= C.projection _ (z.roof.paid U)
 have hO:O.trace=0:= StressExchange.inhibit_nullTrace _ hp (Thera.tag_g D hp)
 have hA: (A0+A1) U= Matrix.trace ((Y-tickA N)*A) • 1:=by
    change Matrix.trace (beforePing (grantA bI E x) k Z.val) • (1:FC I)+ Matrix.trace (beyond (grantA bI E x) k Z.val) • (1:FC I)=_; rw [←add_smul,←Matrix.trace_add,saw_recover,shadows bI x E Z _ (z.roof.paid U) rfl Yp r rfl]
 let L:Op I →+ FC I:=⟨⟨liftHalf w,by simp [liftHalf,dg,dyad]⟩,fun x y=>by change liftHalf w (x+y)=liftHalf w x+liftHalf w y; unfold liftHalf; rw [Matrix.trace_add,dg_add,add_smul,smul_add]; abel⟩
 have ht(i:FaceDir): (J0 i+J1 i) U=L (M i):=by
    change L (beforePing (grantJ bI E _) k Z.val)+L (beyond (grantJ bI E _) k Z.val)=_ ; rw [←map_add,saw_recover]
 have hz:(∑ i:FaceDir,(J0 i+J1 i)) U=dg O:=by rw [Finset.sum_apply]; simp_rw [ht,←map_sum,ho]; change liftHalf w O=_; rw [liftHalf,hO,zero_smul,smul_zero,sub_zero]
 rw [Pi.sub_apply,Pi.add_apply,hz,hA]; rfl
omit z C
omit Yp Yv
local notation "Tail"=> wholeTail l p s H a b w r * Bc1

include CV Yp Yv
lemma tail_clock : ℒ (A1+∑ i:FaceDir,J1 i) Tail Tail:=by
-- still include z? here we don't; k not appears constraint
 have he:= glowTrace (P:=P) (W:=T) H CV (totals (grantA bI E x) CV.hint (E.moorA x) k).2
 have hu(i:FaceDir):=limbFee w x CV Yp Yv (destSite x r i) (totals (grantJ bI E (destSite x r i,i)) CV.hint (E.moorJ (destSite x r i,i)) k).2 (turns_near x i)
 have hg: (∑ i:FaceDir, legOut l p s H w a b r * Bc1)=(Fintype.card FaceDir:ℝ)*legOut l p s H w a b r*Bc1:=by rw [sum_const,card_univ,nsmul_eq_mul]; exact (mul_assoc ..).symm -- ]
 let hT:= he.arc (Fence.sumF univ J1 (fun _=>Ξ * Bc1) (fun _=> Ξ *Bc1) (fun i _=>hu i))
 rw [wholeTail,add_mul,←hg]; exact hT
-- receipts for partial masks (.tee keeps no false S disjoint assumption, only unflagged case fails to recruit the deleted factors)
abbrev missedSeedφ {v:ℝ}(p:BudgetPoint)(K:Scree.Loom N)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)(e:FaceDir):phy N:=legBeforeφ bI K w x E k e-houseK p (offsetMask p.B (destSite x r e)) (legBeforeφ bI K w x E k e)
def missesAllφ (p:BudgetPoint)(K:Scree.Loom N)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v):phy N:= let A':=blazePlate K (beforePing (grantA bI E x) k); (A'-houseK p (offsetMask p.B x) A')+(∑ i:FaceDir, missedSeedφ bI p K k w x E i)-(cometKφ N bI x r-houseK p (offsetMask p.B x) (cometKφ N bI x r))
local notation "L0"=>dropout l p s H a b w v r
include hm
lemma residue : ℒ (missesAllφ bI p K k w x E) L0 0:=by
 have ht: Roof0⊆Λ:= offsetFit x x (by rw [separation_self]; omega) hm
 have he:= Fence.tee (P:=P) (W:=T) (glowTrace H CV (totals (grantA bI E x) CV.hint (E.moorA _) k).1.pay) ht
 have hu(i:FaceDir):=Fence.tee (A:=offsetMask p.B (destSite x r i)) (limbFee w x CV Yp Yv _ (totals (grantJ bI E (destSite x r i,i)) CV.hint (E.moorJ _) k).1.pay (turns_near x i)) (offsetFit x _ (turns_near x i) hm)
 let P':ℝ:=Ξ*Bc0; have hx:= (he.arc (Fence.sumF univ (missedSeedφ bI p K k w x E) (fun _=> P'+P') (fun _=>0) (fun i _=> hu i))).sub (Fence.tee (excessFee bI x CV Yp Yv (r:=r)) ht)
 simp_rw [sum_const,card_univ,nsmul_eq_mul,mul_zero,zero_add] at hx; change ℒ _ _ 0 at hx
 refine hx.smaller (le_of_eq ?_) le_rfl; unfold P' dropout wholeTail; ring
include z C
lemma local_fence : ℒ (fun i:Orbit N=>jewelT bI x E K p k w (i.1,K i)) (seaFront l p s H a b r+Tail+L0) Tail:=by
 let V:= missesAllφ bI p K k w x E; let U:= gateFee bI x CV Yp Yv (r:=r)
 have hx:=actual_clock bI w z x E; rw [hx]
 have hp:=(U.sub (tail_clock bI w x E CV Yp Yv (k:=k))).sub (residue bI w x E CV Yp Yv hm (k:=k)); rw [zero_add,add_zero, ←untruncated bI w z x E C Yp Yv] at hp
 unfold missesAllφ missedSeedφ at hp; rw [sum_add_distrib,sum_sub_distrib] at hp; dsimp only at hp; convert hp using 1; abel
end Chamber
end YM.CF.LitCurrent
