import YM.SU5.LitCurrent.Source
import YM.SU5.Exchange.Stack.Nest
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
variable (w:ℝ)(z:Checked p K t d a k q)(x:Site N)(E:Pattern P T r d a v)

variable (CV: DockPulse p K t d a H s l q)(C:Permission P T d)
variable (Yp:Solo a b P d)(Yv:Solo a b T d)
variable {S:SOp N}

def heavy (w:ℝ)(p:Scree.Loom N)(V:SOp N):phy N:=firePlate p V- (w:ℂ) • blazePlate p V
local notation "UA"=> (tickA N)

-- perimeter.Sync needs move coupon. support purchases uniformly on ± hits.
local notation "Λ"=> grooveB l p (node x)
local notation "Roof0"=> offsetMask p.B x
local notation "ℒ"=>Fence P T K p q l (node x) H s
variable (hm:p.B+2*r ≤ l*p.B)
abbrev legOut (l:ℕ)(p:BudgetPoint)(s H w a b:ℝ)(r:ℕ):ℝ:=(treeEarnings l p s H a b+‖(w:ℂ)‖ *reefCost l p s H)*Real.exp (a*(4*(2*(r:ℝ))+1))
local notation "Ξ"=>legOut l p s H w a b r
include CV Yp Yv
lemma limbFee (y:Site N)(F:Soak (node y) S a v d)(pD:separation x y ≤ r):
    ℒ (heavy w K S) (Ξ*v) (Ξ*v):=by
 have he:= soak_move F pD CV.hint.le
 have ht:= glowTrace (P:=P) (W:=T) H CV he; have hp:= (trimQ H CV Yp Yv he).sub (ht.scale (w:ℂ))
 apply Fence.smaller hp <;> (unfold legOut; apply le_of_eq; ring)

-- contact payment/truncation and failures
local notation "S1" x:max=>E.A x
abbrev cometK (N:Side)(x:Site N)(r:ℕ)(b:Orbit N):FC (Single N):= dg (roomW x r)-Matrix.trace ((tickA N)*roomW x r) • 1
abbrev cometPrice (l:ℕ)(p:BudgetPoint)(s H a b:ℝ)(r:ℕ):ℝ:=treeEarnings l p s H a b*roomPrice a r+ reefCost l p s H*(2*(Tap.wingRent Fir.Aop a*roomPrice a r))
local notation "ω"=>cometPrice l p s H a b r
lemma excessFee : ℒ (cometK N x r) ω ω:=by
 let h:=room_bill (d:=d) x r CV.hint.le; exact (trimQ H CV Yp Yv h).sub (glowTrace H CV (aura_Y h (Tap.soil_tick a d) CV.hint.le))

abbrev seaFront (l:ℕ)(p:BudgetPoint)(s H a b:ℝ)(r:ℕ):ℝ:=let T:= payΩ a b (roomPrice a r); let V:=reefCost l p s H; V*(2*(T*(Real.exp a+b)))+V*(2*(b*T))
lemma gateFee : ℒ (fun U=>kerLocal (P (profile (K U))) (tickA N) (roomW x r) (T (profile (K U)))) (seaFront l p s H a b r) 0:= spinPlasma H CV Yp Yv (roomW x r) (room_bill (d:=d) x r CV.hint.le)

local notation "Bc0"=> expiry (4*a) v
local notation "Bc1"=> Real.exp (-a*k)*expiry (4*a) v
local notation "A0"=>blazePlate K (beforePing (E.A x) k)
local notation "A1"=>blazePlate K (beyond (E.A x) k)
abbrev legBefore {v:ℝ}(K:Scree.Loom N)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)(k:ℕ)(i:FaceDir):phy N:=let y:=destSite x r i; heavy w K (beforePing (E.J (y,i)) k)
local notation "J0"=>legBefore K w x E k
abbrev legBeyond {v:ℝ}(K:Scree.Loom N)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)(k:ℕ)(i:FaceDir):phy N:=let y:=destSite x r i; heavy w K (beyond (E.J (y,i)) k)
local notation "J1"=>legBeyond K w x E k
omit CV Yp Yv
include z
lemma actual_clock : (fun i:Orbit N=> surrogate K p k w x E (i.1,K i))=houseK p Roof0 A0+∑ e:FaceDir,houseK p (offsetMask p.B (destSite x r e)) (J0 e)-houseK p Roof0 (cometK N x r):=by
 funext i; have hu: excess p x r (i.1,K i)=houseK p Roof0 (cometK N x r) i:=by
   unfold excess houseK; split
   · rename_i h; rw [Set.indicator_of_mem (show i∈pingMask p Roof0 from h)]
   rename_i h; rw [Set.indicator_of_notMem (show i∉ pingMask p Roof0 from h)]
 have ht: gaugeSeed K p k x E (i.1,K i)=houseK p Roof0 A0 i:=by
    unfold gaugeSeed taxHat; dsimp only; rw [noTag x _ z (E.moorA _)]; unfold houseK; split; next g=> rw [Set.indicator_of_mem (show i∈pingMask p Roof0 from g)]
    next g=> rw [Set.indicator_of_notMem (show i∉ _ from g),Matrix.trace_zero,zero_smul]
 rw [surrogate]; simp only [Pi.sub_apply,Pi.add_apply,Finset.sum_apply,hu,ht]; apply congrArg (·-_); apply congrArg₂ (·+·) rfl; apply sum_congr rfl; intro e _; let y:=destSite x r e; unfold fatSeed carrierHat; dsimp only; rw [noTag y _ z (E.moorJ (y,e))]; unfold houseK; split; next g=> rw [Set.indicator_of_mem (show i∈_ from g)]; rfl
 next g=> rw [Set.indicator_of_notMem (show i∉_ from g)]; simp [liftHalf,dg,dyad]
include C
lemma untruncated : A0+A1+ (∑ i:FaceDir,(J0 i+ J1 i))-cometK N x r=(fun U=>kerLocal (P (profile (K U))) (tickA N) (roomW x r) (T (profile (K U)))):=by
 funext U; let Z:=roller z.angle z.roof U
 let Y:=P Z.val; let D:= T Z.val; let A := roomW x r; let O:=Sault.inward Y A D; let M(e:FaceDir):=sky (E.J (destSite x r e,e)) Z
 have ho : ∑ i:FaceDir,M i=O:= E.chimeJ x (K U) (z.roof.paid U) Z rfl
 have hp: IsStarProjection Y:= C.projection _ (z.roof.paid U)
 have hO:O.trace=0:= StressExchange.inhibit_nullTrace _ hp (Thera.tag_g D hp)
 have hA: (A0+A1) U= Matrix.trace ((Y-tickA N)*A) • 1:=by
    change Matrix.trace (beforePing (E.A x) k Z.val) • (1:FC I)+ Matrix.trace (beyond (E.A x) k Z.val) • (1:FC I)=_; rw [←add_smul,←Matrix.trace_add,saw_recover,←E.tax _ _ (z.roof.paid U) Z rfl,tax_eq]; rfl
 let L:Op I →+ FC I:=⟨⟨liftHalf w,by simp [liftHalf,dg,dyad]⟩,fun x y=>by change liftHalf w (x+y)=liftHalf w x+liftHalf w y; unfold liftHalf; rw [Matrix.trace_add,dg_add,add_smul,smul_add]; abel⟩
 have ht(i:FaceDir): (J0 i+J1 i) U=L (M i):=by
    change L (beforePing (E.J _) k Z.val)+L (beyond (E.J _) k Z.val)=_ ; rw [←map_add,saw_recover]
 have hz:(∑ i:FaceDir,(J0 i+J1 i)) U=dg O:=by rw [Finset.sum_apply]; simp_rw [ht,←map_sum,ho]; change liftHalf w O=_; rw [liftHalf,hO,zero_smul,smul_zero,sub_zero]
 rw [Pi.sub_apply,Pi.add_apply,hz,hA]; rfl
omit z C
lemma turns_near (x:Site N)(e: FaceDir): separation x (destSite x r e)≤r:=by rcases e with ⟨i,b⟩; cases b; exact (stopBeam x i r).1; simpa [destSite,gapPlus,strideD,Step.vec,sub_eq_add_neg] using (stopBeam x i r).2

abbrev wholeTail (l:ℕ)(p:BudgetPoint)(s H a b w:ℝ)(r:ℕ):ℝ:= reefCost l p s H+ (Fintype.card FaceDir:ℝ)*legOut l p s H w a b r
abbrev dropout (l:ℕ)(p:BudgetPoint)(s H a b w v:ℝ)(r:ℕ):ℝ:= (2:ℝ)*(wholeTail l p s H a b w r*expiry (4*a) v +cometPrice l p s H a b r)
local notation "Tail"=> wholeTail l p s H a b w r * Bc1

include CV Yp Yv
lemma tail_clock : ℒ (A1+∑ i:FaceDir,J1 i) Tail Tail:=by
-- still include z? here we don't; k not appears constraint
 have he:= glowTrace (P:=P) (W:=T) H CV (totals (E.A x) CV.hint (E.moorA x) k).2
 have hu(i:FaceDir):=limbFee w x CV Yp Yv (destSite x r i) (totals (E.J (destSite x r i,i)) CV.hint (E.moorJ (destSite x r i,i)) k).2 (turns_near x i)
 have hg: (∑ i:FaceDir, legOut l p s H w a b r * Bc1)=(Fintype.card FaceDir:ℝ)*legOut l p s H w a b r*Bc1:=by rw [sum_const,card_univ,nsmul_eq_mul]; exact (mul_assoc ..).symm -- ]
 let hT:= he.arc (Fence.sumF univ J1 (fun _=>Ξ * Bc1) (fun _=> Ξ *Bc1) (fun i _=>hu i))
 rw [wholeTail,add_mul,←hg]; exact hT
-- receipts for partial masks (.tee keeps no false S disjoint assumption, only unflagged case fails to recruit the deleted factors)
abbrev missedSeed {v:ℝ}(p:BudgetPoint)(K:Scree.Loom N)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)(e:FaceDir):phy N:=legBefore K w x E k e-houseK p (offsetMask p.B (destSite x r e)) (legBefore K w x E k e)
def missesAll (p:BudgetPoint)(K:Scree.Loom N)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v):phy N:= let A':=blazePlate K (beforePing (E.A x) k); (A'-houseK p (offsetMask p.B x) A')+(∑ i:FaceDir, missedSeed p K k w x E i)-(cometK N x r-houseK p (offsetMask p.B x) (cometK N x r))
local notation "L0"=>dropout l p s H a b w v r
include hm
lemma residue : ℒ (missesAll p K k w x E) L0 0:=by
 have ht: Roof0⊆Λ:= offsetFit x x (by rw [separation_self]; omega) hm
 have he:= Fence.tee (P:=P) (W:=T) (glowTrace H CV (totals (E.A x) CV.hint (E.moorA _) k).1.pay) ht
 have hu(i:FaceDir):=Fence.tee (A:=offsetMask p.B (destSite x r i)) (limbFee w x CV Yp Yv _ (totals (E.J (destSite x r i,i)) CV.hint (E.moorJ _) k).1.pay (turns_near x i)) (offsetFit x _ (turns_near x i) hm)
 let P':ℝ:=Ξ*Bc0; have hx:= (he.arc (Fence.sumF univ (missedSeed p K k w x E) (fun _=> P'+P') (fun _=>0) (fun i _=> hu i))).sub (Fence.tee (excessFee x CV Yp Yv (r:=r)) ht)
 simp_rw [sum_const,card_univ,nsmul_eq_mul,mul_zero,zero_add] at hx; change ℒ _ _ 0 at hx
 refine hx.smaller (le_of_eq ?_) le_rfl; unfold P' dropout wholeTail; ring
include z C
lemma local_fence : ℒ (fun i:Orbit N=>surrogate K p k w x E (i.1,K i)) (seaFront l p s H a b r+Tail+L0) Tail:=by
 let V:= missesAll p K k w x E; let U:= gateFee x CV Yp Yv (r:=r)
 have hx:=actual_clock w z x E; rw [hx]
 have hp:=(U.sub (tail_clock w x E CV Yp Yv (k:=k))).sub (residue w x E CV Yp Yv hm (k:=k)); rw [zero_add,add_zero, ←untruncated w z x E C] at hp
 unfold missesAll missedSeed at hp; rw [sum_add_distrib,sum_sub_distrib] at hp; dsimp only at hp; convert hp using 1; abel
end YM.CF.LitCurrent
