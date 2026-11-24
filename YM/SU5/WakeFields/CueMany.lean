import YM.SU5.WakeFields.Players
import YM.SU5.WakeFields.Ferro
import YM.SU5.WakeFields.SpinShot
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.EmberWind
open Finset Function Filter NormedSpace SU Lat Lattice Cube MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
        ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch
        Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Hiro
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel
open WakeInvestment

namespace MixedCards.Receipt
open Ballad (Twah)
open Crossing (Story)
variable {J : Type*} (L : List J)
variable (D : J → Ticket) (U : J → Staff)
local notation "Q" => SU.group.ColorIndex
abbrev pad (p:Q) : ColorL:= EuclideanSpace.single p 1
local notation "ℵ" => SU.Slot
abbrev Deck (J : Type*) := List (materialL J)
abbrev with2 (H:Story J) (i:J)(p k : SU.Slot) : Story J:= H++[(i,k,true),(i,p,false)]
abbrev dyeC (p:Q)(i k: SU.Slot) :ℂ:= colorEntry i k (pad p)

-- Note universe : `cost` ℂ not norm price.
def cue (D:J→Ticket)(F:Deck J→Story J → ℂ) (L:List J)(G:Deck J)(H: Story J) : ℂ := match L with
 | []=> F G H
 | i::t=> match D i with
   | some a => ∑ b∈ colors a,(1/16:ℂ)*cue D F t G (with2 H i b b)
   | none => ∑ p:Q,∑ j:ℵ,∑ k:ℵ,dyeC p j k*cue D F t (G++[(i,p)]) (with2 H i j k)

variable (G : Deck J) (H : Story J)
variable {F:Deck J→ Story J → ℂ}
lemma payMix {i:J} (u:D i=none) : cue D F (i::L) G H=∑ p:Q, ∑ j:ℵ,∑ k:ℵ,dyeC p j k*cue D F L (G++[(i,p)]) (with2 H i j k) := by rw [cue, u]
lemma payPure {i:J} {a : Lead.Clan} (u:D i=some a) : cue D F (i::L) G H= ∑ b∈ colors a,(1/16:ℂ)*cue D F L G (with2 H i b b) := by rw [cue,u]

variable {V : Type*}[NormedAddCommGroup V][InnerProductSpace ℝ V][MeasurableSpace V][BorelSpace V][FiniteDimensional ℝ V]
open Regis.Resonance ProbabilityTheory
variable (B : materialL J → V) (y:V)
local notation "µ" => stdGaussian V
variable (n : Side) (T : FC (Single n) →ₗ[ℂ] ℂ)
abbrev fixedArc (x:V) : J→ ColorL := fun i => WithLp.toLp 2 (fun j=> inner ℝ (B (i,j)) x)
abbrev rungB (G:Deck J) (x:V) := (↑(payday (G.map B) x):ℂ)

def residue (y : V) := judged U D L n (fixedArc B y)
abbrev roll (U:J→Staff)(n:Side) : Story J → FC (Single n) := rollC (Flare.ton∘Crossing.rack (Staff.u∘U) (Staff.spin∘U) 1 n)
abbrev GAfee (G:Deck J) := (memo (G.map B):ℂ)
abbrev goods (y:V) := rungB B G y * T (roll U n H * residue L D U B n y)

lemma brand (i:ℵ)(k:ℵ)(x:ColorL) : colorEntry i k x=∑ a:Q,(x a:ℂ)*dyeC a i k:=by
  -- decompose
  let b:= EuclideanSpace.basisFun Q ℝ
  have hx: (∑ i:Q,x i • pad i)=x:=by simpa [pad,b,EuclideanSpace.basisFun_apply] using (b.sum_repr x) -- may not simp b
  nth_rw 1 [←hx]; rw [map_sum]; apply sum_congr rfl; intro a _; rw [map_smul]; rfl

abbrev countSale (i:J)(p k : SU.Slot) : FC (Single n) := Hiro.sold 1 (U i).u (U i).spin p k

lemma pureSlot (i:J) (V: Staff) (k:Lead.Clan)(c:ColorL) :
    play V (some k) n c= ∑ p∈colors k,(1/16:ℂ) • Hiro.sold 1 V.u V.spin p p := by
  clear i
  obtain ⟨hub,u,z,spin,steps,e⟩:=V; cases spin with | mk m t=>
  have he := Twah.bouquet (R:=1) (N:=n) (unifyT u (m,t)) k
  rw [SitSpin.in_Twah] at he; norm_num only [Nat.cast_one,one_pow,one_smul] at he
  change (1/16:ℂ) • SitSpin.raw u k m t n (1,1) = _; rw [he]; exact smul_sum .. -- argument syntax
lemma colorSlot (i:J) (h:D i=none) (x:V) :
    play (U i) (D i) n (fixedArc B x i)=∑ q:Q,∑ j:ℵ,∑ k:ℵ, (dyeC q j k* (inner ℝ (B (i,q)) x:ℂ)) • countSale U n i j k:= by
  rw [h,play,tomato]
  let F (q:Q) (j k:ℵ): FC (Single n):= ((↑(inner ℝ (B (i,q)) x):ℂ) * dyeC q j k) • (countSale U n i j k)
  -- commute color sums
  simp_rw [brand _ _ (fixedArc B x i),sum_smul]
  simp_rw [mul_comm (dyeC _ _ _)]
  change ∑ j:ℵ,∑ k:ℵ,∑ q:Q, F q j k = ∑ q:Q,∑ j:ℵ,∑ k:ℵ,F q j k
  rw [sum_comm (s:= (univ:Finset Q))]; apply sum_congr rfl; intro i _; rw [sum_comm]

lemma rolling (i:J)(j k:SU.Slot): roll U n (with2 H i j k) = roll U n H * countSale U n i j k := by
  unfold roll rollC with2; simp only [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl
lemma residue_cons (i:J)(x:V) : residue (i::L) D U B n x = play (U i) (D i) n (fixedArc B x i)*residue L D U B n x:=rfl
lemma paving (j: materialL J)(x:V) : rungB B (G++[j]) x = (↑(inner ℝ (B j) x):ℂ)*rungB B G x := by
  unfold rungB payday; simp [mul_comm]

lemma accompany {i:J} {a:Lead.Clan} (u:D i=some a)(y:V) : goods (i::L) D U G H B n T y= ∑ b∈colors a,(1/16:ℂ) * goods L D U G (with2 H i b b) B n T y := by
  unfold goods; rw [residue_cons,u,pureSlot _ i] -- tune
  simp_rw [sum_mul,mul_sum,Matrix.smul_mul,Matrix.mul_smul,map_sum,map_smul,smul_eq_mul,mul_sum,rolling]
  apply sum_congr rfl; intro j _; rw [mul_assoc (roll U n H) (countSale U n i j j) (residue L D U B n y)]; unfold countSale; ring

lemma accompanying {i:J} (u:D i=none)(y:V) : goods (i::L) D U G H B n T y=∑ a:Q, ∑ j:ℵ,∑ k:ℵ, dyeC a j k * goods L D U (G ++ [(i,a)]) (with2 H i j k) B n T y := by
  unfold goods; rw [residue_cons,colorSlot]
  · simp_rw [sum_mul,mul_sum,Matrix.smul_mul,Matrix.mul_smul,map_sum,map_smul,smul_eq_mul,mul_sum,rolling]
    apply sum_congr rfl; intro q _; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=>?_
    rw [mul_assoc (roll U n H) (countSale U n i j k) (residue L D U B n y), paving]; ring
  exact u

lemma budget : Integrable (goods L D U G H B n T) µ:= by
  induction L generalizing G H with
  | nil=> exact ((payday_val (G.map B)).accepted.ofReal (𝕜:=ℂ)).mul_const (T (roll U n H * 1)) -- tune
  | cons i L ih=>
    cases h:D i with
    | some a=> rw [funext (fun y=> accompany L D U G H B n T h y)]
               exact integrable_finsetSum _ (fun i _=> (ih _ _).const_mul _)
    | none=> rw [funext (fun y=> accompanying L D U G H B n T h y)]; exact integrable_finsetSum _ fun _ _=> integrable_finsetSum _ fun i _=> integrable_finsetSum _ fun j _=> (ih _ _).const_mul _

abbrev defaultPrice (G:Deck J) (H:Story J) := GAfee B G * T (roll U n H) -- order arg B before G?

lemma real_body : (∫ y,goods L D U G H B n T y∂µ) = cue D (defaultPrice U B n T) L G H:=by
  induction L generalizing G H with
  | nil=> change (∫ y, rungB B G y * T (roll U n H*1) ∂µ) = _; rw [mul_one,integral_mul_const, cue]; unfold rungB; rw [integral_complex_ofReal]
  | cons i L ih=>
    cases h:D i with
    | some a=>
      simp_rw [accompany L D U G H B n T h]; rw [payPure L D G H h, integral_finsetSum _ fun _ _=> (budget L D U _ _ B n T).const_mul _]
      simp_rw [integral_const_mul,ih]
    | none=>
      simp_rw [accompanying L D U G H B n T h]; rw [payMix L D G H h];
      rw [integral_finsetSum]; swap; · exact fun _ _=> integrable_finsetSum _ fun _ _=> integrable_finsetSum _ fun _ _=> (budget L D U _ _ B n T).const_mul _
      apply sum_congr rfl; intro j _; rw [integral_finsetSum]; swap; · exact fun _ _=> integrable_finsetSum _ fun _ _=> (budget L D U _ _ B n T).const_mul _
      apply sum_congr rfl; intro k _; rw [integral_finsetSum]; swap; · exact fun _ _=> (budget L D U _ _ B n T).const_mul _
      simp_rw [integral_const_mul,ih]

abbrev bus (GG:materialL J→materialL J→ℂ) (SS:Twah.Stamp J→ Twah.Stamp J→ℂ) := cue D (fun G H=> WakeFields.Ferro.ledger GG G * Emu.runes SS H) L G H
lemma bullion {j:ℕ}{M:Jill.Male} (p:1≤j)(t:Kea.Pad j n)(x:Wave (Single n))(l:Sea (Dial.spar j M (1:Pane n)) x) :
    let T:= Lamour.alleyR (Dial.mateK n) x
    (∫ y,goods L D U G H B n T y∂µ) = bus L D G H (fun i k=>(↑(inner ℝ (B i) (B k)):ℂ)) (Crossing.covRead j 1 (Staff.u∘U) (Staff.spin∘U) n M):=by
  intro T; rw [real_body]; unfold bus; apply congrArg (fun F=>cue D F L G H); funext G H
  rw [defaultPrice,WakeFields.Ferro.truePrice _ _ _ le_rfl] -- tune direction
  exact congrArg (_ * ·) (Crossing.chosen j (Staff.u∘U) (Staff.spin∘U) 1 p t _ l H)

#print axioms rolling
#print axioms defaultPrice
#print axioms real_body
#print axioms payPure
#print axioms budget
#print axioms bullion
-- counting weights: keep gauge first and count every ticket. Use `scalecost` nat weight instead of length filter. generalized motions consume Pairwise on ALL slots or generalized pairwise on subfilter.
def volumeFee : Ticket → ℕ
 | some _ => 3 | none => 5
abbrev scaleFee (D:J→Ticket)(L:List J) := (L.map (volumeFee ∘ D)).sum
lemma volumePure {i:J}{Z : Lead.Clan} (h:D i=some Z) : scaleFee D (i::L)=3+scaleFee D L := by simp only [scaleFee,List.map_cons,List.sum_cons, comp_apply,h]; rfl
lemma volumeColor {i:J}(h:D i=none) : scaleFee D (i::L)=5+scaleFee D L := by simp only [scaleFee,List.map_cons,List.sum_cons, comp_apply,h]; rfl
variable (P:materialL J→materialL J→ℂ)(W:Twah.Stamp J→ Twah.Stamp J→ℂ)
lemma bright_bus (m:ℕ)(h:H.length=m*2)(x:ℂ): bus L D G H (fun i j=> x^4*P i j) (fun i j=>x^3*W i j)=
    x^(scaleFee D L+2*G.length+3*m)*bus L D G H P W := by
  induction L generalizing G H m with
  | nil=> unfold bus; rw [cue,cue, Crossing.rune_factor _ _ h, show (4:ℕ)= 2*2 from rfl, pow_mul x,
                                      WakeFields.Ferro.multiplier _ _ _ _ le_rfl]; change _ = x^(0+2*G.length+3*m)*_
          rw [zero_add,pow_add,pow_mul x 2,pow_mul]; ring
  | cons i L ih =>
    unfold bus; cases g:D i with
    | none=> rw [volumeColor L D g,payMix L D G H g,payMix L D G H g]
             simp_rw [mul_sum]; refine sum_congr rfl (fun p _=> sum_congr rfl fun j _=>sum_congr rfl fun k _=>?_)
             change dyeC _ _ _*bus L D _ _ _ _ = _
             rw [ih _ _ (m+1) (by unfold with2; simp [h]; omega),show scaleFee D L+ 2 * (G++[(i,p)]).length + 3*(m+1) = (5+scaleFee D L)+2*G.length+3*m from (by simp; omega)]
             unfold bus; ring
    | some a=> rw [volumePure L D g,payPure L D G H g,payPure L D G H g,mul_sum]
               refine sum_congr rfl fun j _=> ?_; change (1/16:ℂ)*bus L D _ _ _ _ = _
               rw [ih _ _ (m+1) (by unfold with2; simp [h]; omega),show scaleFee D L+ 2 * G.length + 3*(m+1) = (3+scaleFee D L)+2*G.length+3*m from (by omega)]
               unfold bus; ring

variable {α : Type*} (A : Filter α)
lemma busLimit {M:J→ J→Prop} (t:(G.map Prod.fst ++ L).Pairwise M)
    {P':α→materialL J→materialL J→ℂ}(h:∀ (i j:materialL J), M i.1 j.1 →
      Tendsto (fun n=> P' n i j) A (𝓝 (P i j))) {S':α→Twah.Stamp J→ Twah.Stamp J→ℂ}
    (w:∀ i j,Tendsto (fun n=>S' n i j) A (𝓝 (W i j))) :
    Tendsto (fun n=> bus L D G H (P' n) (S' n)) A (𝓝 (bus L D G H P W)) := by
  induction L generalizing G H with
  | nil=> rw [List.append_nil] at t
          exact (WakeFields.Ferro.motions P G A _ (fun i j=> M i.1 j.1) G.length le_rfl (List.pairwise_map.mp t) h).mul (Crossing.rune_ride A W _ w H)
  | cons i L ih=>
    unfold bus; cases g:D i with
    | none=> simp_rw [payMix L D G H g]; exact tendsto_finsetSum _ fun p _=> tendsto_finsetSum _ fun j _=> tendsto_finsetSum _ fun k _=> (ih (G++[(i,p)]) (with2 H i j k) (by simpa [List.append_assoc] using t)).const_mul _
    | some a=> simp_rw [payPure L D G H g]; exact tendsto_finsetSum _ fun j _=> (ih _ (with2 H i j j) (t.sublist ((List.Sublist.cons i (List.Sublist.refl _)).append_left _))).const_mul _

#print axioms bright_bus
#print axioms busLimit
end MixedCards.Receipt
end YM.CF.Buffered.EmberWind
