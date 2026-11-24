import YM.SU5.Celeste.Ambrosia
import YM.SU5.Celeste.Stanzas
/-! # Flat comparisons BEFORE pruning. tools. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Py Py.Rate Py.Rate.LocalLimit
open Py.Rate.LocalLimit.Papal (Weaver household)
open Signal.Interval (separationCost)
open Buffered.Afterglow
open Buffered.Lifted Ballad Window
open Pannier.Chancel Push.SectorMeasure
variable {N:Side}{S:Finset Cover}{ζ:ℝ}
open Bilinear
variable {R k ℓ d j:ℕ} {B:Side}{s:ℝ}
open Morn
variable {a e C:ℝ}{F G: Weaver}{V W: Finset Cover}{p:ℕ}
lemma levy (h:1≤j)(g: ∀ᶠ N:Side in atTop,Even N.val → Heather 0 p d C e j N)(q: V.card ≤ p)(t: W.card ≤ p)
 (q': Voice F V)(t': Voice G W)(X:∀ (N:Side)(x:Fields N),‖F N x‖≤ C) (Y:∀ (N:Side)(x:Fields N),‖G N x‖≤ C)(q0:Clarity F j s)(t0: Clarity G j s)(v:0≤ s)
 (η:∀ x∈ V,∀ y∈W,d+1≤ Signal.Interval.separationCost x y): Clarity (F*G) j (e+s^2) := by
 filter_upwards [g,q0,t0,distantBook η] with N g h ht he m M x k; let E:= alleyR (mateK N) x; let u:= F N (1,1); let y:= G N (1,1); have hZ:‖E (u*y)-E u*E y‖≤e:= g m M _ _ (card_image_le.trans q) (card_image_le.trans t) he _ _ _ (X N (1,1)) (Y N (1,1)) ((q'.1.bounded N).allV (1,1)) ((t'.1.bounded N).allV (1,1)) k
 change ‖E (u*y)‖≤_; refine (norm_le_norm_sub_add _ (E u* E y)).trans (add_le_add hZ ?_); rw [norm_mul,sq]; exact mul_le_mul (h m M x k) (ht m M x k) (norm_nonneg _) v -- tune apply
lemma normReflect (F:Weaver)(N:Side)(x:Fields N)(a:Axis)(z:ℤ): ‖fluent a z F N x‖=‖F N (reflFields a z x)‖:= (twist_norm ..).trans (norm_cc ..)
lemma normTake (N:Side)(u:∀ x, ‖F N x‖≤ C)(x:Fields N)(a:Axis)(z:ℤ): ‖traction a z F N x‖≤C:=by rw [traction,normReflect,normReflect]; apply u
lemma levy_star (p:Clarity F j s)(h:1≤j)(t:F≠0 ∨ True): Clarity (fluent 3 0 F) j s:=p.turn h 3 0
lemma useful (s:ℝ)(h:0 < s)(p:s≤1/2): s/2+s^2 ≤ s:=by nlinarith
lemma Clarity.far (t:Voice F V)(q:Voice G W)(w:Clarity F j s)(v: Clarity G j s)(B:Side)(x:Axis)(p:0< s)(D:s≤1/2)(h:1≤j):∀ᶠ k in atTop, Clarity (F*Morn.takeoff B G x k) j s:=by
 obtain ⟨c,hc,X⟩:= t.1.rent; obtain ⟨c',hc',Y⟩:=q.1.rent; let C:=max c c'; let Z:=max V.card W.card;
 obtain ⟨d,hZ⟩:=fragments h Z C (hc.trans (le_max_left ..)) (s/2) (half_pos p)
 have hl (k:ℕ): Voice (Morn.takeoff B G x k) (onFlight B W x k):= q.tract x _
 filter_upwards [flown_away B V W x (d+1)] with k e; apply (levy (d:=d) h hZ (le_max_left ..) (card_image_le.trans (le_max_right ..)) t (hl k) (fun N x=> (X N x).trans (le_max_left ..)) (fun N i=> normTake N (fun i=> (Y N i).trans (le_max_right ..)) i _ _) w (v.tract h x _) p.le e).mono; intro N g t M z q; exact (g t M z q).trans (useful s p D) -- eEq.fin holds hyp!
abbrev father(B:Side)(x:Axis)(L:Weaver)(k:ℕ): Weaver:= fluent x 0 (takeoff B L x k)*takeoff B L x k
abbrev claret(B:Side)(S:Finset Cover)(x:Axis)(k:ℕ):= Tower.reflectedBox x 0 (onFlight B S x k)∪ onFlight B S x k
lemma Voice.favor (u: Voice F V)(B:Side)(x:Axis)(k:ℕ): Voice (father B x F k) (claret B V x k):=((u.tract x _).turn x 0).mul (u.tract x _)
lemma Clarity.favor (t: Voice F V)(v: Clarity F j s)(B:Side)(x:Axis)(p:0< s)(D:s≤1/2)(h:1≤j):∀ᶠ k in atTop, Clarity (father B x F k) j s:=by
 obtain ⟨C,he,G⟩:= t.1.rent; let S:= V.card; obtain ⟨k,hK⟩:=fragments h S C he (s/2) (half_pos p)
 filter_upwards [tower_epoch B V x (k+1)] with i e; let W:= onFlight B V x i; let A:= takeoff B F x i; have hp:Clarity A j s:= v.tract h x _; have hl(N:Side)(c:Fields N): ‖A N c‖ ≤ C:= normTake N (G N) c x _; exact (levy h hK (queue_bound (a:=x) B _ _) card_image_le (V:=Tower.reflectedBox x 0 W) (W:= W) ((t.tract x _).turn x 0) (t.tract x _) (fun N c=>(normReflect A N c x 0).trans_le (hl N _)) hl (hp.turn h x 0) hp p.le e).mono fun N t he M x v=> (t he M x v).trans (useful _ p D)
-- prepare contract for an array of Weaver checks, may append
variable {n:ℕ}
structure Ladle (j:ℕ)(B:Side)(ℓ:ℕ)(s:ℝ)(ι:Type)[Fintype ι] where
 label : ι → Weaver
 area : ι→ Finset Cover
 price (i:ι): Voice (label i) (area i)
 clarity(i:ι): Clarity (label i) j s

namespace Ladle
variable {ι γ:Type}[Fintype ι][Fintype γ]
variable (A:Ladle j B ℓ s ι)(W:Ladle j B ℓ s γ)
def tack : Ladle j B ℓ s (ι ⊕ γ) where
 label:= Sum.elim A.label W.label
 area:= Sum.elim A.area W.area
 price i:= by cases i; apply A.price; apply W.price
 clarity i:= by cases i; apply A.clarity; apply W.clarity
abbrev pour(e:ℕ):ι × Bool → Weaver := fun (i,b) => if b then father B 3 (A.label i) e else A.label i
def starlit(e:ℕ):ι × Bool → Finset Cover:= fun (i,b)=>if b then claret B (A.area i) 3 e else A.area i
structure Service (e:ℕ) (p r:ℕ)(C:ℝ) : Prop where
 warm : 0≤C
 gauge (i:ι): Tower.region 3 0 ℓ (onFlight B (A.area i) 3 e)
 seat(i:ι×Bool):Voice (A.pour e i) (insert 0 (A.starlit e i))
 fit_v(i:ι×Bool): Clarity (A.pour e i) j s
 tender(i:ι×Bool)(N:Side)(x: Fields N): ‖A.pour e i N x‖≤C
 smallL(i:ι×Bool) : (insert 0 (A.starlit e i)).card ≤ p
 stan(i:ι×Bool): breadth 0 (insert 0 (A.starlit e i))≤r
lemma orchestra (p:0<s)(D:s≤1/2)(h:1≤j):∃ e p r C,A.Service e p r C:=by
 have he:= Filter.eventually_all.mpr fun i:ι=> Filter.Eventually.and (prepareLaunch B (A.area i) 3 ℓ) (Clarity.favor (A.price i) (A.clarity i) B 3 p D h); obtain ⟨e,y⟩:=he.exists
 let S(i):= insert 0 (A.starlit e i); have ht(i:ι) := A.price i; have h0(i:ι):=(ht i).favor B 3 e; have h1(i:ι×Bool):Voice (A.pour e i) (S i):=by obtain ⟨i,b⟩:=i; cases b; exact (ht i).mono (subset_insert ..); exact (h0 i).mono (subset_insert ..)
 have hv(i:ι×Bool) := (h1 i).1.rent; -- tune
 choose C t f using hv
 have hu(i:ι×Bool):∀ᶠ n:ℝ in atTop,C i≤n:=eventually_ge_atTop _
 obtain ⟨C',⟨g,_⟩⟩:= ((Filter.eventually_all.mpr hu).and (eventually_ge_atTop (0:ℝ))).exists; -- `_` bind fix
 refine ⟨e,univ.sup fun i=> (S i).card,univ.sup (fun i=> breadth 0 (S i)),C',by assumption,fun i=>(y i).1, h1,?_,fun i N x=>(f i N x).trans (g i),fun i=>le_sup (f:=fun i=>(S i).card) (mem_univ _),fun i=>le_sup (f:=fun i=> breadth 0 (S i)) (mem_univ _)⟩
 rintro ⟨i,b⟩; cases b; exact A.clarity i; exact (y i).2
end Ladle
-- assemble the requested trio of goals
namespace Morn
variable (B)(j ℓ:ℕ)(s:ℝ)(h:1≤j)(g:0<s)(u:s≤1/2)
def lastGoal (B:Side)(k i:ℕ)(W:Lead.Clan): Weaver:= fluent 3 0 (leastOne B k W)*takeoff B (leastOne B k W) 3 i
abbrev Trinity:= (Bool ⊕ Unit) × Lead.Clan
abbrev hoy (B:Side)(k t:ℕ): Trinity → Weaver:= fun (x,c)=> match x with
 | .inl true=>leastOne B k c
 | .inl false=>leastTwo B k c
 | .inr _=>lastGoal B k t c
structure Gaze extends Ladle j B ℓ s Trinity where
 hair : ℕ
 fare : ℕ
 bright :0 < hair
 crown : Suit B ℓ hair
 oven : toLadle.label = hoy B hair fare
include h g u
-- avoid universe polym etc.
theorem brought_up: Nonempty (Gaze B j ℓ s):=by
 obtain ⟨k,n,y,f⟩:= (Qualify B ℓ j h s g).exists; let S:=(rayL B k).patio; let U:=Tower.reflectedBox 3 0 S; let r:=S∪U
 obtain ⟨y',fy⟩ := (Filter.eventually_all.mpr fun i:Lead.Clan=> Clarity.far (F:=fluent 3 0 (leastOne B k i)) (G:= leastOne B k i) (V:=U) (W:=S) ((placates_one B k i).turn 3 0) (placates_one B k i) (Clarity.turn h (f i).1 3 0) (f i).1 B 3 g u h).exists
 refine ⟨{hair:=k,fare:=y',bright:=n,crown:=y,label:=hoy B k y',oven:=rfl,area:=fun (x,c)=> match x with
             | .inl true=> S
             | .inl false=>r
             | .inr _=>U∪onFlight B S 3 y'
          ,price:=?_, clarity:=?_}⟩
 · rintro ⟨i,b⟩; have hp:=placates_one B k b; rcases i with (a|_); cases a; apply placates_two; exact hp; exact (hp.turn 3 0).mul (hp.tract 3 _)
 rintro ⟨i,b⟩; rcases i with (a|_); cases a; exact (f b).2; exact (f b).1; exact fy b
end Morn
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.Morn.brought_up
#print axioms YM.CF.Lamour.Bridge.Celeste.Ladle.orchestra
