import PF.Material
import PF.Near
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce
namespace Pose
open BPress Spin Branch Pec
variable {n:Side}
local notation "I'"=> Single n
local notation "G5"=> SU.group
local notation "X"=> Seat n
-- $D needle, node. Portal
-- bring two threshold portals; stronger Cube.Guard domain, e radius uniform.
local notation "cap" e => Spin.OpenW n e
open Tenant Material Dial
variable (v:gaugeLink n)(b:Bool)
-- use exact lie generator, not fixed learning

def swing (z:SU.group.Color) (V:Pane n):Pane n:= oneOffer v (if b then 1 else SU.group.lieExp z) (if b then (SU.group.lieExp z)⁻¹ else 1) V
private lemma euler : ∃ c:ℝ,0<c ∧∀ z:SU.group.Color, SU.group.chord (SU.group.lieExp z) ≤ c * ‖z‖ :=by
 obtain ⟨D,η,h,g,p⟩:= Next.Fluctuations.chord_chart_cost SU.group
 refine ⟨D+2/η,by positivity,fun z=>?_⟩; by_cases hv:‖z‖ ≤ η
 · exact (p z hv).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (norm_nonneg _))
 exact (SU.group.chord_le_two _).trans ((le_trans (le_of_eq (show (2:ℝ)= (2/η)*η by field_simp)) (mul_le_mul_of_nonneg_left (le_of_not_ge hv) (by positivity))).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h.le) (norm_nonneg _)))

def Λ:ℝ:=euler.choose
lemma hr : 0 < Λ:=euler.choose_spec.1
lemma swing_buy (z:SU.group.Color)(V:Pane n)(i:gaugeLink n) : BPress.chord (swing v b z V i) (V i) ≤ Λ * ‖z‖:= by
 unfold swing; refine (one_cost (e:=v) _ _ V i).trans ?_; cases b <;> simpa [Λ] using euler.choose_spec.2 z
lemma swing_local (z:SU.group.Color) {F:Support (More n)}{U V:Pane n}(p: Agrees F U V) : Agrees F (swing v b z U) (swing v b z V) := one_agrees _ _ p
lemma swingC : Continuous (fun (p: SU.group.Color × Pane n)=> swing v b p.1 p.2) := by
 refine continuous_pi fun i=> ?_; by_cases h:i=v
 · subst i; unfold swing; simp_rw [one_on]; have hr:=Gauge.lieExp_cont SU.group; cases b <;> simp only [Bool.false_eq_true,↓reduceIte,one_mul,mul_one] <;> fun_prop (disch:=first| apply hr| assumption)
 simp_rw [swing,one_off _ _ h]; fun_prop
-- pay Guard via fare
open Region
lemma cap_swing {d:ℝ}{V:Pane n}(p:Cube.Guard V d)(z:SU.group.Color) : Cube.Guard (swing v b z V) (d+4*(sphereRate*(Λ * ‖z‖))):=by
 rw [guard_s]; rw [guard_s] at p; intro f; let x:=faceValue (swing v b z V) f; let y:=faceValue V f; let D:=sphereRate
 have ht:BPress.chord x y ≤ 4*(Λ*‖z‖):= BPress.chord.face _ V _ _ (fun i _ _=>swing_buy v b z V i)
 unfold tideF at *; change max ‖SU.fund x-1‖ ‖(matter x).val-1‖ ≤ _
 have hc:=p f; rw [max_le_iff] at hc ⊢; have hy :=sphereRate_cost; have hs :0<D:= hy.positive
 exact ⟨(norm_sub_le_norm_sub_add_norm_sub (fund x) (fund y) _).trans ((add_le_add ((hy.top _ _).trans (mul_le_mul_of_nonneg_left ht hs.le)) hc.1).trans_eq (by ring)), (norm_sub_le_norm_sub_add_norm_sub _ (matter y).val 1).trans ((add_le_add ((hy.bot ..).trans (mul_le_mul_of_nonneg_left ht hy.positive.le)) hc.2).trans_eq (by ring))⟩ -- fund firstF
lemma radius {d₁ e:ℝ}(h:d₁<e):∃ w> (0:ℝ),∀ n:Side,∀ v:gaugeLink n,∀ b:Bool,∀ (z:SU.group.Color)(V:Pane n),‖z‖ ≤ w → Cube.Guard V d₁ → Cube.Guard (swing v b z V) e:=by
 let c:=4*(sphereRate*Λ); have hc:0<c:=by have v:=hr; have g:=sphereRate_cost.positive; unfold c; positivity; -- precedence
 let w:=(e-d₁)/c; refine ⟨w, div_pos (sub_pos.mpr h) hc, fun n v b z V a p => (cap_swing v b p z).shrink ?_⟩
 have he:= (le_div_iff₀ hc).mp a; unfold c at *; linarith

-- domain type independent e's choice
variable (n)
abbrev Test (d ε:ℝ):= Spin.OpenW n d × {x:SU.group.Color// ‖x‖≤ε}

def H (d ε:ℝ):Material.Host (Seat n) (Single n) (Test n d ε) where
 space := terr _
 port := Spin.home n
 advert := fun S x y=> Agrees S x.1.val y.1.val ∧ x.2=y.2
 relay := fun p z => ⟨agrees_mono z.1 (Finset.coe_subset.mpr p), z.2⟩
variable {d ε e A c: ℝ} -- n wrong
variable {n}
def tollZ (d ε:ℝ) (x:Test n d ε):ℝ:= ‖x.2.val‖
private abbrev old(x:Test n d ε)(h:d≤e):Spin.OpenW n e:= ⟨x.1.val,x.1.property.shrink h⟩
private abbrev Authorized (v:gaugeLink n)(b:Bool)(d ε e:ℝ):Prop:=∀ x:Test n d ε,Cube.Guard (swing v b x.2.val x.1.val) e
private abbrev tick(x:Test n d ε)(h:Authorized v b d ε e):Spin.OpenW n e:= ⟨_,h x⟩
lemma lacks {M R:Pane n}{S:Finset (Seat n)}(p:Agrees S M R): invitation S M R=0:=invitation.agrees (fun i l=>p i (Finset.mem_filter.mp l).2.1 (Finset.mem_filter.mp l).2.2)
lemma dragC {v:gaugeLink n}(b:Bool)(S:Support (More n))(V:Pane n)(z:SU.group.Color) : invitation S (swing v b z V) V ≤ if Skye.ends v ⊆ S then Λ*‖z‖ else 0:=by
  unfold invitation; by_cases hw: v∈ leaks S
  · obtain ⟨t,i,k⟩:= Finset.mem_filter.mp hw
    rw [if_pos (show _ from by intro j h; rcases Finset.mem_insert.mp h with y|y; exact y ▸ i; exact Finset.mem_singleton.mp y ▸ k),Finset.sum_eq_single v]; exact swing_buy ..
    · intro i _ hi; simp only [swing,one_off _ _ hi, BPress.chord.refl]
    exact fun h=> (h hw).elim
  simp only [Finset.sum_eq_zero fun i hi=> (show BPress.chord (swing v b z V i) (V i)=0 from by rw [swing, one_off _ _ (show i≠v from fun t=> hw (t ▸ hi)),BPress.chord.refl])]; split; have h:=hr; positivity; rfl
-- simultaneous preserve Crown domain using Pledge. same labels pull from `RootedK`, showing δ-sense with exact-zero when e doesn't furnish S
variable {P:Spin.Pledge}{roller:Branch.Raw (Spin.OpenW n e)  (Single n)}
lemma film (G:P.Costs (Form.stage (AtW n e)) roller)(he:d≤e)(hp:Authorized v b d ε e) : Shot (H n d ε) (fun _=>1) ∅ P.rate P.price (fun x=> roller (old x he)) ∧ Shot (H n d ε) (fun _=>1) ∅ P.rate P.price (fun x=> roller (tick v b x hp)) ∧ Shot (H n d ε) (tollZ d ε) (Skye.ends v) P.rate (Λ*P.price) (fun x=> roller (tick v b x hp)-roller (old x he)):=by
  obtain ⟨F,K,T,L,Q⟩:=G
  let B:= Test n d ε; let C:= Spin.OpenW n e; let y: B→ C:=fun x=>old x he; let z:B→ C:=fun x=>tick v b x hp
  have hy:Continuous y:= Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _
  have hz:Continuous z:= Continuous.subtype_mk ((swingC v b).comp ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst))) _
  have hf(S)(c:B→C)(g:∀ x x',(H n d ε).advert S x x' → Agrees S (c x).val (c x').val)(i j: (Single n)) (x x') (p:(H n d ε).advert S x x'): F S (c x) i j= F S (c x') i j:=by
     have ht:= ((T S).expo i j).variation (c x) (c x'); change _ ≤ _*invitation _ _ _ at ht; rw [lacks (g _ _ p),mul_zero] at ht; exact sub_eq_zero.mp (norm_le_zero_iff.mp ht)
  have ho(S x x')(p:(H n d ε).advert S x x') : Agrees S (y x).val (y x').val:=p.1
  have hm(S x x')(p:(H n d ε).advert S x x') : Agrees S (z x).val (z x').val:=by
    change Agrees _ (swing v b x.2.val x.1.val) (swing v b x'.2.val x'.1.val); have hR: x.2=x'.2:=p.2; rw [hR]; exact swing_local v b _ p.1
  have hl (c:B→C)(p:Continuous c)(u:∀ S x x',(H n d ε).advert S x x'→ Agrees S (c x).val (c x').val) : Shot (H n d ε) (fun _=>1) ∅ P.rate P.price (fun x=> roller (c x)):=by
    exact ⟨fun S x=>F S (c x),K,fun S=>⟨fun i j=> let w:= (T S).expo i j; ⟨w.positive, fun t=>⟨empty_subset _,w.triggered t⟩,fun x=>by rw [mul_one]; exact w.bounded _, hf S c (u S) i j,w.connected.comp p⟩⟩, L,fun x=>Q _⟩
  refine ⟨hl y hy ho,hl z hz hm,?_,fun S:Seal (Seat n)=> if Skye.ends v⊆S then fun i j=>Λ*K S i j else 0,?_,?_,?_⟩ -- F' hole
  case refine_1 => exact fun S x=> F S (z x)-F S (y x)
  · intro S; refine ⟨fun i j=>?_⟩; let w:=(T S).expo i j
    have ht(x) : ‖F S (z x) i j-F S (y x) i j‖ ≤ K S i j * (if Skye.ends v⊆S then Λ*tollZ d ε x else 0):=(w.variation ..).trans (mul_le_mul_of_nonneg_left (dragC ..) w.positive)
    dsimp only; split
    next h=> exact ⟨mul_nonneg hr.le w.positive,fun t=> ⟨h,(w.triggered (right_ne_zero_of_mul t))⟩,fun x=>by change _ ≤ (Λ*_)*_; have he:=ht x; rw [if_pos h] at he; exact he.trans_eq (by ring), fun x y' p=> congrArg₂ (fun (i j:ℂ)=>i-j) (hf S z (hm S) i j x y' p) (hf S y (ho S) i j x y' p), (w.connected.comp hz).sub (w.connected.comp hy)⟩
    next h=>
      have he:(fun x:B=> (F S (z x)-F S (y x)) i j)=(0:B→ℂ):=by funext x; have hv:=ht x; rw [if_neg h,mul_zero] at hv; exact norm_le_zero_iff.mp hv
      rw [he]; exact Bit.trivial
  · refine (L.funds hr.le).lowers ?_; intro S i j; apply mul_le_mul_of_nonneg_left _ (rent_pos ..).le; split; rfl; exact mul_nonneg hr.le ((T S).nonn _ _)
  intro x; simp only [Q, Finset.sum_sub_distrib]; rfl
variable {game_:Preparation}
-- campaign constants: obtain jointly Costs for P and actual T at exact d; $M0/season
lemma range_h (h:Solstitial game_) : ∃ P:Spin.Pledge,∀ᶠ k:ℕ in atTop,∀ n:Side,k≤n.val →
    (∀ M:Tulip.Male,P.Costs (AtW n game_.d).stage (spar game_.K.j M ∘ Subtype.val)) ∧
    (∀ J:Cascade.Interest n,J.under (levelQ game_.W.C) (cashU game_.W.C) (levelQ game_.W.C) (cashU game_.W.C) (levelQ game_.W.C) (cashU game_.W.C) → P.Costs (AtW n game_.d).stage (J.P.den ∘ Subtype.val)):=by
 obtain ⟨σ,C,v,p,H⟩:= h.season
 let Q:Spin.Pledge:=⟨levelQ game_.W.C,cashU game_.W.C,level_p _,(Hom.Credit.posB _).trans_le (le_max_right ..)⟩
 let L':Spin.Pledge:= ⟨σ,C,v,p⟩; let P':=L'.scales (sphereRate/game_.d); let R:=Spin.aimPrice Q Q
 refine ⟨P'.bond R,H.mono (fun k p=> fun n hk=>?_ )⟩
 constructor
 · intro M; let ψ(x:Spin.OpenW n game_.d):↥(Openc (More n) game_.d):= ⟨profile x.val,⟨x.val,x.property,by simpa using game_.dpos⟩⟩
   have hp:= Drapes.Crown.lib ((p n hk).1 M); let D:=sphereRate; have hd:= sphereRate_cost; have he:=game_.dpos
   refine Pledge.Costs.up (Pledge.Costs.morph (P:=L') hp ψ (Continuous.subtype_mk (Dial.profile_c.comp continuous_subtype_val) _) rfl rfl (div_pos hd.positive he).le ?_) (Pledge.bond_lel P' R)
   intro S x y; change Tulip.fare S (profile x.val) (profile y.val)/|game_.d| ≤ _/ _*invitation S x.val y.val; rw [abs_of_pos he]; exact (div_le_div_of_nonneg_right (invitation.forum_compare hd) he.le).trans_eq (by ring)
 intro J g; exact Pledge.Costs.up (Form.pulls (Spin.aim_cost J.P (show J.P.toll Q.rate Q.rate Q.price Q.price from g.1)) (fun x:OpenW n game_.d=> x.val) continuous_subtype_val (fun S x y=>le_rfl)) (Pledge.bond_ler P' R)

-- Domain joint names
namespace Products
open Cascade
-- θ∈analytic ball. use before and after functions including e neg; for e-specific aperture domain old Γ shared across all keys. Compute exact material expressions charged LZ.5. 
variable (R:Cascade.Interest n)(ω : ℕ)

def rolled (x:Pane n):Op (Single n):=spar ω R.M x
def curt (x:Pane n):Op (Single n):=(1-rolled R ω x)*R.P.den x*(rolled R ω x)

def arcLog (x y: Pane n):Op (Single n):= Near.braid (rolled R ω x) (rolled R ω y)

def rotation (x y: Pane n):Op (Single n):= exp (arcLog R ω x y)

def correction (x y: Pane n): Op (Single n):= star (rotation R ω x y)*(1-curt R ω y)*(1+curt R ω x)-1
def V_pose (x y:Pane n): Op (Single n):= (rolled R ω y)*(rolled R ω x)+(1-rolled R ω y)*(1-rolled R ω x)
-- Two-color menu eventually also add companion tank letters, not these.
inductive Kind where
 | dP | dT | dC | dV | dU | L | Kck | LK
 deriving DecidableEq, Fintype

def sheet (T: Kind) (x y:Pane n) : Op (Single n) := match T with
 | .dP=> rolled R ω y-rolled R ω x
 | .dT=> R.P.den y-R.P.den x
 | .dC=> curt R ω y-curt R ω x
 | .dV=> V_pose R ω x y-1
 | .dU=> rotation R ω x y-1
 | .L=> arcLog R ω x y
 | .Kck=> correction R ω x y
 | .LK=> Branch.pencil (correction R ω x y)

variable (a:ℝ)
def after (i: Test n d ε):Pane n := swing v b i.2.val i.1.val
local notation "Y1" => Test n d ε
abbrev plain (f:Pane n → Op (Single n)) : Raw (Y1) (Single n):=f ∘ fun x=> x.1.val

def read (T:Kind) (x:Test n d ε):= sheet R ω T x.1.val (after v b x)
-- use ProdBench abstract
local notation "𝒯"=> H n d ε
local notation "Ξ"=>Op (Single n)
local notation "Δ"=>tollZ d ε (n:=n)
local notation "ℚ₁"=>Skye.ends v

def prepares (π:Cascade.Interest n)(e:ℝ)(P: Spin.Pledge) :Prop:=
 (∀ y: Spin.OpenW n e,IsStarProjection (rolled π ω y.val)) ∧
 P.Costs (AtW n e).stage (rolled π ω ∘ Subtype.val) ∧ P.Costs (AtW n e).stage (π.P.den ∘ Subtype.val)

-- unlinked and same-linked endpoint costs. arithmetic. need explicit v implicit. use generic H instead for combinators.
variable {u:Seal (Seat n)}{W Q:Branch.Raw (Test n d ε) (Single n)}{s t r:ℝ}
private abbrev Price_u (s t)(f:Branch.Raw (Test n d ε) (Single n)):=Shot (H n d ε) (fun _=>1) ∅ s t f
private abbrev Price_v (u:Seal (Seat n))(s t)(f:Branch.Raw (Test n d ε) (Single n)):=Shot (H n d ε) (tollZ d ε) u s t f
private lemma no (h:Price_u s t W)(g:Price_u s r Q)(p:0≤ s): Price_u s (2*(t*r)) (fun x=> W x * Q x):=by convert (h.mult g p) using 1; ext; simp; simp
private lemma singleR (h:Price_u s t W)(g:Price_v u s r Q)(p:0≤ s): Price_v u s (2*(t*r)) (fun x=> W x * Q x):=by convert (h.mult g p) using 1; ext; simp; simp
private lemma singleL (h:Price_v u s t W)(g:Price_u s r Q)(p:0≤ s): Price_v u s (2*(t*r)) (fun x=> W x * Q x):=by convert (h.mult g p) using 1; ext; simp; simp
-- fix simp order

-- precise costs for C & dC
def credit(a B:ℝ):= 4*((Real.exp a+B)*B*B)
def dynamic (a B:ℝ):= 4*(Λ*B*B*B + (Real.exp a+B)*(Λ*B)*B + (Real.exp a+B)*B*(Λ*B))
private lemma shiftC (E:Authorized v b d ε e)(m:d≤e)(p:prepares ω R e P):
    let Xg:=fun (x:Test n d ε)=> x.1.val;
    let Y:=after v b (d:=d) (ε:=ε);
    Price_u P.rate (credit P.rate P.price) (curt R ω ∘ Xg) ∧
    Price_u P.rate (credit P.rate P.price) (curt R ω ∘ Y) ∧
    Price_v (Skye.ends v) P.rate (dynamic P.rate P.price) (curt R ω ∘ Y-curt R ω ∘ Xg):=by
 intro Xg Y; let l:= Skye.ends v; let a:=P.rate; let t:= P.price
 let S:=rolled R ω; let T:=R.P.den
 let B:=S ∘ Xg; let B':=S ∘ Y; let C:=T ∘ Xg; let C':=T ∘ Y
 obtain ⟨h,h',dh⟩:=film v b p.2.1 m E; obtain ⟨g,g',dg⟩:=film v b p.2.2 m E
 change Price_u a t B at h; change Price_u a t B' at h'; change Price_v l a (Λ*t) (B'-B) at dh
 change Price_u a t C at g; change Price_u a t C' at g'; change Price_v l a (Λ*t) (C'-C) at dg
 let Z:= 1-B; let Z':= 1-B'; have hv:Price_u a (Real.exp a+t) Z:= Shot.one.sub h; have hu:Price_u a (Real.exp a+t) Z':= Shot.one.sub h'
 have ht:Price_v l a (Λ*t) (Z'-Z):=by
    rw [sub_sub_sub_cancel_left]
    rw [←neg_sub B' B]; exact dh.neg
 have hp :0≤a:= P.pos.le
 let f:= credit a t
 have he: Price_u a f (Z*C*B):= (no (no hv g hp) h hp).relax (le_of_eq (by unfold f credit; ring))
 have hz: Price_u a f (Z'*C'*B'):= (no (no hu g' hp) h' hp).relax (le_of_eq (by unfold f credit; ring))
 refine ⟨he,hz,?_⟩ -- definitional comp
 have hk: (Z'*C'*B'-Z*C*B)= ((Z'-Z)*C'*B' + Z*(C'-C)*B' + Z*C*(B'-B)):=by noncomm_ring
 change Price_v l a (dynamic a t) (Z'*C'*B'-Z*C*B); rw [hk]; exact (((singleL (singleL ht g' hp) h' hp).plus (singleL (singleR hv dg hp) h' hp)).plus (singleR (no hv g hp) dh hp)).relax (le_of_eq (by unfold dynamic; ring))
-- dV cost through ΔP J, and thus budget L via Mercator. Radius coupling and rates stored numerically to guide h.

private def Rbook (P:Spin.Pledge):=2* (Λ*P.price*(2*P.price+Real.exp P.rate))
private def Wbook (P:Spin.Pledge):=2*Rbook P
private def Lbook (P:Spin.Pledge):= 2 * Wbook P -- half allowance left
private def Ubook (P:Spin.Pledge):=2 * Lbook P
private def Kbook (P:Spin.Pledge):ℝ:= 4*(Ubook P*(Real.exp P.rate+credit P.rate P.price)*(Real.exp P.rate+credit P.rate P.price)) + 2*(dynamic P.rate P.price*(Real.exp P.rate+credit P.rate P.price))
private def Fee (P:Spin.Pledge):= max (Λ*P.price) (max (dynamic P.rate P.price) (max (credit P.rate P.price) (max (Rbook P) (max (Wbook P) (max (Lbook P) (max (Ubook P) (2*Kbook P)))))))
private lemma money (P:Spin.Pledge): 0<Λ*P.price ∧ 0<Kbook P ∧ 0<Wbook P:=by
  have ht:=hr; have hu:=P.bought; have he:= P.pos; refine ⟨by positivity,?_,?_⟩ <;> simp only [Kbook,Ubook,Lbook,Wbook,Rbook,credit,dynamic] <;> positivity -- unfold K if no K
private lemma money_hi (P:Spin.Pledge): Wbook P ≤ Fee P ∧ Rbook P ≤ Fee P ∧ Ubook P ≤ Fee P ∧ Lbook P ≤ Fee P ∧ credit P.rate P.price ≤ Fee P ∧ dynamic P.rate P.price ≤ Fee P ∧ Λ*P.price ≤ Fee P ∧ 2*Kbook P ≤ Fee P := by
 simp [Fee]

structure CoverR (n:Side)(r A:ℝ)(f:Kind→ Test n d ε→ Op (Single n))(p:gaugeLink n):Prop where
 parts i: Price_v (Skye.ends p) r A (f i)

variable (Q:Spin.Pledge)
private lemma allKit (E:Authorized v b d ε e)(m:d ≤ e)(p:prepares ω R e Q)(a₀:0 ≤ ε)(u: ε*Fee Q  ≤  1/128) : CoverR n Q.rate (Fee Q) (fun i (x:Test n d ε)=>read v b R ω i x) v ∧
    ∀ x:Test n d ε, ‖rolled R ω (after v b x) - rolled R ω x.1.val‖  ≤  1/64:=by
 let τ:=Q.rate; let k:=Q.price; let A:=fun x:Y1=>x.1.val; let B:=after v b (d:=d) (ε:=ε)
 let I:=rolled R ω; let S':=I ∘ B; let S:= I ∘ A; let T':=R.P.den ∘ B; let T:=R.P.den ∘ A; let C:=curt R ω ∘ A; let C':=curt R ω ∘ B; let G:=Skye.ends v
 let J:=(2:ℝ) • S-1
 have hv(x:Y1):0 ≤  Δ x:=norm_nonneg _; have hg(x:Y1):Δ x ≤ ε:= x.2.property
 obtain ⟨hp,hk,hw⟩:=money Q; obtain ⟨hW,hR,hU,hL,hC,hD,hY,hK⟩:=money_hi Q
 have hx:=Q.pos
 obtain ⟨g,g',gg⟩:=film v b p.2.1 m E; obtain ⟨i,i',ii⟩:=film v b p.2.2 m E
 change Price_u τ k S at g; change Price_u τ k T' at i'; change Price_v G τ (Λ*k) (S'-S) at gg; change Price_v G τ (Λ*k) (T'-T) at ii
 obtain ⟨hc,hc',hh⟩:=shiftC v b R ω E m p; change Price_u τ (credit τ k) C at hc; change Price_v G τ (dynamic τ k) (C'-C) at hh
 have hJ:Price_u τ (2*k+Real.exp τ) J:= by
    have he:Price_u τ (Real.exp τ) (1: Y1 → Ξ):= Shot.one
    have h:Price_u τ (‖(2:ℝ)‖*k+Real.exp τ) J:= Shot.sub (Shot.mono g (2:ℝ)) he; simpa only [Real.norm_of_nonneg (by norm_num:(0:ℝ) ≤ 2)] using h
 let Z:= ((S'-S)*J)
 have hz : Price_v G τ (Rbook Q) Z := singleL gg hJ hx.le
 have hxU(x:Y1):IsStarProjection (S x):= p.1 (old x m)
 have hcQ(x:Y1):C x*C x=0:=by
    let V:=S x; let αx:=T x; have ht: V*(1-V)=0:=by rw [mul_sub,mul_one,show V*V=V from (hxU x).isIdempotentElem.eq,sub_self]
    change ((1-V)*αx*V)*((1-V)*αx*V)=_; rw [mul_assoc,←mul_assoc V,←mul_assoc V,ht,zero_mul,zero_mul,mul_zero]
 have zQ(x:Y1):Z x= V_pose R ω (A x) (B x)-1 ∧ (2:ℝ) • Z x= Near.bud (S x) (S' x)-1 :=by
    let αx:=S' x; let Yz:=S x; have he:Yz*Yz=Yz:=(hxU x).isIdempotentElem.eq
    constructor
    · change (αx-Yz)*((2:ℝ) • Yz-1)=αx*Yz+(1-αx)*(1-Yz)-1; rw [two_smul]; noncomm_ring [he]
    unfold Near.bud Near.reflector; simp only [two_smul, Z,Pi.mul_apply,Pi.sub_apply,J,Pi.smul_apply,Pi.one_apply,Pi.add_apply]; change _ = _; noncomm_ring [show S x*S x=S x from he]
 let αx(x:Y1):=(2:ℝ) • Z x; have ht:Price_v G τ (Wbook Q) αx:=by unfold Wbook; simpa only [Real.norm_of_nonneg (by norm_num:(0:ℝ) ≤ 2)] using hz.mono (2:ℝ)
 have fits(y)(p:y ≤ Fee Q): ε*(2*y) ≤ 1/2:=by linarith only [u,mul_le_mul_of_nonneg_left p a₀]
 let fL:=fun x:Y1=> arcLog R ω (A x) (B x)
 have L : Price_v G τ (Lbook Q) fL :=by
   have h := (Shot.pencil_charge ht hx.le hv _ a₀ hg (fits _ hW)).mono (1/2:ℝ)
   apply Shot.relax (c:=Lbook Q) (r:=‖(1/2:ℝ)‖*(2*Wbook Q)) ?_ ((mul_le_of_le_one_left (by positivity) (by norm_num [Real.norm_eq_abs])).trans le_rfl)
   convert h using 1; funext x; unfold fL arcLog Near.braid; change _=(1/2:ℝ) • Branch.pencil (αx x); rw [show αx x=_ from (zQ x).2]; rfl
 let U:=fun x:Y1=> rotation R ω (A x) (B x)
 have hhU : Price_v G τ (Ubook Q) (U-1):= Shot.expon L hx.le hv _ a₀ hg (fits _ hL)
 let D':=Real.exp τ+credit τ k
 have he: Price_u τ D' (1-C'):= Shot.one.sub hc'; have hD':Price_u τ D' (1+C):= Shot.one.plus hc
 have hU': Price_v G τ (Ubook Q) (fun i=>star (U i)-1):= by simpa only [Pi.sub_apply,Pi.one_apply,star_sub,star_one] using hhU.starP
 let K(x:Y1):=correction R ω (A x) (B x)
 have heQ : Price_v G τ (Kbook Q) K :=by
   have hb:= (singleL (singleL hU' he hx.le) hD' hx.le).plus (singleL hh.neg hD' hx.le)
   apply Shot.relax (r:=2*(2*(Ubook Q*D')*D')+2*(dynamic τ k*D')) (c:=Kbook Q) ?_ (le_of_eq (by unfold Kbook D' τ k; ring)); convert hb using 1; funext x; change star (U x)*(1-C' x)*(1+C x)-1=(star (U x)-1)*(1-C' x)*(1+C x)+(-(C' x-C x))*(1+C x); noncomm_ring [hcQ x]
 have hFee:0 ≤ Kbook Q:=hk.le
 have hJ:= Shot.pencil_charge heQ hx.le hv _ a₀ hg (fits _ ((show Kbook Q≤2*Kbook Q by linarith only [hFee]).trans hK))
 refine ⟨⟨fun J=>?_⟩,fun x=>?_⟩
 · cases J with
   | dP=>exact gg.relax hY
   | dT=>exact ii.relax hY
   | dC=>exact hh.relax hD
   | dV=>exact ((show (fun x=> read v b R ω Kind.dV x)= Z from funext fun x=> (zQ x).1.symm) ▸ (hz.relax hR)) -- eqrec direction?
   | dU=> exact hhU.relax hU
   | L=> exact L.relax hL
   | Kck=>exact heQ.relax ((show Kbook Q≤2*Kbook Q by linarith only [hFee]).trans hK)
   | LK=> exact hJ.relax hK
 apply (gg.squeezed x (hv x) hx.le).trans; change (Λ*Q.price) * _ ≤ _; rw [mul_comm]; refine (mul_le_mul (hg _) hY hp.le a₀).trans (u.trans (by norm_num))
open UVNext.PricedKernels
private abbrev Fike:= (Fintype.card SU.Slot:ℝ) * Fintype.card SpinIdx + 4

def RollKit (n:Side)(R:Cascade.Interest n)(ω:ℕ)(d ε c C:ℝ):Prop :=
  ∀ (b:gaugeLink n→ Bool), ∀ i:Kind,
    ∃ M W, Material.Roll (H n d ε) (tollZ d ε) Skye.ends (2*c) C C (fun e=>read e (b e) R ω i) M W
-- pre aperture. Need strengthen e budget all labels by same C: choose C≥r*c(C),≥r. 
variable {game_:Preparation}
local notation "A_p"=>levelQ game_.W.C
local notation "B_p"=>cashU game_.W.C
private abbrev wall(n:Side)(J:Cascade.Interest n):=J.under A_p B_p A_p B_p A_p B_p
private abbrev center:= (game_.d+game_.J.roomX)/2
-- contour count from basin; holds w/o Side big. Sum ee.orol. No increase for crease geometry L.
private lemma feeCard (n:Side){t:ℝ}(p:0<t) :
    let v(i j:Seat n):=Real.exp (-t*separation i j);
    let C:=Fike*UVNext.PricedKernels.basin t;
    (∀ i:Single n, ∑ e:gaugeLink n, v e.1 (Spin.home n i) ≤ C) ∧
    (∀ e:gaugeLink n,∑ i:Single n,v e.1 (Spin.home n i) ≤ C):=by
 intro v C; have hv(i j):0 ≤ v i j:=(Real.exp_pos _).le
 have hw(i:Seat n): ∑ j,v i j≤ basin t:= funnel p i
 have hr:0 ≤ basin t:= (Finset.sum_nonneg (s:=univ) (fun j _=>hv (0:Seat n) j)).trans (hw 0) -- fix
 constructor
 · intro i; unfold gaugeLink Edge; rw [Fintype.sum_prod_type]; dsimp only; simp only [sum_const,card_univ,nsmul_eq_mul,Axis,Fintype.card_fin,←mul_sum]
   have hl:∑ x,v x (Spin.home n i) = ∑ x,v (Spin.home n i) x:=by apply sum_congr rfl; intro t _; unfold v; rw [separation_comm t]
   rw [hl]; apply mul_le_mul _ (hw _) (Finset.sum_nonneg fun _ _=>hv _ _) (by unfold Fike; positivity)
   unfold Fike; push_cast; linarith only [show (0:ℝ)≤(Fintype.card SU.Slot:ℝ) * Fintype.card SpinIdx from by positivity]
 intro e; unfold Single; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; change ∑ x:Site n, ∑ _i:SpinIdx, ∑ _:SU.Slot, v e.1 (node x) ≤ C
 simp only [sum_const,card_univ,nsmul_eq_mul,←mul_sum]; have hp: ∑ x:Site n, v e.1 (node x) ≤ basin t:=by rw [←sum_image (by intro i _ j _ h; exact Tenant.needle h)]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>hv e.1 i).trans (hw e.1)
 unfold C Fike; rw [←mul_assoc]; apply mul_le_mul (by rw [mul_comm]; linarith) hp (sum_nonneg fun _ _=>hv ..) (by positivity)

/-- Credential for (LZ.3–5) matrix purchases (amplitude version here), on actual H at d and any Solstitial P. Keeps all stage addresses on the no-new-d restriction (take sufficiently late i from Stem kicking). a_* from $\sigma$ of P. Include every incidence costs; transformations at chosen e can additionally use `Near.turns`, at present not here asserting every term polygauge or extension via gates.
-/
theorem epoch (h:Solstitial game_) : ∃ (z0 c C:ℝ),0<z0 ∧ 0<c ∧ 0<C ∧
    ∀ᶠ k:ℕ in atTop,∀ n:Side,game_.U.roundZ ≤ n.val → k≤n.val →∀ R:Cascade.Interest n,wall n R (game_:=game_) →
    RollKit n R game_.K.j (center (game_:=game_)) z0 c C ∧
    ∀ (v:gaugeLink n)(b:Bool),∀ x:Test n (center (game_:=game_)) z0,
    let P':=rolled R game_.K.j x.1.val;
    let V:=after v b x;
    let Pz:=rolled R game_.K.j V;
    Cube.Guard V game_.d ∧ IsStarProjection P' ∧ IsStarProjection Pz ∧ ‖Pz-P'‖≤1/64:=by
 obtain ⟨Q,H0⟩:=range_h h
 let m:= center (game_:=game_); have hw:m < game_.d:=by unfold m center; linarith only [game_.J.hr]
 obtain ⟨d₀,g,T⟩:= radius hw; let t:= Q.rate; let C:= Fee Q
 have hp:0<C:= (money Q).2.2.trans_le (money_hi Q).1
 let z0:=min d₀ ((1/128)/C); have hv:0< z0:=lt_min g (div_pos (by norm_num) hp)
 let a:=t/2; have ha:0 < a := half_pos Q.pos
 let Δ':=Fike * UVNext.PricedKernels.basin a; let D:=max C (C*Δ')
 refine ⟨z0,a,D,hv,ha,hp.trans_le (le_max_left ..),H0.mono (fun k he n hr hN R J =>?_)⟩
 let ω:=game_.K.j; let e:=game_.d; obtain ⟨X1,X2⟩:= he n hN
 have hθ:prepares ω R e Q:=⟨(fun x=>(game_.U.broadness n hr R.M).projection x.val x.property),X1 _,X2 _ J⟩
 have hz(v:gaugeLink n)(b:Bool):Authorized v b m z0 e:= fun x=> T _ _ _ _ x.1.val (x.2.property.trans (min_le_left ..)) x.1.property
 have ht(v:gaugeLink n)(b:Bool):= allKit v b R ω Q (hz v b) hw.le hθ hv.le ((le_div_iff₀ hp).mp (min_le_right ..))
 constructor
 · intro b i
   have hy:= feeCard n ha
   obtain ⟨M,W,L⟩:= Material.booked (o:=fun e:gaugeLink n=> e.1) hp.le Δ' Q.pos.le (fun e:gaugeLink n=> (ht e (b e)).1.parts i) (fun j=>Finset.mem_insert_self ..) (by simp only [neg_div]; exact hy.1) (by simp only [neg_div]; exact hy.2)
   refine ⟨M,W,L.shapes,fun i=>?_, L.total,fun j=> ?_, fun j=>?_,fun j=>?_⟩;
   · rw [show 2*a=t by unfold a; ring]; exact (L.grant i).book (le_max_left ..)
   · rw [show 2*a=t by unfold a; ring]; exact (L.row j).trans (le_max_right ..)
   · rw [show 2*a=t by unfold a; ring]; exact (L.col j).trans (le_max_right ..)
   rw [show 2*a=t by unfold a; ring]; exact (L.all j).trans (le_max_right ..)
 intro v b x; dsimp only; exact ⟨hz v b x,hθ.1 (old x hw.le),hθ.1 (tick v b x (hz v b)),(ht v b).2 _⟩

-- unlinked companions. users can derive (1-Q),(1±C), adjoints by Shot rules. including all at moved args.
abbrev Peers (n:Side)(R:Cascade.Interest n)(ω:ℕ)(d ε t c:ℝ):Prop:=
  let A:=fun x:Test n d ε=>x.1.val; ∀ (v:gaugeLink n)(b:Bool), let B:=after v b (d:=d) (ε:=ε);
    ∀ (f:Pane n→Op (Single n)), f=rolled R ω ∨ f=R.P.den ∨ f=curt R ω →
    Material.Shot (H n d ε) (fun _=>1) ∅ t c (f ∘ A) ∧ Material.Shot (H n d ε) (fun _=>1) ∅ t c (f ∘ B)

lemma unlinks (E:Authorized v b d ε e)(m:d≤e)(p:prepares ω R e Q)(f:Pane n→ Op (Single n))(g:f=rolled R ω ∨ f=R.P.den ∨ f=curt R ω) : let Xg:=fun (x:Test n d ε)=>x.1.val;
    let B:=after v b (d:=d) (ε:=ε); let c:=max Q.price (credit Q.rate Q.price)
    Price_u Q.rate c (f ∘ Xg) ∧ Price_u Q.rate c (f ∘ B):=by
  intro Xg B c; obtain ⟨i,j,h⟩:=film v b p.2.1 m E; obtain ⟨t,w,_⟩:=film v b p.2.2 m E; obtain ⟨s,n,_⟩:=shiftC v b R ω E m p
  rcases g with rfl|rfl|rfl; exact ⟨i.relax (le_max_left ..),j.relax (le_max_left ..)⟩; exact ⟨t.relax (le_max_left ..),w.relax (le_max_left ..)⟩; exact ⟨s.relax (le_max_right ..),n.relax (le_max_right ..)⟩

protected lemma RollKit.shot {R:Cascade.Interest n}{ω:ℕ}{c C:ℝ}(G:RollKit n R ω d ε c C) (x:Kind):Material.Shot (H n d ε) Δ (Skye.ends v) (2*c) C (read v b R ω x):=by obtain ⟨M,W,f⟩:=G (fun _=>b) x; exact ⟨M v,W v,f.shapes v,f.grant v,f.total v⟩

-- Refine epoch to smaller ε chosen after C; preserves same Roll choices & Peers per new fixed appointment (not asserting every term agrees in overlaps!). Need choose peer constants first (rate same?) combine via min(t,ρ). Roll.grant lower and rad). cheap path instead rerun epoch proof with combined X. Include K small by allKit costs, independent cFinal. Want algebra theorem rely on K bound from installed C and ε. Re-issue with explicit shrink via continuous domain embedding and $ν$ preserving. Γ.sheets compare through Spin incl `$W$'' at transferred uses.
lemma repath {C c ε ε':ℝ}(t:ε' ≤ ε)(g: RollKit n R ω d ε c C): RollKit n R ω d ε' c C :=by
 intro b i; obtain ⟨M,W,h⟩:=g b i
 let j(c:Test n d ε'):Test n d ε:=(c.1,⟨c.2.val,c.2.property.trans t⟩); have hj:Continuous j:=continuous_fst.prodMk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd) _)
 refine ⟨fun v S=>M v S ∘ j,W, fun v S=>?_ ,h.grant,?_,h.row,h.col,h.all⟩
 · refine ⟨fun x y=>?_⟩; let w:= (h.shapes v S).block x y
   refine ⟨w.pos,w.stake,fun z=>w.load (j z),fun x y p=>w.inputs (j x) (j y) ?_,w.listens.comp hj⟩
   exact ⟨p.1,Subtype.ext (congrArg (fun x:{c:SU.group.Color // ‖c‖≤ε'}=>x.val) p.2)⟩
 exact fun v x=>h.total v (j x)
lemma Cheap_roll {C c ε:ℝ}(t:r ≤ c)(w:C ≤ s)(g: RollKit n R ω d ε c C) : RollKit n R ω d ε r s:=by
 intro b i; obtain ⟨M,W,h⟩:=g b i
 have hv(e:gaugeLink n){a a':ℝ}(hG:a ≤ a'):=sale_mono (w:=W e) (w':=W e) (a:=a) (d:=a') (fun S i j=>mul_le_mul_of_nonneg_right (rent_up hG S) ((h.shapes e S).block i j).pos)
 refine ⟨M,W,h.shapes,fun e=>?_,h.total,fun i=>?_,fun i=>?_,fun i=>?_⟩
 · exact ((h.grant e).lowers (fun S i j=>mul_le_mul_of_nonneg_right (rent_up (by linarith only [t]) S) ((h.shapes e S).block i j).pos)).book w
 · exact (sum_le_sum (fun e _=> (sum_le_sum (fun j _=> hv e (a':=2*c/2) (by linarith only [t]) i j)))).trans ((h.row i).trans w)
 · exact (sum_le_sum (fun e _=> (sum_le_sum (fun j _=> hv e (a':=2*c/2) (by linarith only [t]) j i)))).trans ((h.col i).trans w)
 exact (sum_le_sum (fun e _=> (sum_le_sum (fun j _=> hv i (a':=2*c/2) (by linarith only [t]) e j)))).trans ((h.all i).trans w)

structure License (n:Side)(R:Cascade.Interest n)(ω:ℕ) (rad d e t c:ℝ):Prop where
 inv : RollKit n R ω d rad t c
 extension : Peers n R ω d rad (2*t) c
 fit(v:gaugeLink n)(b:Bool)(x:Test n d rad): let P':=rolled R ω x.1.val;
    let V:=after v b x; let Pz:=rolled R ω V;
    Cube.Guard V e ∧ IsStarProjection P' ∧ IsStarProjection Pz ∧ ‖Pz-P'‖≤1/64 ∧ ‖read v b R ω .Kck x‖≤1/64

theorem authorization (h:Solstitial game_) : ∃ z c C:ℝ,0<z∧0<c∧0<C∧∀ᶠ k:ℕ in atTop,∀ n:Side,game_.U.roundZ ≤ n.val → k ≤ n.val →∀ R:Cascade.Interest n,wall (game_:=game_) n R → License n R game_.K.j z (center (game_:=game_)) game_.d c C:=by
 obtain ⟨Q,H0⟩:=range_h h; obtain ⟨z,t,k,hz,hT,hk,H⟩:=epoch h
 let r:=min t (Q.rate/2); have a:0<r:= lt_min hT (half_pos Q.pos)
 let m:=center (game_:=game_); have he:m≤ game_.d:=by unfold m center; linarith only [game_.J.hr]
 let w:=min z ((1/64)/k); let C:=max k (max Q.price (credit Q.rate Q.price))
 have hZ:0<w:=lt_min hz (div_pos (by norm_num) hk)
 refine ⟨w,r,C,hZ,a,hk.trans_le (le_max_left ..),?_⟩
 filter_upwards [H,H0] with i hv hu n v d R t₀
 let Xz:=game_.K.j; obtain ⟨l,p⟩:=hv n v d R t₀; let f(x:Test n m w):Test n m z:=(x.1,⟨x.2.val,x.2.property.trans (min_le_left ..)⟩)
 have hold(v:gaugeLink n)(b:Bool)(x:Test n m w):=p v b (f x)
 have smoked(v:gaugeLink n)(b:Bool):Authorized v b m w game_.d:=fun x=> (hold v b x).1
 have kit:=repath R Xz (show w≤z from min_le_left ..) l
 refine ⟨Cheap_roll R Xz (min_le_left ..) (le_max_left ..) kit,?_,fun v b x=>?_⟩
 · intro v' b y f k
   have e: prepares Xz R game_.d Q:= ⟨fun x=> (game_.U.broadness n v R.M).projection _ x.property,(hu n d).1 _,(hu n d).2 R t₀⟩
   have he:= unlinks v' b R Xz Q (smoked v' b) he e _ k
   have hm:2*r≤Q.rate:=by linarith only [(show r ≤ Q.rate/2 from min_le_right ..)]
   exact ⟨(he.1.lower hm).relax (le_max_right ..),(he.2.lower hm).relax (le_max_right ..)⟩
 obtain ⟨h1,h2,h3,h4⟩:= hold v b x
 refine ⟨h1,h2,h3,h4,((RollKit.shot v b kit Kind.Kck).squeezed x (norm_nonneg _) (by linarith only [hT])).trans ?_⟩
 have ht:tollZ m w x ≤ w:=x.2.property; rw [mul_comm]; exact (mul_le_mul_of_nonneg_right (ht.trans (min_le_right ..)) hk.le).trans_eq (div_mul_cancel₀ _ hk.ne')
end Products

-- delivered at actual kick height and Force election. no threshold assumptions besides Solstitial and r.
open Products Py Cascade
set_option quotPrecheck false
variable (P:Spine)
local notation "Y"=> P.run
local notation "Π1"=> P.par
local notation "c₁"=> (P.par.d+P.par.J.roomX)/2
theorem assigned_rulers (h:Solstitial P.par): ∃ z c C:ℝ,0<z∧0<c∧0<C∧ ∀ s:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s ≤ P.run.uv k → let N:=Papal.count (Y) s i;
    let V:=Papal.gram (Y) s i k;
    Products.License N V.J (Π1).K.j z c₁ (Π1).d c C ∧ (∀ t:Orbit N,Cube.Guard (Papal.room (Y) s i t) (Π1).J.roomX) ∧ (Π1).U.roundZ ≤ N.val:=by
 obtain ⟨z,c,C,p,e,x,H⟩:= Products.authorization h
 obtain ⟨k,hk⟩:= H.exists
 refine ⟨z,c,C,p,e,x,fun s=>?_⟩
 filter_upwards [(Papal.count_grows (Y) s).eventually (eventually_ge_atTop (max k (Π1).U.roundZ))] with i h j l N V
 change max k (Π1).U.roundZ ≤ N.val at h
 have H:= (Papal.prices_plot (Y) s i j l).2.2.2.2.field
 refine ⟨hk N (by omega) (by omega) V.J H, fun t=> (((Y).voyage i).ownership s).paid.paid t, by omega⟩
end Pose
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
