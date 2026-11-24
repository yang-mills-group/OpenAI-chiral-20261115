import YM.CF.Delta.Barge

/-! For local overlaps the endpoint margins travel. Only lands on changed fields are counted. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample NormedSpace Branch Tenant Function Finset MeasureTheory Filter Lattice Petal Ave
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e p K : ℝ} {c : Phase.Part m B}
abbrev Letters (m B : Side) (e p : ℝ) := {U : Briar m B e × Briar m B e // CloseP p U.1.val U.2.val}
abbrev Mkt (m B : Side) (e p : ℝ) := Letters m B e p × Cue m
lemma mail_closed (m B : Side) (e p : ℝ) : IsClosed {U:Briar m B e × Briar m B e|CloseP p U.1.val U.2.val} := by
  have he {I : Type} [Fintype I] [DecidableEq I] (R : E→*UNI I) (v : Continuous (fun t=> (R t).val)): IsClosed {U:Briar m B e × Briar m B e|∀ x, Cube.cmp R (U.1.val x) (U.2.val x)≤p} := by
    simp_rw [Set.setOf_forall]; refine isClosed_iInter fun i=> isClosed_le ?_ continuous_const
    exact ((v.comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))).sub (v.comp ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))).norm
  exact IsClosed.inter (he _ SU.fund_cont) (he _ matter_cont)
instance : CompactSpace (Letters m B e p) := isCompact_iff_compactSpace.mp (mail_closed m B e p).isCompact
def hill (x : Letters m B e p) (g : Court m B) : Letters m B e p := ⟨(routeS g x.val.1,routeS g x.val.2),by
  have he:=x.property
  constructor <;> intro i <;> first | simpa only [routeS,Lattice.gauge,cmp_right,cmp_left] using he.1 i | simpa only [routeS,Lattice.gauge,cmp_right,cmp_left] using he.2 i⟩
def Mail (m B : Side) (e p : ℝ) : Lodge (Index m) ℂ (Letters m B e p) (Court m B) where
  toBell := (moneyW m B e).toBell
  rule := (moneyW m B e).rule
  pick g d:= hill d g
  zone S x y:= (moneyW m B e).zone S x.val.1 y.val.1 ∧ (moneyW m B e).zone S x.val.2 y.val.2
  grows i h:= ⟨(moneyW m B e).grows i h.1,(moneyW m B e).grows i h.2⟩
  ct:= (moneyW m B e).ct
def eastK (x : Mkt m B e p) : Train m B e := (x.1.val.1,x.2)
def westK (x : Mkt m B e p) : Train m B e := (x.1.val.2,x.2)
lemma east_cont : Continuous (eastK (m:=m) (B:=B) (e:=e) (p:=p)) := ((continuous_fst.comp continuous_subtype_val).comp continuous_fst).prodMk continuous_snd
lemma west_cont : Continuous (westK (m:=m) (B:=B) (e:=e) (p:=p)) := ((continuous_snd.comp continuous_subtype_val).comp continuous_fst).prodMk continuous_snd
def wagon (m B : Side) (e p:ℝ) : Cabin cloud (Mail m B e p) where
  seat p:= (Treasury m B e).seat p.val.1
  unionV:= partner m B
  board g:= (pass m B g).measurableEmbedding
  plenty g:= rain_g m B g
  mass g U x:= (Treasury m B e).mass g U.val.1 x
  ct:= by
    change Continuous ((barF (Treasury m B e)) ∘ eastK (m:=m) (B:=B) (e:=e) (p:=p)); exact ((show Continuous (barF (Treasury m B e)) from (Treasury m B e).ct).comp east_cont)
  reflL S d:= ⟨(Treasury m B e).reflL S d.val.1,(Treasury m B e).reflL S d.val.2⟩
abbrev trainP (m B : Side) (e p) := booth (wagon m B e p)
section
variable (L : Wood B p) (b : Room B e)
lemma furn {x : Mkt m B e p} (g : x∈trainP m B e p) : release (eastK x)∈payer m B e := pays g
include L
lemma yarn {x : Mkt m B e p} (g : x∈trainP m B e p) : release (westK x)∈payer m B e := ⟨x.1.val.2.property,passed L.licit x.1.property x.2 g⟩
include b
lemma secF (x : trainP m B e p) : TenantK (stayX (eastK (x.val:Mkt m B e p))) := dark0 b none (furn x.property)
lemma secG (x : trainP m B e p) : TenantK (stayX (westK (x.val:Mkt m B e p))) := dark0 b none (yarn L x.property)
-- expose evaluation only on this open set
def silver (L : Wood B p) (b : Room B e) (c : Phase.Part m B) (x : trainP m B e p) : TwinK (codify (m:=m) (B:=B) c) :=
  ⟨(⟨_,secF L b x⟩,⟨_,secG L b x⟩), L.pose _ _ _ x.val.1.property b x.val.1.val.1.property x.val.1.val.2.property (show Verified m B margin _ _ {0} from (furn x.property).2) (show Verified m B margin _ _ {0} from (yarn L x.property).2) (stick_in _ (mem_singleton_self _)) c⟩ -- L,b not used in header!
lemma silverC (c : Phase.Part m B) : Continuous (silver L b c) := by
  apply Continuous.subtype_mk
  have he : stick (0:Row)∈zone {0}:= stick_in _ (mem_singleton_self _)
  have B (f: Mkt m B e p → Train m B e) (h : Continuous f) (g: ∀ x∈trainP m B e p, release (f x)∈payer m B e) : Continuous (fun x:trainP m B e p=>stayX (f x.val)) := by
    let t := fun x:Mkt m B e p => release (f x)
    let F := fun x:Mkt m B e p=> ((t x).1,slot m (t x).2)
    have ht : Continuous t:= releaseCt.comp h
    have hx : Continuous F:= (continuous_fst.comp ht).prodMk ((slot_cont m).comp (continuous_snd.comp ht))
    exact continuousOn_iff_continuous_restrict.mp ((dress _ _ _ he he none b).comp hx.continuousOn (fun x k=> g x k)) -- tune
  exact (Continuous.subtype_mk (B _ east_cont (fun _=>furn)) _).prodMk (Continuous.subtype_mk (B _ west_cont (fun _=>yarn L)) _)
def greenF (L : Wood B p) (b : Room B e) (c : Phase.Part m B) (f : TwinK (codify (m:=m) (B:=B) c)→ℂ) (x : Mkt m B e p) := @dite _ (x∈trainP m B e p) (Classical.propDecidable _) (fun h=> f (silver L b c ⟨x,h⟩)) (fun _=> 0)
lemma againC (z:IndexK) : Continuous (againK z) := by apply Continuous.subtype_mk; exact (continuous_fst.comp continuous_subtype_val).prodMk (continuous_fst.comp continuous_subtype_val)
def Coin (S : Stamp m B) (f : Mkt m B e p→ℂ) (u:ℝ):Prop := Manifest (wagon m B e p) f u (pavilion m B S) (chairs m B S) ∧
    ∀ x∈trainP m B e p, Agrees (walls m B S) x.1.val.1.val x.1.val.2.val→ f x=0
variable {z : Stamp m B}
def speedL (L : Wood B p) (b : Room B e) (c : Phase.Part m B) (f : TwinK (codify (m:=m) (B:=B) c)→ℂ) := greenF L b c (fun t=>(f t-f (againK _ t))/2)
lemma speed_at {x : Mkt m B e p} (g:x∈trainP m B e p) (c : Phase.Part m B) (f) : speedL L b c f x=(f (silver L b c ⟨x,g⟩)-f (againK _ (silver L b c ⟨x,g⟩)))/2:= dif_pos g
lemma silverTrip (x : Mkt m B e p) (h : x∈trainP m B e p) (g) : (hill x.1 g,partner m B g x.2)∈trainP m B e p := by
  change barF (wagon m B e p) (hill x.1 g,partner m B g x.2)≠0; exact fun k=> h ((wagon m B e p|>.mass g x.1 x.2).symm.trans k)
lemma silverSame {x : Mkt m B e p} (h : x∈trainP m B e p) (g : Court m B) : ∀ k, silver L b c (⟨(hill x.1 g,partner m B g x.2),k⟩:trainP _ _ _ _)=bog (codify (m:=m) (B:=B) c) g (silver L b c ⟨x,h⟩) := by
  intro k; apply Subtype.ext; apply Prod.ext
  · exact Subtype.ext (visiting (eastK x) g)
  exact Subtype.ext (visiting (westK x) g)
omit b L
lemma againTilt (z:IndexK) (p:TwinK z) (k:Geometry z.1): againK z (bog z k p)=bog z k (againK z p) := rfl
lemma mintCoin (S:Stamp m B) (f : Mkt m B e p→ℂ) {u:ℝ} (P:0≤u) (c : ContinuousOn f (trainP m B e p)) (k : ∀ x∈trainP m B e p, ‖f x‖≤u) (l : ∀ x∈trainP m B e p,∀ y∈trainP m B e p,Agrees (walls m B S) x.1.val.1.val y.1.val.1.val → Agrees (walls m B S) x.1.val.2.val y.1.val.2.val → AgreeF (chairs m B S) x.2 y.2→ f x=f y) (v : ∀ x∈trainP m B e p,∀ g,f (hill x.1 g,partner m B g x.2)=f x) (w : ∀ x∈trainP m B e p, Agrees (walls m B S) x.1.val.1.val x.1.val.2.val→ f x=0) : Coin S f u := by
  refine ⟨⟨P,chair_pad,k,fun _ _=> Algebra.mem_top,c,fun x=> nested_ch S,?_,fun k i t=>scents (S:=S) (e:=e) (H:=1) le_rfl k.1 i t,fun g x h=> (v x h g).symm⟩,w⟩
  intro x y u j a V; obtain ⟨h,g⟩:=a
  apply l _ u _ j _ _ V
  · rw [←mount_p]; exact h
  rw [←mount_p]; exact g
include L b
lemma speed_cost {f : TwinK (codify (m:=m) (B:=B) c)→ℂ} (h : Element (binS (codify (m:=m) (B:=B) c)) z K f) : Coin z (speedL L b c f) K := by
  let Z:=codify (m:=m) (B:=B) c; let D := trainP m B e p; let Y:=speedL L b c f
  apply mintCoin _ Y h.posT
  · let G:= fun t: TwinK Z=> (f t-f (againK Z t))/2
    have he : Continuous G:= (h.continuousE.sub (h.continuousE.comp (againC (L:=L) (b:=b) Z))).div_const _ -- tune
    refine continuousOn_iff_continuous_restrict.mpr ((he.comp (silverC L b c)).congr (fun x=> (speed_at L b x.property c f).symm))
  · intro x p; unfold Y; rw [speed_at L b p,norm_div]; norm_num; apply div_le_of_le_mul₀ (by positivity) h.posT; exact (norm_sub_le ..).trans ((add_le_add (h.norms _) (h.norms _)).trans_eq (by ring)) -- tune
  · intro x v₀ y w g k P
    let s:=silver L b c (⟨x,v₀⟩:D); let t:=silver L b c (⟨y,w⟩:D); let dx:= stayX (eastK x); let dy:= stayX (eastK y); let u := stayX (westK x); let v:= stayX (westK y)
    have he : vacancy z dx dy=0 := station_read z none _ _ g trivial (fun (i:Spot m) (h:i∈chairs m B z ×ˢ univ)=> P i.1 (mem_product.mp h).1) -- need specify A
    have hg : vacancy z u v=0 := station_read z none _ _ k trivial (fun i h=> P i.1 (mem_product.mp h).1)
    have hp := h.varies s t; rw [show (binS Z).eval z s t=vacancy z dx dy+vacancy z u v from rfl,he,hg,zero_add,mul_zero] at hp
    have hx:= h.varies (againK Z s) (againK Z t); rw [show (binS Z).eval z (againK Z s) (againK Z t)=vacancy z dx dy+vacancy z dx dy from rfl,he,zero_add,mul_zero] at hx; unfold Y; rw [speed_at L b v₀, speed_at L b w, show f s=f t from sub_eq_zero.mp (norm_le_zero_iff.mp hp),show f (againK Z s)=f (againK Z t) from sub_eq_zero.mp (norm_le_zero_iff.mp hx)] -- tune
  · intro x l g; have he := silverSame (c:=c) L b l g (silverTrip L b x l g); unfold Y; rw [speed_at L b (silverTrip L b x l g) c f,speed_at L b l, he,againTilt, show f (bog Z g _) = _ from h.gauge g _,show f (bog Z g _) = _ from h.gauge g _]
  intro x l k; let u := stayX (eastK x); let v := stayX (westK x)
  have he : vacancy z v u=0 := station_read z none _ _ (fun i g p=> (k i g p).symm) trivial (fun i p=>rfl)
  have hv : vacancy z u u=0 := waivered z (fun _ _=>rfl) (fun _ _ _=>rfl)
  let s:= silver L b c (⟨x,l⟩:D); have hz : (binS Z).eval z s (againK Z s)=0 := add_eq_zero_iff_of_nonneg hv.ge he.ge|>.mpr ⟨hv,he⟩
  have hp:= h.varies s (againK Z s); rw [hz,mul_zero] at hp; unfold Y; rw [speed_at L b l]; change (_:ℂ)/2=0; rw [show f s-f (againK Z s)=0 from norm_le_zero_iff.mp hp,zero_div]
end
end YM.CF.Delta
