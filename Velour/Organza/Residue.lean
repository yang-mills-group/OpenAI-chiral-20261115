import Velour.Organza.District
/-! Operator-valued detector recovers all positive prices.
Equivalence of invariant subsystems; applies also to differences,
intertwiners (via graphs), etc.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL

local notation "U" => S.unit.translation
local notation "M" => S.liftL








def LocalTest (f:Test4): Prop:= HasCompactSupport ⇑f

private lemma full
    (v y:E4→ℂ)(e: Continuous v) (r:Continuous y)
    (h:∀ f,LocalTest f→ ∫ b, f b • v b = ∫ b, f b • y b):v=y:= by
    rw [← e.ae_eq_iff_eq (μ:=volume) r]


    refine ae_eq_of_integral_contDiff_smul_eq e.locallyIntegrable r.locallyIntegrable
         (fun z k u=>?_ )
    let q:= u.comp_left ofReal_zero
    let w:=q.toSchwartzMap (ofRealCLM.contDiff.comp k)
    simp_rw [Complex.real_smul]
    exact h w q

local notation "α" => S.dangle
lemma rasp_inner (X:H.Op)(f:Test4)(v w:H.space):
 ∫ b:E4,f b • inner ℂ v (α b X w) = inner ℂ v (S.rasp X f w):= by
   rw [rasp_apply,←integral_inner (S.unsoiled ..)]
   simp only [inner_smul_right, smul_eq_mul]

lemma rasp_recovers (X Y:H.Op)(v w:H.space)
 (p:∀f,LocalTest f → inner ℂ v (S.rasp X f w)= inner ℂ v (S.rasp Y f w)):
 inner ℂ v (X w)=inner ℂ v (Y w):= by
   have k:=full (fun b=> inner ℂ v (α b X w)) (fun b=>inner ℂ v (α b Y w))
     (continuous_const.inner (S.dangle_cont ..)) (continuous_const.inner (S.dangle_cont ..))
     (fun f q=> (S.rasp_inner ..).trans ((p f q).trans (S.rasp_inner ..).symm))
   have z:=congrFun k 0
   dsimp only [dangle] at z; rw [neg_zero,S.unit.origin] at z; exact z


variable {S}
variable {N:Submodule ℂ H.space}{Q J:ℝ≥0→H.Op}{T V:S.Detector}

lemma Car.fromDistrict (h:S.Car N)(g:IsClosed (N:Set H.space)){x:H.space}(e:x∈N)
 (A:Set H.space)(c:IsClosed A) (b:∀ y:D,y.val∈N→ y.val∈A): x∈A:=by
   have p:Tendsto (fun t=> E t x) (𝓝[>] (0:ℝ≥0)) (𝓝 x):= by
      rw [show x = x from rfl] -- test
      have k := ((S.continuousE x).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))
      rw [show E (0:ℝ≥0) x=x from by rw [S.eZero];rfl] at k; exact k
   exact c.mem_of_tendsto p (Eventually.mono self_mem_nhdsWithin fun t r=>
      b ⟨E t x,S.muslin_cure t r x⟩ (h.turns g t e))

/-- Recovery (on the part of Hilbert space where the real fields are known). -/
lemma Instates.sufficient (h:S.Instates Q T)(k:S.Instates J V)
 (g:IsClosed (N:Set H.space))(c:S.Car N)
 (b:∀f, LocalTest f → ∀v:D,v.val∈N → T f v=V f v)
 {d:ℝ≥0}(p:0<d):
  EqOn ⇑(Q d) (J d) (N:Set H.space):=by
  intro x e; apply c.fromDistrict g e {x|Q d x=J d x} (isClosed_eq (Q d).continuous (J d).continuous)


  intro v r
  have t (f) (q:LocalTest f):
      S.rasp (Q d) f v.val=S.rasp (J d) f v.val:= by
      rw [← labelled_coe, ←labelled_coe, h.guard f d p, k.guard f d p]
      exact congrArg (fun x:D=>(G d x).val) (b f q (G d v) (c.turns g d r))
  exact ext_inner_left ℂ (fun u=>S.rasp_recovers _ _ _ _ (fun f q=> congrArg (inner ℂ u) (t f q)))

lemma Instates.recovers (h:S.Instates Q T)(k:S.Instates J T){d:ℝ≥0}(p:0<d) : Q d=J d:=
  ContinuousLinearMap.ext fun x=> h.sufficient k (N:=⊤)
    isClosed_univ (fun _ _ _=>trivial) (fun _ _ _ _=>rfl) p (x:=x) trivial
#print axioms Instates.sufficient

def Keeps (N:Submodule ℂ H.space)(T:S.Detector): Prop:=
   ∀ f, ∀ v:D, v.val∈N → (T f v).val∈ N
def Kept (N:Submodule ℂ H.space)(Q:ℝ≥0→H.Op): Prop:=
   ∀ d, 0<d → MapsTo (Q d) (N:Set H.space) N


lemma Instates.kept (h:S.Instates Q T)(g:IsClosed (N:Set H.space))(c:S.Car N)
 (b:∀f, LocalTest f → ∀ v:D,v.val∈N→ (T f v).val∈N): Kept N Q:=by
   intro d r x e
   refine c.fromDistrict g e ((Q d) ⁻¹' (N:Set H.space)) (g.preimage (Q d).continuous) (fun v p=>?_ )
   refine (orthogonal_money _ g _).mpr fun y u=>?_
   have t (f) (q:LocalTest f): S.rasp (Q d) f v.val∈N:=by
      rw [←labelled_coe, h.guard f d r]
      exact c.turns g d (b f q (G d v) (c.turns g d p))
   have z:S.rasp 0=0:=by simpa using S.rasp_cutoff 0 0
   have e:=S.rasp_recovers (Q d) 0 y v.val (fun f q=>by
       rw [(N.mem_orthogonal' _).mp u _ (t f q), z]; simp)
   simpa using e

lemma rasp_sits (g:IsClosed (N:Set H.space))(c:S.Car N)
 (X:H.Op)(b: MapsTo X (N:Set H.space) N) (f:Test4):
 MapsTo (S.rasp X f) (N:Set H.space) N:= by
   intro x e
   refine (orthogonal_money _ g _).mpr fun y u=>?_
   rw [←rasp_inner]
   have t(v:E4): α v X x∈N:= c v (b (c (-v) e))
   have q(v:E4): inner ℂ y (α v X x)=0:= (N.mem_orthogonal' _).mp u _ (t v)
   simp [q]


lemma Instates.keeps (h:S.Instates Q T)(g:IsClosed (N:Set H.space))(c:S.Car N)
 (b:Kept N Q): Keeps N T:=by
   intro f v e
   exact g.mem_of_tendsto (h.meet f v) (Eventually.mono self_mem_nhdsWithin fun t p=>
       rasp_sits g c _ (b t p) f e)

variable {L:Submodule ℂ S.muslin}

lemma Mobile.host (m:S.Mobile L)(h:S.Instates Q T)
 (b:∀f, LocalTest f → ∀v∈L, T f v∈L):
    Keeps (S.district L) T ∧ Kept (S.district L) Q:=by
   have g:IsClosed (S.district L:Set H.space):=Submodule.isClosed_topologicalClosure _
   have u: Kept (S.district L) Q:= by
      refine h.kept g m.car fun f p v e=> ?_
      obtain ⟨x,y,q⟩:=m.core e
      have t: Tendsto (fun i=>(T f (x i)).val) atTop (𝓝 (T f v).val):=
          ((h.touch.surges (tendsto_const_nhds (x:=f))) _ _ q).plain
      refine g.mem_of_tendsto t (Eventually.of_forall fun i=>?_ )
      exact (L.map S.muslin.subtype).le_topologicalClosure ⟨_, b f p _ (y i), rfl⟩
   exact ⟨h.keeps g m.car u,u⟩
#print axioms Mobile.host

