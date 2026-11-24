
import SatinPP.Turntable
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
    (l u:ℝ)(A:H.Op)(g:Test4)
abbrev slip (a:Axis):= Hierarchy.Seld.shade (basis a)
lemma Band.slip {l u:ℝ}{g:Test4}(r:Band a l u g):Band a l u (slip a g):=by
 have k:tsupport (Silk.slip a g) ⊆ tsupport g:=SchwartzMap.tsupport_lineDerivOp_subset (basis a) g
 exact ⟨r.wide.of_isClosed_subset (isClosed_tsupport _) k,fun p t=>r.snug p (k t)⟩
local notation "J"=>coat S l u A
local notation "R"=>saucer S
lemma sideways_sheath {b:ℝ}(h:0<b): sideways b∈sheath:=by
 constructor
 · simp
 exact mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr h.ne')) I_ne_zero
lemma coat_pull_edge {b:ℝ}(h:0<b):
 let z:=sideways b; J g z * R= R*J g z + z⁻¹ • (R * J (slip a g) z * R):=by
 let f:=rev a h g
 have e:εpref a f=(sideways b)⁻¹ • rev a h (slip a g):=by
   change I • slip a f=_
   rw [show slip a f=_ from rev_shade ..,smul_smul]
   have s: I * ((b⁻¹):ℂ)=(sideways b)⁻¹:=by
      unfold sideways; rw [mul_inv_rev,inv_neg,inv_I,neg_mul_neg]
   rw [s]


 let L:=S.edge (-l*b)
 let P:=S.edge (u*b)
 let z:=sideways b
 let B:=valise S A f
 let C:=valise S A (rev a h (slip a g))
 have p: B * R=R * B + R * (z⁻¹ • C) * R := by
   change valise S A f * R=_
   rw [orion,e,show valise S A ((sideways b)⁻¹ • rev a h (slip a g))=
         z⁻¹ • C from map_smul (barren S A) z⁻¹ _]
 change J g (sideways b) * R =R * J g (sideways b)+ z⁻¹ • (R *J _ (sideways b)*R)
 rw [coat_edge _ _ _ _ _ h,coat_edge _ _ _ _ _ h]
 change L * B * P * R=R * (L * B * P) + z⁻¹ • (R * (L * C * P) * R)
 have hl:L * R=R * L:=(cupL S _).eq.symm
 have hr:P * R=R * P:=(cupL S _).eq.symm
 rw [mul_assoc _ P,hr,←mul_assoc, mul_assoc L B,p,mul_add]
 rw [←mul_assoc L R, hl,mul_smul_comm, add_mul]
 simp only [mul_assoc,mul_smul_comm,smul_mul_assoc,hr,←hl]


 simp only [←mul_assoc,hl]
lemma coat_pull (r:Band a l u g) (z:ℂ) (h:z∈sheath):
    J g z * R= R*J g z + z⁻¹ • (R * J (slip a g) z * R):=by
 ext1 x; apply sub_eq_zero.mp
 let f(z:ℂ):= J g z (R x) - (R (J g z x)+ z⁻¹ • (R (J (slip a g) z (R x))))
 have hf: Harbor f:=
   (coat_harbor S l u A r (Harbor.const _)).sub
    (((coat_harbor S l u A r (Harbor.const _)).pass R).add
      (Harbor.tInv.smul ((coat_harbor S l u A r.slip (Harbor.const _)).pass R)))
 exact (vanish_seam hf le_rfl (zero_lt_one) (fun b v=>
    sub_eq_zero.mpr (DFunLike.congr_fun (coat_pull_edge S l u A g v.1) x))) h

def overture: ℕ→Test4→ℂ→H.Op
| 0,g,z=>coat S l u A g z
| n+1,g,z=> overture n g z + z⁻¹ • (overture n (slip a g) z*R)
local notation "B" => overture S l u A
variable {g} (r:Band a l u g)


include r in
lemma overture_harbor (n:ℕ){y:ℂ→H}(h:Harbor y):Harbor (fun z=>B n g z (y z)):=by
 induction n generalizing g y with
 | zero=>exact coat_harbor S l u A r h
 | succ n ih=>
   have a₁:=ih r h
   have a₂:=Harbor.tInv.smul (ih r.slip (h.pass R))
   exact a₁.add a₂
include r in
lemma overture_price (n:ℕ)(z:ℂ)(h:z∈sheath):J g z*Cache S n=Cache S n *B n g z:=by
 induction n generalizing g with
 | zero=> simp [overture,Cache]
 | succ n ih=>
    let K:=Cache S n; let f:=slip a g
    calc
     _= (J g z*R)*K:=by unfold Cache; rw [pow_succ',mul_assoc]
     _= (R*J g z+ z⁻¹ • (R*J f z*R))*K:=by rw [coat_pull S l u A g r z h]
     _= R*(J g z*K)+z⁻¹ • (R*(J f z*K)*R):=by
        simp only [add_mul,mul_assoc,smul_mul_assoc, show R*K=K*R from (Commute.self_pow _ _).eq]
     _ = _:=by rw [show J g z*K=_ from ih r,show J f z*K=_ from ih r.slip,overture,mul_add]
               dsimp only [K,f,Cache]; rw [pow_succ']; simp only [mul_assoc,mul_smul_comm]


open Classical
local notation "W"=> Bench S
def panel (g:Test4)(z:ℂ):W→ₗ[ℂ] W:=
 if h:Band a l u g ∧ z∈sheath
 then park S (J g z) (fun n=>⟨B n g z,overture_price S l u A h.1 n z h.2⟩)
 else 0
def Wick (g:Test4) (d:ℕ)(z:ℂ):W→ₗ[ℂ] W:=
 (hill S d).comp ((panel S l u A g z).comp (hill S d))
variable (d:ℕ)(z:ℂ)(Y:Bench S)
include r
lemma pane (h:z∈sheath): (panel S l u A g z Y).val= J g z Y.val:=by
 unfold panel; rw [dif_pos ⟨r,h⟩]; rfl
local notation "D"=>Wick S l u A
lemma wPaid (h:z∈sheath):
  Cache S d (D g d z Y).val= J g z (hall S d Y):=by
  change Cache S d (hall S d (panel S l u A g z (hill S d Y)))=_
  rw [releases,pane S l u A r z _ h];rfl
lemma Wick_graph (h:z∈sheath)(m:ℕ):
  hall S m (D g d z Y)= B (d+m) g z (hall S (d+(d+m)) Y):=by
 change hall S m (hill S d (panel S l u A g z (hill S d Y)))=_
 rw [hill_comb,panel,dif_pos ⟨r,h⟩,park_κ S (d+m) _ _ _ _ (overture_price S l u A r _ z h),hill_comb]
omit r


def Road (S:OS.Semigroup H a)(Y:ℂ→Bench S):Prop:=∀m,Harbor (fun z=>hall S m (Y z))
lemma road_const (Y:Bench S):Road S (fun _=>Y):=fun _=>Harbor.const _
lemma Road.under {S:OS.Semigroup H a}{Y:ℂ→Bench S}(h:Road S Y):Harbor (fun z=>(Y z).val):=
  (h 0).use fun z _=>(home S (Y z)).symm

include r in
lemma Wick_harbor {Y:ℂ→Bench S}(h:Road S Y):
 Road S (fun z=>D g d z (Y z)):=fun m=>
   (overture_harbor S l u A r (d+m) (h _)).use (fun _ v=> Wick_graph S l u A r d _ _ v m)

-- shutter, open to a duration c
def shutter (c:ℝ)(z:ℂ):Bench S→ₗ[ℂ]Bench S:=
 park S (tide S (infer z c)) (autumn S _
   (((cupL S _).mul_right (cupE S _)).symm))
-- time boundary walls
def border (t:ℝ):Bench S→ₗ[ℂ]Bench S:= usher S (t • basis a)
lemma border_val (t:ℝ) (Y:W):(border S t Y).val= S.edge t Y.val:=by
 change M S _ _=_; rw [timeslot];rfl
lemma border_pay (t:ℝ)(Y:W) : hall S d (border S t Y)=S.edge t (hall S d Y):=by
 rw [←timeslot, border,usher,park_κ S d _ _ _ _ ((tread S _).symm.pow_right d)]


lemma border_march (t v:ℝ)(Y:W):border S t (border S v Y)= border S (t+v) Y:=by simp [border,ushe,add_smul]
lemma shutter_graph(c:ℝ):
 hall S d (shutter S c z Y)= tide S (infer z c) (hall S d Y):=park_κ S d _ _ _ _
        ((((cupL S _).mul_right (cupE S _)).symm.pow_right d))
lemma infer_side (t c:ℝ):infer (sideways t) c= sideways (c*t):=by
 unfold sideways infer;push_cast;ring
lemma shutter_edge(c t:ℝ):shutter S c (sideways t)=border S (c*t):=by
 ext1 w; apply Subtype.ext; rw [border_val]
 change tide S _ _=_
 rw [infer_side,tide_edge];rfl
lemma shutter_harbor (c:ℝ)(p:0<c) {Y:ℂ→W}(h:Road S Y):Road S (fun z=>shutter S c z (Y z)):=by
 intro m; let f(z:ℂ):=hall S m (Y z)
 have t:Harbor (fun z=>tide S (infer z c) (f z)):=by
    constructor
    · have C :Continuous (fun t:ℂ × H.space=>tide S (infer t.1 c) t.2):=
            tide_c S (continuous_const.mul continuous_fst) continuous_snd
      have h':ContinuousOn f sheath:=(h m).keep
      have e:=C.comp_continuousOn (continuousOn_id.prodMk h')
      exact e


    · apply DifferentiableOn.analyticOnNhd _ open_inside
      exact (tide_analytic S c p).differentiableOn.clm_apply (h m).free.differentiableOn
 exact t.use (fun _ _=>shutter_graph S m _ _ c)

include r in
lemma Wick_edge {b:ℝ}(h:0<b):
 D g d (sideways b)=(border S (-l*b)).comp
      ((ℑ S A (rev a h g) d).comp (border S (u*b))):=by
 ext1 w; apply Subtype.ext; apply cache_I S d
 let E:= Cache S d
 let L:=S.edge (-l*b)
 let P:=S.edge (u*b)
 have e(v:H): E (L v)= L (E v):= DFunLike.congr_fun ((cupL S _).pow_left d).eq v
 let p:=rev a h g
 let φ:=ℑ S A p d
 rw [wPaid S l u A r d _ _ (sideways_sheath h),coat_edge _ _ _ _ _ h]
 change _=E (border S _ (φ (border S (u*b) w))).val
 rw [border_val,e,show E (φ (border S (u*b) w)).val=_ from Hierarchy.Seld.native S A p _ d,border_pay]
 rfl

#print axioms Wick_harbor
#print axioms Wick_edge
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
