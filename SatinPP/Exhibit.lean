
import SatinPP.Waterborne
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(g:Test4)
-- ℓ variable at z
def lit (f:E4→H.Op) (p:E4):= Q S p * f p * Q S (-p)

section Gallery
def Held (g:Test4)(f:E4→H.Op):Prop :=
   HasCompactSupport g ∧ ∀p∈tsupport g, ContinuousAt f p
variable {g}{f:E4→H.Op}

private lemma under_spot {X:Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {t:E4→X}
   (c:∀p∈tsupport g, ContinuousAt t p):
  Continuous (fun p=> g p • t p):= by
  classical
  rw [continuous_iff_continuousAt]; intro p
  by_cases hp:p∈tsupport g
  · exact g.continuous.continuousAt.smul (c p hp)
  refine (show ContinuousAt (fun _:E4=> (0:X)) p from continuousAt_const).congr ?_
  filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hp] with x e
  exact (show g x • t x=0 by rw [image_eq_zero_of_notMem_tsupport e,zero_smul]).symm


lemma litC (t:Held g f)(y:H):Continuous (fun p=>g p • lit S f p y):=by
 refine under_spot fun p h=>?_
 have e:Continuous (fun u:E4×H.space=>Q S u.1 u.2):=Q_join S continuous_fst continuous_snd
 have q:Continuous (fun p:E4=> Q S (-p) y):=Q_join S continuous_id.neg continuous_const
 have c:=continuousAt_id (x:=p) |>.prodMk ((t.2 p h).clm_apply q.continuousAt)
 exact e.continuousAt.comp c
lemma litP (p:E4)(y:H):‖lit S f p y‖≤‖f p‖ * ‖y‖:=by
 change ‖Q S p (f p (Q S (-p) y))‖≤_
 have r(t:E4)(x:H):‖Q S t x‖=‖x‖:=S.unitary ..
 rw [r]
 simpa only [r] using (f p).le_opNorm (Q S (-p) y)
variable (t:Held g f)
include t
lemma litI (y:H): Integrable (fun p=>g p • lit S f p y):= (litC S t y).integrable_of_hasCompactSupport
  (t.1.smul_right)
lemma lit_rate : ∃ r, ∀ x, ‖∫ p,g p • lit S f p x‖ ≤ r * ‖x‖:=by
  obtain ⟨c,u⟩:= t.1.bddAbove_image (f:=fun p=>‖f p‖) ((continuousOn_of_forall_continuousAt t.2).norm)


  refine ⟨vial g*c,fun x=>?_⟩
  rw [mul_assoc,vmeets,←integral_mul_const]
  apply norm_integral_le_of_norm_le (g.integrable.norm.mul_const _)
  apply Eventually.of_forall; intro p; simp only [norm_smul]
  by_cases h:p∈tsupport g
  · have v:‖f p‖≤c:=u (mem_image_of_mem _ h)
    exact mul_le_mul_of_nonneg_left ((litP S p x).trans
       (mul_le_mul_of_nonneg_right v (norm_nonneg _))) (norm_nonneg _)
  simp [image_eq_zero_of_notMem_tsupport h]
def casting: H.Op:=
 LinearMap.mkContinuous (σ:=RingHom.id ℂ)
  { toFun y:=∫ p,g p • lit S f p y
    map_add' y x:=by simp only [map_add,smul_add]; exact integral_add (litI S t y) (litI S t x)
    map_smul' b v:=by simp_rw [map_smul,smul_comm _ b];rw[integral_smul];rfl }
  _ (lit_rate S t).choose_spec
omit t
open Classical in
def salon (g:Test4)(f:E4→H.Op) :H.Op:= if q:Held g f then casting S q else 0
lemma salon_val (t:Held g f)(y:H):
  salon S g f y=∫ p,g p • lit S f p y:=by rw [salon,dif_pos t];rfl
end Gallery


variable (A:Stamp H)(l u:ℝ)(z:ℂ)
-- Wick point of charge
def sail (p:E4):H.Op:=paint S A (infer z (fore a l p)) (infer z (aft a u p))
def voyage (g:Test4):H.Op:=salon S g (sail S A l u z)

variable {d m:ℕ}{c:ℝ}(K:Paid S m c A)(r:Band a l u g)(v:z∈inside)
include K r v
variable {S A g l u z}
lemma held_sail:Held g (sail S A l u z):=by
 refine ⟨r.wide,fun p h=>?_⟩; obtain ⟨a₁,a₂⟩:=r.snug p h
 have t:Continuous (fun p:E4=>p a):=by fun_prop
 exact continuousAt_paint (f:=fun p=>infer z (fore a l p)) (g:=fun p=>infer z (aft a u p)) K
    (infer_warm v (sub_pos.mpr a₁)) (infer_warm v (sub_pos.mpr a₂))
    (by unfold infer fore; fun_prop) (by unfold infer aft; fun_prop)
lemma voyage_val(y:H):
  voyage S A l u z g y=∫ p,g p • lit S (sail S A l u z) p y:=salon_val S (held_sail K r v) y

local notation "κ"=>Cache S d
variable {B:H.Op}(e:Role S d A B)
include e
lemma sail_role (p:E4)(t:p∈tsupport g):
 κ*lit S (sail S A l u z) p*κ=entry S l u B z p:=by


 obtain ⟨b,h⟩:=r.snug p t
 let y:=infer z (fore a l p); let w:=infer z (aft a u p)
 have hy:y∈inside:=infer_warm v (sub_pos.mpr b)
 have hw:w∈inside:=infer_warm v (sub_pos.mpr h)
 have k (s:E4) :κ*Q S s=Q S s *κ:=((cupU S _).pow_left _).eq
 have c(n:ℂ)(m:n∈inside)(s:E4):S.F n * Q S s=Q S s * S.F n:= S.stays m _
 change κ*(Q S p * paint S A y w* Q S (-p))*κ=tide S y*Q S p*B*Q S (-p)*tide S w
 rw [←mul_assoc,←mul_assoc,k,mul_assoc,mul_assoc _ (Q S (-p)),←k (-p),
     tide_heat S y hy,tide_heat S w hw,e.suited K y w hy hw]


 rw [
    c _ hy, ←c w hw (-p)]
 simp_rw [mul_assoc]
 rw [←mul_assoc (κ) (parabola S d y),←mul_assoc (parabola S d w) κ,recover _ _ _ hy,change_m _ _ _ hw]

lemma coat_eq:
 coat S l u B g z=κ*(voyage S A l u z g)*κ:=by
 ext1 x
 change _=κ (voyage S A l u z g (κ x))
 rw [coat_val,voyage_val K r v _,← (κ).integral_comp_comm (litI S (held_sail K r v) (κ x))]
 congr 1 with p; rw [map_smul]
 by_cases h:p∈tsupport g
 · rw [←sail_role K r v e p h]; rfl
 simp [image_eq_zero_of_notMem_tsupport h]
lemma opens(Y:Bench S):
  (Wick S l u B g d z Y).val= voyage S A l u z g Y.val:=by
 apply cache_I S d
 rw [wPaid S l u B r _ _ _ (inside_subset_sheath v),coat_eq K r v e]
 change κ (voyage S A l u z g (κ (hall S d Y)))=_; rw [releases]


omit K r v e
def mat (a:Axis)(A:Stamp H)(l u:ℝ)(p:E4):= A (fore a l p) (aft a u p)
variable (r:Band a l u g)
include r K
lemma shore_eq {p:E4}(t:p∈tsupport g): sail S A l u 1 p=mat a A l u p:= by
 unfold sail infer; rw [mul_one,mul_one,paint_real K (sub_pos.mpr (r.snug p t).1) (sub_pos.mpr (r.snug p t).2)]
 rfl
abbrev eu : (1:ℂ)∈inside:=zero_lt_one (α:=ℝ)
lemma shore(y:H):voyage S A l u 1 g y=∫ p,g p • lit S (mat a A l u) p y:=by
 rw [voyage_val K r eu y];congr 1 with p
 by_cases t:p∈tsupport g
 · unfold lit; rw [shore_eq K r t]
 simp [image_eq_zero_of_notMem_tsupport t]


omit K r
lemma Q_star(p:E4):star (Q S p)=Q S (-p):=by
 unfold Q;rw [map_neg,←laneslot,←laneslot,tstar]; rfl
lemma lit_star (p:E4)(f:E4→H.Op):
 star (lit S f p)=lit S (fun p=>star (f p)) p:=by
 unfold lit; rw [star_mul,star_mul,Q_star,Q_star,neg_neg,mul_assoc]
lemma held_star {f:E4→H.Op}(t:Held g f):Held (bar g) (fun p=>star (f p)):=by
 have p:tsupport (bar g) ⊆ tsupport g:= by refine closure_mono ?_
                                           intro x e
                                           contrapose! e;rw [Function.notMem_support] at *
                                           rw [bar_at,e];simp
 exact ⟨t.1.of_isClosed_subset (isClosed_tsupport _) p, fun _ h=>(t.2 _ (p h)).star⟩

lemma salon_star {f:E4→H.Op}(t:Held g f)(x:H):
 star (salon S g f) x=∫ p,star (g p) • lit S (fun p=> star (f p)) p x:=by
 let h:=held_star t
 simp_rw [←bar_at] -- RHS
 apply ext_inner_right ℂ; intro y
 change inner ℂ ((salon S g f).adjoint x) y=_
 rw [ContinuousLinearMap.adjoint_inner_left,salon_val S t y,← inner_conj_symm _ y,
     ← integral_inner (litI S t y),←integral_inner (litI S h x),←integral_conj]
 congr 1 with p
 rw [inner_conj_symm,←lit_star,inner_smul_left,inner_smul_right,bar_at]


 congr 1
 · exact (star_star _).symm
 exact (ContinuousLinearMap.adjoint_inner_left ..).symm
include K r
lemma reverse_shore(y:H):
  star (voyage S A l u 1 g) y
    =∫ p, star (g p) • lit S (fun p=>star (mat a A l u p)) p y:=by
 unfold voyage;rw [salon_star (held_sail K r eu) y];congr 1 with p
 by_cases t:p∈tsupport g
 · unfold lit; dsimp only; rw [shore_eq K r t]
 simp [image_eq_zero_of_notMem_tsupport t]
#print axioms opens
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
