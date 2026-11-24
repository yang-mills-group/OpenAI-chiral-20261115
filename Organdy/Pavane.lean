import Organdy.Emery
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


open _root_.Zephyr.Chern
open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

variable {N:Side}
local notation "Ω"=> Single N

/-- Sweep conjugation on ℂ matrices, as an additive map to move slots. -/
def echoPlus (s:Sweep N) : Op Ω→+Op Ω where
  toFun:=ech s
  map_zero':=by simp [ech,win_z]
  map_add' x y:=by simp [ech]
lemma plusSee (s:Sweep N) (B:Op Ω): echoPlus s B=ech s B:=rfl
lemma echoProd (s:Sweep N) (x y:Op Ω): ech s (x*y) = ech s x * ech s y:=by simp [ech]

def ebony (s:Signed) : ℂ:=if detX s then -1 else 1
lemma ebb(U V: Op Ω)(r:Signed) :
    swapX (detX r) U - swapX (detX r) V=ebony r • (U-V):=by
    rw [ebony]
    cases detX r
    · simp [swapX]
    · simp only [swapX, if_true, neg_smul, one_smul]
      abel
variable (P:Spine)(i k t:ℕ)
local notation "Λ"=>P.par
local notation "N'"=> age P.run i t
local notation "KL"=> (P.run.voyage i).CapeT t
local notation "d'"=> (Λ).d
local notation "πP" => PresN P i k t
local notation "Ω'" => Single N'

lemma amberTip (s:Sweep N')(U:Pane N')(h :Guard U d')
    (R:Op Ω'):
    (julStep s (cellPay πP R) (profile U))=
        ebony s.s • cellPay πP (ech s⁻¹ R) (profile U):= by
    let F:=πP (profile (flashA s U)) - tickA N'
    have hπ:ech s (πP (profile U)) = swapX (detX s.s) (πP (profile (flashA s U))):=by
       have ht:JetS s.s s.charge (detX s.s) (spinU s.charge s.s):=spinZ ..
       have he:= (Λ).J.gran.trans ((P.run.voyage i).ownership t).size
       have b:1≤ (Λ).K.j:=by rw [(Λ).kJ];decide
       exact funde_f (castX s) (xtra _) _ ht U _ b _ _ ((Λ).V.note.fields_one _ ((Λ).U.needed.trans he)) (h.shrink (Λ).U.gem)

    have hτ:ech s (tickA N')=swapX (detX s.s) (tickA N'):=by
       rw [touchP]
       exact tickR (castX s) (xtra _) _ (spinZ ..) N'
    let G:=πP (profile U) - tickA N'
    have e:ech s G= ebony s.s • F:=by
        unfold G F
        have E:=map_sub (echoPlus s) (πP (profile U)) (tickA N')
        simp only [plusSee,hπ,hτ,ebb] at E; exact E
    have u: ech s⁻¹ F=ebony s.s • G:=by
        have z := (_root_.congrArg (ech s⁻¹) e)
        rw [Sour.paceK,mul_inv_cancel,beat_x,ebony] at z
        rw [ebony]
        by_cases p:detX s.s = true
        · simp only [p,↓reduceIte,neg_smul,one_smul] at z ⊢
          have x:ech s⁻¹ (-F)=-(ech s⁻¹ F):=map_neg (echoPlus s⁻¹) F
          rw [z,x,neg_neg]
        · rw [if_neg p,one_smul] at z ⊢; rw [z]
    rw [julStep, ← Levier.veil_p]
    change ech s⁻¹ (F*R)=ebony s.s • (G*ech s⁻¹ R)
    rw [echoProd,u,smul_mul_assoc]

abbrev lightTip (y:Site N') :=Matrix.trace (cellPay πP (millQ y) (profile 1))

lemma lightTip_move (s:Sweep N')(u:s.charge=false) (y:Site N'):
 lightTip P i k t y=ebony s.s * lightTip P i k t (occupant s y) :=by
 have z :Guard (1:Pane N') d':= petal_idle (stream N') ▸ (petals_safe (stream N') (Λ).dpos).self_of_nhds
 have h:= congrArg Matrix.trace (amberTip P i k t s 1 z (millQ y))
 rw [julStep, ← Levier.veil_p,show stir _ _ (1:Pane N')=(1:Pane N') from flashes_clear s,ech_free,
    movedMill, Matrix.trace_smul,smul_eq_mul] at h
 have e:(s⁻¹).charge=false:=u
 rw [e] at h
 exact h
lemma lightTip_same (y:Site N'):lightTip P i k t y= lightTip P i k t 0:=by
    have h:=lightTip_move P i k t (taxiPlus y) rfl 0
    have w: occupant (taxiPlus y) (0:Site N')=y:=by
        apply unaryN
        rw [occupant, Shape.nodex]
        change boxA (taxiPlus y) (node 0)=_
        rw [platforms,zero_add]
    have z: ebony (taxiPlus y).s=1:= by change ebony 1=1; simp [ebony,det_i]
    rw [w,z,one_mul] at h; exact h.symm

lemma lightTip_vanish (y:Site N'): lightTip P i k t y=0:=by
 let s:Sweep N' := ⟨Signed.mirror 0,0,false⟩
 have h:=lightTip_move P i k t s rfl y
 have w:ebony s.s= -1:=by simp [ebony,s,det_t]
 have q:lightTip P i k t (occupant s y)=lightTip P i k t y:=(lightTip_same ..).trans (lightTip_same P i k t y).symm -- syntax
 rw [w,q] at h
 linear_combination h/2

lemma lightFull_vanish (m:ℕ):
 Matrix.trace (fullPay πP m (profile 1))=0:=by
 let Q:=fun (_:ℕ)(B:Op Ω')=> Matrix.trace (cellPay πP B (profile 1))=0
 apply boxProp Q m (List.ofFn (id:Axis→Axis)) (0:Site N') _ _ millQ
 · intro y _; exact lightTip_vanish ..
 · simp [Q,cellPay]
 intro _ _ a b h w; unfold Q cellPay at h w ⊢; rw [mul_add,Matrix.trace_add,h,w,zero_add]

abbrev boughtTurn (s:Sweep N)(m:ℕ):= ech s⁻¹ (windmill 0 m)
lemma payRotated (m:ℕ):
 ∃ δ:ℝ,0<δ∧∀ᶠ t in atTop, ∀ i k,∀ s:Signed,
   Rising (((2*m)^4:ℕ)*δ)
     (dropArc (stream _) (cellPay (PresN P i k t) (boughtTurn (polestar _ s) m))):=by
 obtain ⟨δ,r,h⟩:=payCellsEvery P (Occup (12*m+1))
 refine ⟨δ,r,?_⟩
 filter_upwards [h] with t' z i' k' s
 let n:=age P.run i' t'
 let f:=echoPlus ((polestar n s)⁻¹)
 let M:=PresN P i' k' t'
 let Q (u:ℕ)(B:Op (Single n)):= Rising (u*δ) (dropArc (stream _) (cellPay M (f B)))
 refine boxProp Q m (List.ofFn (id:Axis→Axis)) (0:Site n) ?_ ?_ millQ ?_
 · have h: dropArc (stream _) (cellPay M 0) = fun _=>0:=by funext; simp [cellPay,dropArc]
   have r := Bloom.constant 0
   unfold Q
   rw [map_zero,h]
   refine ⟨r.1,?_⟩
   rw [r.bud_eq]
   simp
 · intro a b U V u v
   unfold Q
   rw [Nat.cast_add,right_distrib,map_add,show cellPay M (f U+f V)=cellPay M (f U)+cellPay M (f V) by funext;simp [cellPay,mul_add]]
   exact Rising.dropSum u v

 intro y e
 unfold Q
 let x:=occupant (polestar n s) y
 have u:f (millQ y)=millQ x:=movedMill (polestar n s) y -- may inference fail
 rw [Nat.cast_one,one_mul,u]
 have g:separation 0 y≤12*m:= by change separation 0 y ≤ 4*(3*m) at e; omega
 exact (wrap_lift x) ▸ z i' k' _ (slipIn x _ (nearbyMill s m y g))
