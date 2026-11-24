import YM.SU5.FiniteGaugeData.Tower.Sight
import YM.SU5.Reconstruction.UVPrice.Population
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
local notation "U" j:max v:max=> (T.crew j).play v
variable (p:Coupon a Γ)
noncomputable def Live (p:Coupon a Γ): H.Op:= K.E p.dt*T.raw (look a) (fun i=>p.stamp i.val)
noncomputable def Lore (x:H) (p:Coupon a Γ): ℂ:= inner ℂ x (Live K T p x)
@[fun_prop] lemma lore_cont : Continuous (Lore K T):= continuous_pi fun i=> continuous_id.inner (Live K T i).continuous
local notation "R" => Cross a
private def arrive {a:Axis}{Γ:AddSubgroup ℝ}(p:Coupon a Γ): List (CF.Buffered.Afterglow.Tower.Trans a) → Cross a
 | []=>0
 | i::l=> (p.stamp i.val:ℝ) • cross a i.val i.property + arrive p l
private lemma arrive_part (p:Coupon a Γ)(l: List (CF.Buffered.Afterglow.Tower.Trans a))(h:l.Nodup)(i: CF.Buffered.Afterglow.Tower.Trans a) : (arrive p l).val i.val= if i∈ l then (p.stamp i.val:ℝ) else 0:=by
 induction l with
 | nil=>simp [arrive]
 | cons j l ih=>
    obtain ⟨r,u⟩:= List.nodup_cons.mp h
    have he:(arrive p (j::l)).val= (p.stamp j.val:ℝ) • basis j.val + (arrive p l).val:= rfl
    by_cases v:i=j
    · subst j; rw [he]; simp [ih u,r]
    have hx:i.val ≠ j.val:= by intro h; exact v (Subtype.ext h)
    rw [he]; simp [ih u,hx,hx.symm,v]
private lemma arrive_tar (p: Coupon a Γ) : p.displacement=arrive p (look a):=by
 apply Subtype.ext; ext i
 rcases eq_or_ne i a with rfl|h
 · exact (show p.displacement.val i=0 from p.displacement.property).trans (show (arrive p (look i)).val i=0 from (arrive ..).property).symm
 let I:CF.Buffered.Afterglow.Tower.Trans a:= ⟨i,h⟩
 rw [show (arrive p (look a)).val i= if I∈ look a then (p.stamp i:ℝ) else 0 from arrive_part p (look a) (look_one a) I,if_pos (look_all ..)]; exact diameter_at _ i h
variable (A:H ≃ₗᵢ[ℂ] W)
structure Captions : Prop where
 time (t:ℝ≥0) (x:H): A (K.E t x) = S.E t (A x)
 space(i:CF.Buffered.Afterglow.Tower.Trans a)(v:Γ)(x:H): A ((U i v) x) = S.U ((v:ℝ) • cross a i.val i.property) (A x)
variable (W': Captions K T S A)
include W'
theorem rendering(p:Coupon a Γ)(x:H): Coupon.cash S p (A x) = A (Live K T p x):=by
 unfold Coupon.cash Live; rw [arrive_tar]; change S.E p.dt (S.U _ (A x))=A (K.E p.dt _); rw [W'.time]; refine congrArg _ ?_
 suffices h:∀ l:List (CF.Buffered.Afterglow.Tower.Trans a), S.U (arrive p l) (A x) = A (T.raw l (fun i=>p.stamp i.val) x) by exact h _
 intro l; induction l with
 | nil=> rw [arrive,S.uZero, T.raw_nil]; rfl
 | cons i l ih=> rw [arrive, S.space,ContinuousLinearMap.comp_apply, ih,T.raw_step,ContinuousLinearMap.comp_apply,W'.space]
theorem invoice (x:H): Lore K T x= Coupon.tagT S (A x):=by
 funext i
 unfold Lore Coupon.tagT; rw [rendering K T S A W']; exact (A.inner_map_map ..).symm
end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.invoice
