import YM.CF.BProof.Gauss.Month

/- Lifetime settings on the gap transform. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open Prox (Base Show Scope Pup Solo)
open YM.SectorNext.Vacuum.Panel
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {s:Side}(Y:Yard s)(T:PathData SU.group)(M:ℕ)(c:Clip)(θ:ℝ)

/-- Settings before use at any period; later instantiate at functions of y. -/
structure Beam (c:Clip)(P:ℝ)(d:ℕ)(M:ℕ)(y:ℝ) where
 k : ℕ
 n : ℕ
 q : ℝ
 thick : Bin.Qualified (peak c P d M) (Gauss.floor c d) k
 precise : Bin.scope (peak c P d M) (Gauss.floor c d) k ≤ y⁻¹^2
 route {A:Type} [Fintype A](B:Base A)(h:B.dim=3): Journey.Bloc B (Bin.maximum (Gauss.floor c d)) (Bin.pay (peak c P d M)) q (d*3*SU.group.lieDim) (6*M*k) n

def horizon (d:ℕ) (c:Clip)(P:ℝ)(M:ℝ→ℕ)(y:ℝ):= Bin.stride (fun y=>peak c P d (M y)) (fun _=>Gauss.floor c d) 6 y
def frameR (d:ℕ) (c:Clip)(P:ℝ)(M:ℝ→ℕ)(y:ℝ):=6*M y*horizon d c P M y
def lane (d:ℕ) (c:Clip)(P:ℝ)(M:ℝ→ℕ)(y:ℝ):=Bin.stride (fun _=>Bin.maximum (Gauss.floor c d)) (fun y=>Bin.pay (peak c P d (M y))) 2 y
def chargeT (d:ℕ)(c:Clip)(P:ℝ)(M:ℝ→ℕ)(y:ℝ):= Month.rate 3 (frameR d c P M y) (lane d c P M y)
def frameBill (d:ℕ)(c:Clip)(P:ℝ)(M:ℝ→ℕ)(y:ℝ) := Month.boundPL 3 (d*3*SU.group.lieDim) (frameR d c P M y) (lane d c P M y)

/-- uniform PL on this d. `settings` return *one* witness built on these functions. -/
lemma calendar (P:ℝ)(d:ℕ)(M:ℝ→ℕ)(h:0<d)(p:PL fun y=> (M y:ℝ)):
    PL (fun y=>(frameR d c P M y:ℝ)) ∧ PL (fun y=>(lane d c P M y:ℝ))∧ PL (fun y=>(chargeT d c P M y)⁻¹) ∧ PL (fun y=>frameBill d c P M y) ∧ ∀ᶠ y:ℝ in atTop,∃ B:Beam c P d (M y) y,B.k=horizon d c P M y ∧ B.n=lane d c P M y ∧ B.q=chargeT d c P M y := by
 let a:=Gauss.floor c d; let f(y):= peak c P d (M y); have he:PL f:=peak_PL c P d M p; have h':=Bin.buys f he (fun y=>peak_hi c P d (M y)) (floor_p c d h) (floor_le c d)
 let Q(y):= Bin.pay (f y); let u:=Bin.maximum a; let k(y):=frameR d c P M y
 have hk:PL fun y=>(k y:ℝ):=by have hg:=h'.1; unfold k frameR horizon; push_cast; exact ((PL.const 6).mul p).mul hg
 have ha:=peak_hi c P d
 have hU:= Bin.max_ge (p:=1) (a:=a) le_rfl (floor_p c d h) (floor_le c d); have hp1(y:ℝ): Q y≤1:= Bin.pay_hi f (fun y=>ha _) y
 have h'' := Month.can (d:=3) (b:=d*3*SU.group.lieDim) (fun _=>u) Q (PL.const u) (Bin.pay_bill f he (fun y=>ha _)) (fun y=>Bin.pay_pos (ha _) (a:=a) (floor_p c d h) (floor_le c d)) (fun y=>(hp1 y).trans hU) k hk
 have hl: PL (fun y=>(lane d c P M y:ℝ)):=by unfold lane; exact h''.1
 refine ⟨hk,hl,Month.rate_inv_pl _ hk 3 hl,Month.bill_pl _ hk _ _ hl,?_⟩; filter_upwards [h'.2,h''.2] with y hy hz; refine ⟨⟨horizon d c P M y,lane d c P M y,chargeT d c P M y,?_,?_,?_⟩,rfl,rfl,rfl⟩
 · unfold horizon; exact hy.1
 · unfold horizon; exact hy.2
 intro X i B hp; unfold chargeT frameR lane; specialize hz B hp; exact hz

namespace Beam
variable {Y M c} {P y q w:ℝ} (U:Beam c P Y.short M y)
def kP (c:Clip)(P:ℝ)(M:ℕ)(Y:Yard s) := peak c P Y.short M
def aP (c:Clip)(Y:Yard s) := Gauss.floor c Y.short
abbrev horizon' := 6*M*U.k
def ζ := Bin.beam (kP (Y:=Y) c P M) U.k ∘ host Y T M c θ -- synt defs args tune
variable (H:Room Y M)(u:T.Bounds c w P q)(h: θ∈Set.Icc (1/2) 2)(Z:Finset Y.Col)
include u h H
lemma measured :
    let W:= ζ T θ U Z;
    W.IsHermitian∧ Numeric W (Bin.pay (kP (Y:=Y) c P M)) (Bin.maximum (aP (Y:=Y) c))∧ ‖W‖≤Bin.maximum (aP (Y:=Y) c) ∧ ‖1-W*host Y T M c θ Z*W‖≤y⁻¹^2 := by
 let W:=ζ T θ U Z; let V:=host Y T M c θ Z
 obtain ⟨a,b,c,p⟩:= Bin.sun U.k V U.thick (charge_H ..) (numbered Y T M c θ Z H u h.2 h.1); refine ⟨a,b,c,?_⟩; have he: Wᵀ=W:=by simpa using (show W.IsHermitian from a).eq
 change ‖1-W*V*W‖≤_; change ‖1-Wᵀ*V*W‖≤_ at p; rw [he] at p; exact p.trans U.precise
omit u h
lemma ζ_v : Prox.Via (edge Y) (Scope.flags _) (ζ T θ U) U.horizon' := Bin.fareVia (p:=kP c P M Y) U.k _ _ _ (hostP Y T M c θ H) -- tune
lemma held (i j:Stamp Y)(e:i.1∈Z): ζ T θ U Z i j=(1:Pool (Stamp Y)) i j:= by
 have hv: Bin.Badge 1 i (host Y T M c θ Z):= fun j=> by rw [host_row Y T M c θ Z i j H e, one_smul]
 have hx:= Bin.Badge.carries (peak c P Y.short M) hv U.k; rw [Bin.fare_one] at hx; simpa only [one_smul,ζ,Function.comp_apply,kP] using hx j
end Beam
end YM.CF.BProof.Gauss
