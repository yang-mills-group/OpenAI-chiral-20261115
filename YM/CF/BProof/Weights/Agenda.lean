import YM.CF.BProof.Weights.Burn
import YM.CF.BProof.Mapping.Ledger

/- combine all non-Mark gauge matter into final real log-potential, no ferm.
`Agenda` supplies pledge Paid and coherent domains, schedule inequalities not hypotheses
final, consumed at fixed budget; implementing purchases post CG_T.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Weights
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Release Release.hot Mapping House Pricing Prox Moment Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
local notation "G"=> SU.group
variable {s c': Side}(Y:Yard s)(S:Hall s)(g:Ratio c' s)
variable (M:ℝ→ℕ)(T:PathData G)(θ β:ℝ){R y w v κ:ℝ}{c:Clip}{K:Chart G}{P: Pub G}(p:Model K P c Y.short M R y κ)(u:Room Y (M y))(t:T.Bounds c w R v)(h:θ∈Set.Icc (1/2) 2)(q:BudgetPoint)
variable (x x': Pawn Y) (b:Y.Col)
abbrev Ledger (I:Type*)[Fintype I] (f:Pawn Y→ℝ)(α C:ℝ):= Account.Teller (House.Bed Y c') (Pawn.Proceeds Y S y T θ p.X κ) (fun V a b=> Pawn.Agreed g a b V) I f α C
-- compact condition. energies E,w. force Section window raising G-body.
structure Agenda (A:Chart G)(P:Pub G)(K':ℕ)(C:ℝ) (M:ℝ→ℕ) (c:Clip)(w R κ y k α:ℝ) where
 r : 1 < Deep.D Y -- for gauge weak touch price
 range_cost : 5*M y + 2 < 2*Deep.D Y
 limit : license M Y.short c R y ≤ g.count.val
 coverage : 1+steady c Y.short M R y ≤ g.count.val
 fund : House.Fund Y g S K'
 α_pos : 0≤α
 -- gauge rates use shared small k. NPL license later.
 price : Mapping.Factor g.count.val (expense 0) (expense 0) k α
 price_m : Mapping.Factor g.count.val (up 1) (upward S.X.size S.k K' 1) k α
 stamp : StampC P c Y.short M R κ y
 ink : Ink A C y
 thin : thin C y≤mA y
 jac : 3*k≤ halfC Y.short M c R y
 weak : 3*k≤ uPull w (M y)

variable (C:ℝ){K':ℕ}{j α:ℝ}(k:ValidR c q (M y))(vβ:y≤2*β)(hq:q.threshold=thresh y)(A:Agenda Y S g K P K' C M c w R κ y j α)
-- burns
include A k
-- receipts ea.
include t p u h
variable (e:β≤2*y)
include e hq vβ
def tabPay (gL:ℕ)(P:Pub G)(c:Clip)(M:ℝ→ℕ)(R C:ℝ)(d:ℕ)(y α:ℝ) := House.ply gL 1 α * Weights.tabW P c M R C d y -- ply arg order? `ply (t r)`
lemma convey : Nonempty (Ledger Y S g M T θ p Y.Col (fun x=>∑ b,tabs Y S M T θ β p q x b) α (tabPay g.count.val P c M R C Y.short y α)):=by
 let f(b:Y.Col):= House.ray Y (hide Y g b) 1; let K(b:Y.Col):= tabW P c M R C Y.short y; have hb : 0≤β:=by have ht:=A.stamp.early; linarith
 refine ⟨f,K,(fun b x=> tabs Y S M T θ β p q x b),fun x _=>rfl,?_,fun i x hv=>tabBound Y S M T θ β p u t h q k x i A.stamp A.ink hq hv e hb,fun b=>?_,fun i=>tabs_m Y S M T θ β p t q i,?_⟩
 · exact House.banner Y g 1 K α _ (fun b=> ⟨tabW_pos ..,le_rfl⟩) A.α_pos
 · exact ⟨⟨hide Y g b, House.ray_home ..⟩, House.ray_n Y (hide Y g b) 1⟩
 intro i x y' a v w; exact tab_spark Y S g M T θ β p u t h q k x y' i (f i) v a (House.ray_loan Y g (f i) 1 (by have := A.limit; unfold license at this; omega) (fun a h=>h)) w A.range_cost -- tune
omit e hq vβ k
def WPay (P:Pub G)(c:Clip)(d gL:ℕ)(R:ℝ)(M:ℝ→ℕ)(y j α:ℝ):= tPay c d M R y * TZ 0 gL j α
lemma issue : Nonempty (Ledger Y S g M T θ p (Finset Y.Col) (fun x=>∑ i, issueW Y M T θ p u t h x i) α (WPay P c Y.short g.count.val R M y j α)):=by
 let V:= issueW Y M T θ p u t h; let f(i:Finset Y.Col):= holes Y g i 0; let W:= zCost Y M T θ p u t h
 refine Account.Teller.weak (u:= Function.swap V) (W:=f) (p:=W) (h:=issue_column (T:=id) Y g W 0 j α _ A.price ((w_toll Y M T θ p u t h).weaken id W A.jac le_rfl) (fun i q=> w_roots Y M T θ p u t h i q)) (fun i q=> ?_) (fun i x _=> price_W Y M T θ p u t h x i) (fun i _ a b g' _ _=> issue_same Y g M T θ p u t h a b _ g' i (fun l v=>holed Y g i 0 v)) (fun i=> W_m Y M T θ p u t h i) (fun x v=>rfl)
 obtain ⟨⟨x,hx⟩,k⟩:= w_roots Y M T θ p u t h i q; exact ⟨⟨_,holed Y g i 0 hx⟩, hole_conn _ _ _ 0 k⟩
-- gauge weak postponed exact_channels.
omit u h
abbrev fogBill := weak (s:=s) c q T (M y) β t k -- tune `Y` retained?
variable {p}
-- generic B:Bill for issued. exact equality negative left. cost uses measured tolerance (τ =3*j)
abbrev swage (B: Moment.Bill s G)(x: Pawn Y) := -Charge.left Y (Pawn.put S x y T θ p.X) B
abbrev κ_bound (d gL:ℕ)(j α L:ℝ):= L*TT d 1 1 gL j α
include u
lemma earn {B:Moment.Bill s G}(E:ℝ)(w:B.fine (3*j) E) : Nonempty (Ledger Y S g M T θ p (Support s) (fun x=>swage (p:=p) Y S M T θ B x) α (κ_bound Y.short g.count.val j α E)):=by
 let v(Z:Support s):= if Coop Y Z then 0 else B.amount Z
 let f(Z:Support s)(x:Pawn Y):= if Coop Y Z then 0 else -(B.tax Z (Pawn.put S x y T θ p.X))
 have hv(Z:Support s):0≤v Z:=by unfold v; split; exact le_rfl; exact B.amount_p Z
 have hx:= Toll.shrink id B.amount w v hv (fun i=>by unfold v; split; exact B.amount_p _; exact le_rfl)
 have hh(Z:Support s)(h:v Z≠0): Seek Y Z 1:=by
    have u : ¬ Coop Y Z:=fun g=> h (if_pos g); obtain ⟨x,t⟩:=B.roots Z (by unfold v at h; rwa [if_neg u] at h); exact ⟨Y.gain Z x t (fun i p=> u ⟨i,x,p⟩),t,A.r⟩
 -- select arbitrary Queue only if nz. Lean choose!. queue existence
 choose! H hP using fun Z (h:v Z≠0)=> (show ∃ H:Grid.Sites (Season Y c'),∃ Q:Queue Y g S Z K' 1,H=Q.Z from by obtain ⟨q⟩:= House.can Y g S Z K' A.fund 1 (hh Z h) 1; exact ⟨_,q,rfl⟩)
 refine Account.Teller.weak (u:=f) (W:=H) (p:=v) (House.micro (T:=id) Y g S K' v H 1 1 j α E A.price_m (by have := A.r; have := Deep.D_le Y; omega) hx (fun i p=>?_) ) (fun i p=>?_) (fun i p g=>?_ ) (fun i he x y' p' h₁ h₂=>?_) (fun i=>?_) (fun x p=>?_)
 · exact ⟨hh i p,hP i p⟩
 · obtain ⟨q,v⟩:=hP i p; rw [v]; obtain ⟨x,h,xv⟩:=(hh i p).near; refine ⟨⟨_,q.lunch (Grid.to_collar _ _ (Grid.to_collar _ _ (mem_image_of_mem (addr Y g) h)))⟩,q.funds⟩ -- tune
 · unfold f v; split; rw [norm_zero]; rw [norm_neg]; exact B.enough i _
 · obtain ⟨r,q⟩:= hP i he; unfold f; split; exact rfl; apply congrArg Neg.neg; exact B.stops i _ _ (Pawn.transcript g S x y' i y T θ (Model.X _) u r (q ▸ p') (by have := A.coverage; rw [p.p_hor]; omega) h₁.2.2.1 h₂.2.2.1)
 · unfold f; split; exact measurable_const; exact ((B.meas i).comp (Pawn.put_m ..)).neg
 unfold swage Charge.left; rw [← Finset.sum_neg_distrib]; rw [sum_filter]; refine sum_congr rfl fun i _=>?_ ; by_cases v:Coop Y i <;> simp [v,f]
end YM.CF.BProof.Weights
