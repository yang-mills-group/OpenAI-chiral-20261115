import YM.CF.BPress.Huon.Picnic
/-! Full light.Algebra. Core bound with conditions.h.U.Status.Y.Result.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along
variable {m s N:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u b C':ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Pilot
variable (B0: Born A R X Y) (P: Edition Y)(F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)(W: Recipe (A:=A) T)(r:ℕ)
local notation "Ξ" => Visit A R H
section Defs
variable (ε)
abbrev anchor := ∑ i:Tenor η, money B0 P r i
def logM (V:SlotT A R)(x: Visit A R H) :ℂ:= ((Huon.storm W x V:ℝ):ℂ)+ leftP B0 P F Q r x V + rightP B0 P r x V
def talent(x: Visit A R H):= (Pulse.gaugeY (R:=R) (H:=H) W x+Pulse.comG ε F Q P x) + ((∑ i:Tenor η,paysL P F Q r x i)+ (∑ i,start0 B0 P F Q r x i)) -- tune comG order
abbrev duskWeight (V:SlotT A R)(x: Visit A R H):ℂ:= shapeM x V X ε * Complex.exp (logM B0 P F Q W r V x)
end Defs
variable {B0 P F Q W r} (l: Passports Y T G h P p3 q d ε t v) (p: Budgeting H W τ u D ζ δ C) (tH:Seer H R X k) (p':ShortP X H R r)(a':Mangrove R H W.M)
include p
lemma ykp (x:Ξ): stall ε W F Q P (party A R H x) = Complex.exp (anchor B0 P r)*((∏ V∈Camp x.val H, duskWeight (ε:=ε) B0 P F Q W r V x)*Complex.exp (talent ε B0 P F Q W r x)):=by -- tune arg order dusk
 let U:= party A R H x; let μ:=Wage H W U.val; let v:= Camp x.val H; let ℓ:= logM B0 P F Q W r; let u:= Huon.storm W x; let h:= skew P F Q x; let M:=anchor B0 P r; let g:= maskH R H X (House.read A R x.val) ε; let Qp:=(∏ t∈ v, shapeM x t X ε); let T' := stern0 F Q ε P U
 change Real.exp μ • (g*Complex.exp T')=Complex.exp M*((∏ v∈Camp x.val H,_)*_); unfold duskWeight; rw [prod_mul_distrib,←Complex.exp_sum]; have hx: (μ:ℂ)+T'= (∑ y∈v,ℓ y x)+M+ talent ε B0 P F Q W r x:=by
    have he : μ= (∑ i∈v,u i)+(μ-∑ i,cold H W U.val i):= by rw [show (∑ i∈v,u i)= _ from (StormEq W p x).symm]; abel -- tune
    nth_rw 1 [he]; rw [Complex.ofReal_add,Complex.ofReal_sum]; unfold talent; rw [show T'= (∑ i:Tenor η,h i)+Pulse.comG ε F Q P x from rfl, whole B0 P F Q r x]; unfold ℓ logM; rw [sum_add_distrib,sum_add_distrib,sum_add_distrib]; unfold Pulse.gaugeY; push_cast; unfold M u μ U v party anchor; abel -- tune orientation membership
 rw [Complex.real_smul,Complex.ofReal_exp,mul_left_comm (Complex.exp (μ:ℂ)) g, ←Complex.exp_add,hx,show g=Qp from slate_mask F x ε,Complex.exp_add,Complex.exp_add]; unfold Qp v ℓ; ring -- tune
include l tH p' a' in
lemma sharing (x y:Visit A R H)(V:SlotT A R)(pY:V∈Camp x.val H)(h:V∈ Camp y.val H)(u:Peel.Along x.val y.val (Contour.station Peel.fan V)): duskWeight (ε:=ε) B0 P F Q W r V x=duskWeight (ε:=ε) B0 P F Q W r V y:=by obtain ⟨a,g⟩:= stories (B0:=B0) (F:=F) (Q:=Q) l p' tH x V y u pY h; unfold duskWeight logM; rw [a,g,(seesCold W p a' x V y u).2,shape_read F tH.charter ε u] -- tune explicit
omit p
include l
lemma anchor_cost : ‖anchor B0 P r‖≤(Fintype.card (Site (More (mid m s))):ℝ)*p3.price:=by
 have he:= l.cruise.total p3.pos.le (fun i p=> ?_); swap; · exact Classical.byContradiction (fun t=> let h:=l.point i t; notMem_empty i.1 (show i.1∈(∅:Support η) from p ▸ (show i.1∈ scaffold i from h.2)))
 apply (norm_sum_le ..).trans; refine (sum_le_sum (?_ :∀ i∈ _, ‖money B0 P r i‖ ≤ P.opfee i)).trans (budget_sum he _); intro i p; unfold money; split; exact l.known i _; rw [norm_zero]; exact l.cruise.pos _ -- tune
-- core bound with abs values.Currency.H status counts.
def costY (n:ℕ)(a:ℝ) (L D u:ℕ):ℝ:= (estate 29*L^3*(D+2*u+1):ℕ)*|Real.log a| -- remove n
variable (R C)
def last (b d: ℝ)(w z Q0 u:ℕ):ℝ := -(b/16)*(R.L.val:ℝ)^3*Q0 + C*w - d*z -- tune
variable {R C}
def peakP(r:ℕ)(c:ℝ):=costη R p3 B (mcap X H r)+ costY r c R.L.val B.D X.W.M
-- test
end Pilot
end YM.CF.BPress.Huon
