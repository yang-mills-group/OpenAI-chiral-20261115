import YM.CF.BPress.Primary.Price
import YM.CF.BPress.Pf.Anchor
/- £ site roots. includes pigment. exact denominator still by Pose.U Variables. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale
variable {N:Side}{U:Driver N}{A B C:Pledge}
local notation "Z₀"=> U.decks
variable (x:U.Pose)
abbrev slag := shale ((Z₀).keys true x) ((Z₀).keys false x) ((Z₀).A x) ((Z₀).M x) ((Z₀).col x) ((Z₀).col' x)
abbrev real_ := oxide ((Z₀).keys true x) ((Z₀).keys false x) ((Z₀).A x) ((Z₀).M x) ((Z₀).col x 2)
abbrev stark := totalBill ((Z₀).keys true x) ((Z₀).keys false x) ((Z₀).A x) ((Z₀).M x) ((Z₀).col x) ((Z₀).col' x)
def stork(W:Pec.Pride N):= slag x - Nougat.pearls W x.val.G
lemma real_c(i: Single N): (slag x i i).re=(real_ x i i).re:=by unfold slag shale; rw [Matrix.add_apply, realc,imc]; simp [degZ] -- tune
namespace Fare
variable {V:Pledge}(W:Pec.Pride N)
abbrev homeX:= Pf.Anchor.homeF U.Beta.stage
abbrev town(W:Pec.Pride N)(x: U.Pose)(i:Site (More N)):= homeX (U:=U) (stork x W) i
abbrev CostSpec (W:Pec.Pride N) (U:Driver N):= Anchor.Homes V (U.Beta.stage) (fun i=>stork i W)
variable (A B C) (K : Pledge)
local notation "β"=> payA A B C
variable (X:Pledge)(g:Wish U A B C)(S:Grant X A (payA A B C) (stream 1) (Sight.price U.h) U.v U.ε quota) (w:Pec.Lac W K.rate K.price)
include g S
lemma mint(L :Pec.Pride N)(p:Pec.Lac L K.rate K.price) : (X.plus (ζPearl K)).Costs (U.Beta).stage (fun i=>stork i L):=by
 have he:= (S.to_χ (wish U g).gates).1; refine Costs.sub he (Form.pulls (Nougat.ΞPearl L K p) (fun x:U.Pose=>x.val.G) (cont_G.comp continuous_subtype_val) ?_); exact fun i x y=> Plain.ticketS ..
lemma bill (x:U.Pose): (stork x W).trace=stark x-Pec.pigment W x.val.G :=by rw [stork,Matrix.trace_sub,←pigment_c]; exact congrArg (·-_) ((S.to_χ (wish U g).gates).2 x)
omit g S
-- purchase V etc once.
structure bought (E P:Pledge):Prop where
 h : ∀ {I Y D:Type}[LinearOrder I][Fintype I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{T:Raw D I}, Capacity b quota→E.Costs b T→ ∃ U K,Anchor.Homes P b T U K
theorem purchase (U:Pledge):∃ K,bought U K:=by obtain ⟨K,k⟩:=Anchor.site U Form.paid; exact ⟨K,⟨fun _ u=> k ‹_› u⟩⟩ -- tune implicit binder strict
include g
open Pf.Frame
lemma real_move (Y:Mach (More N)) : real_ (moveW x g Y)=twist (tradew N Y) (real_ x):=by
 let A':=U.decks.A; let T:=U.decks.M; let c:=U.decks.col; let W :=tradew N Y; let F : Issued (U.decks.keys true x) (U.decks.keys false x) (A' x) (T x) (c x) (U.decks.col' x) U.v U.ε:=x.property.state; let L:= U.decks.keys true x; let K:=U.decks.keys false x; let y:=moveW x g Y; have ht:=F.rails; have he(h:Bool): twist W (cutM (U.decks.keys h x))=cutM (U.decks.keys h x):= Hole.terra_l ..; obtain ⟨hv,hp⟩:= Pf.Frame.permit_f W F.proj F.she ht (he true) (he false); have hg: A' y=twist W (A' x) := (Driver.body x g Y).a; have hh:T y= twist W (T x):= (Driver.body x g Y).t; have hi :c y 2= congrC W (c x 2):= congrFun (voices x g Y).1 2; change oxide L K (A' y) (T y) (c y 2)=_; rw [hg, hh, hi]; change oxide L K _ _ _=twist W (oxide L K (A' x) (T x) (c x 2)); rw [oxide,oxide,Pf.Frame.staticH (by exact F.near) W,hv,hp, Pf.Frame.billZ_f W F, map_add,map_add,map_add]; exact he true; exact he false -- tune
lemma home_hold (Y:Mach (More N))(i:Site (More N)): (town W (moveW x g Y) i).re= (town W x i).re:=by
 have ht(x:U.Pose): (town W x i).re=(homeX (U:=U) (real_ x) i).re-(homeX (U:=U) (pearls W x.val.G) i).re:=by unfold homeX town homeX Anchor.homeF stork; rw [Complex.re_sum]; simp_rw [Matrix.sub_apply,Complex.sub_re,real_c,sum_sub_distrib,Complex.re_sum]; -- tune
 have he(x:U.Pose): homeX (U:=U) (twist (tradew N Y) (real_ x)) i=homeX (U:=U) (real_ x) i:= Pf.Anchor.invariant (b:=Tulip.forum N 1) (real_ x) i (bail N 1) Y -- tune
 rw [ht,ht, show pearls W _=pearls W x.val.G from ?_,real_move A B C x g Y,he]; -- `_ binder role find
 exact pearl_motion W x.val.G Y
lemma phase_hold (W:Pec.Pride N)(Y:Mach (More N)): stark (moveW x g Y)-Pec.pigment W (G (moveW x g Y).val)=stark x-Pec.pigment W x.val.G:=by
 let W':= tradew N Y; let V:=moveW x g Y; let L:=U.decks.keys true x; let K:=U.decks.keys false x; have F: Issued L K (U.decks.A x) (U.decks.M x) (U.decks.col x) (U.decks.col' x) U.v U.ε:= x.property.state; have he(h:Bool): twist W' (cutM (U.decks.keys h x))=cutM (U.decks.keys h x):= Hole.terra_l ..; have hp(c): stark (U:=U) c=(((real_ c).trace.re:ℝ):ℂ)+ ↑(sweepR ((Z₀).keys true c) ((Z₀).keys false c) ((Z₀).A c) ((Z₀).M c) ((Z₀).col c) ((Z₀).col' c)).im*degZ:=rfl
 rw [hp,hp, real_move A B C x g Y,trace_twist,show Pec.pigment W V.val.G = _ from Pec.pinG W x.val.G Y]; have ht:= Pf.Frame.march W' F (he true) (he false); rw [(Driver.body x g Y).a,(Driver.body x g Y).t,(voices x g Y).1,(voices x g Y).2]; rw [show U.decks.keys true V=L from rfl,show U.decks.keys false V=K from rfl,ht] -- tune
end Fare
end YM.CF.BPress.Primary
