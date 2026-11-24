import YM.CF.BPress.Primary.Mass
/-! ℓ-Pig Matrix terms into averaged Ballad. price_point witness. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine
variable {s N:Side}{U:Driver N}{A B C X Q K:Pledge}
abbrev Tenor(s:Side):= Site s×Support s
abbrev scaffold {s:Side} : Tenor s→ Support s:= Prod.snd
variable {I:Pec.Pride N}
structure Book (U:Driver N)(Q:Pledge)(I:Pec.Pride N) where
 F : Site (More N)→Support (More N)→ U.Pose→ℂ
 W : Site (More N)→Support (More N)→ℝ
 h : CostSpec (V:=Q) I U F W
namespace Book
variable (V: Wish U A B C)
include V
theorem books(g:Grant X A (payA A B C) (stream 1) (Sight.price U.h) U.v U.ε quota)(c:Pec.Lac I K.rate K.price)(p : Fare.bought (X.plus (ζPearl K)) Q): Nonempty (Book U Q I) :=by
 obtain ⟨F,K,f⟩:= p.h (Beta U).full (Fare.mint A B C K X V g I c); exact ⟨⟨F,K,f⟩⟩ -- tune binder
omit V
variable (W: Book U Q I)(p:Tenor (More N))(x y:U.Pose)
abbrev bud := W.W p.1 p.2
abbrev toll := W.F p.1 p.2
-- parameter periodic.
abbrev ballad := average (Machine.spinM V) (W.toll p)
include W
lemma stock_x : Measurable (toll W p):= (W.h.handles ..).continuousE.measurable -- may timeout Borel implicit
lemma stock_t : ‖toll W p x‖≤ W.bud p:= (W.h.handles ..).norms _
include V
lemma stock_ballad : ‖ballad V W p x‖ ≤ W.bud p:= (μ_worker V).price_A _ (W.stock_x p) (W.stock_t p) _
lemma stock_m : Measurable (ballad V W p):=(μ_worker V).meas_A _ (W.stock_x p) (W.stock_t p)
lemma stock_g (g:Mach (More N)): ballad V W p (moveW x V g)=ballad V W p x:= (μ_worker V).move_avg _ (W.stock_x p) (W.stock_t p) _ _
lemma stock_k : ‖ballad V W p x-ballad V W p y‖ ≤W.bud p* U.Beta.eval (scaffold p) x y:= by
 refine (μ_worker V).priceΔ _ (W.stock_x p) (W.stock_t p) _ _ _ ?_; intro g; rw [← posesτ x y V g (scaffold p)]; exact (W.h.handles ..).varies _ _
lemma story_sum(g:Grant X A (payA A B C) (stream 1) (Sight.price U.h) U.v U.ε quota): ∑ p:Tenor (More N),ballad V W p x= stark x- Pec.pigment I x.val.G:=by
 rw [(μ_worker V).total_avg W.toll W.stock_x W.stock_t]; have hh(g:Mach (More N)): Machine.spinM V g x=moveW x V g:=rfl; simp_rw [hh]; have he(x) : ∑ p:Tenor (More N), W.toll p x= stark x-Pec.pigment I (x.val.G):=by rw [←Fare.bill A B C I X V g x,Anchor.truth (U.Beta.stage)]; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; exact (W.h.bill i x).symm -- tune order args
 simp_rw [he,phase_hold A B C x V I]; simp -- tune
lemma story_real(i:Site (More N)): ∑ p:Support (More N),(ballad V W (i,p) x).re=(Fare.town I x i).re:=by
 rw [(μ_worker V).subtotal_r (fun p:Support (More N)=> W.toll (i,p)) (fun _=>W.stock_x _) (fun i=>W.stock_t _)]; simp_rw [←Complex.re_sum, show ∀ x, (∑ p:Support (More N), W.toll (i,p) x)=Fare.town I x i from (fun x=>(W.h.bill i x).symm)]; simp_rw [spinM,home_hold _ _ _ x I V]; simp -- tune
end Book
end YM.CF.BPress.Primary
