import YM.CF.BPress.Primary.Mass
/-! Exact pure Regular part via averaging. second Weak includes Force diff not averaged per prohibition. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree
variable {N:Side}{U:Driver N}{A B C K:Pledge}{F:Scree.GramM N}
namespace Dust
variable (V:Wish U A B C)(T: Till (Beta U) F)(s:Support (More N))(p:U.Pose)(h:Pec.Post N)(W:Shot N)
local notation "Ω"=> (U.Pose × Pec.Post N)
def ΩMove (x: Mach (More N))(u:Ω): Ω:= (moveW u.1 V x,gauge x u.2)
lemma Ω_worker: Worker (ΩMove V):=by
 refine ⟨fun p g ⟨x,y⟩=>?_,?_ ⟩; · unfold ΩMove; dsimp only; apply Prod.ext (pose_seq x V g p); ext1 i; simp [Lattice.gauge,mul_assoc]
 let G:= Mach (More N); refine (((μ_worker V).meas).comp (f:=fun t:Ω× G=> (t.1.1,t.2)) ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk ?_; apply measurable_pi_lambda; intro j; unfold Lattice.gauge; fun_prop -- tune
abbrev pure_ (T: Till (Beta U) F)(s:Support (More N))(p:Ω):= RegGas T (decks U) 1 p.1 p.2 s
def pureG : ℂ:= average (ΩMove V) (pure_ T s) (p,h)
def wholeG : ℂ:= logGas (decks U) p W T 1 s-pure_ T s (p,W.field.1)+ pureG V T s p W.field.1 -- tune order
variable {c r ε g μ:ℝ} {V T p h s} (S: Store (Beta U) U.decks K F c U.ε U.v g r μ T)
set_option synthInstance.maxSize 20000
local instance ptBore : BorelSpace (Paint (More N)):= by letI: SecondCountableTopology (Op SU.Slot):=inferInstance; letI: BorelSpace (Op SU.Slot):=inferInstance; exact Pi.borelSpace
include S
lemma pure_meas (s:Support (More N)): Measurable (pure_ T s):=by
 -- $
 have hp: Continuous U.decks.KG := (Plain.cont_spin false).comp ((continuous_subtype_val (p:=Driver.Hallowed U)).prodMk (g:=fun _=> (2:ℝ)) continuous_const); exact S.pure_f measurable_const measurable_fst hp.measurable measurable_snd s -- tune field path cont
lemma pure_p (x:Ω) : ‖pure_ T s x‖≤T.currencyGas g s:= Gas_bill S _ 1 (by simp) _ (readyF _ _ S.Tclock.he) -- tune
variable (V) (s p h) -- annotation p/h? same explicit once omit
include V
lemma pure_on : ‖pureG V T s p h‖ ≤ T.currencyGas g s:= (Ω_worker V).price_A (pure_ T s) (pure_meas S s) (pure_p S) _
lemma pure_m : Measurable (fun x:Ω=>pureG V T s x.1 x.2) := (Ω_worker V).meas_A _ (pure_meas S s) (pure_p S)
lemma pure_g(u: Mach (More N)) : pureG V T s (moveW p V u) (gauge u h)=pureG V T s p h :=by change average (ΩMove V) (pure_ T s) (ΩMove V u (p,h))=_; exact (Ω_worker V).move_avg (pure_ T s) (pure_meas S s) (pure_p S) u (p,h)
lemma pure_read {x:U.Pose}{u:Pec.Post N}(t:Along s p.val x.val)(v:Agrees s h u): pureG V T s p h=pureG V T s x u:=by
 refine Worker.align (Ω_worker V) _ _ _ ?_; intro g; exact reg_read S _ _ _ s (gauge g h) (gauge g u) (t.move g|>.price0) (fun i p q=> by unfold Lattice.gauge; rw [v i p q]) -- tune include args S for label
abbrev dustC (W:Pledge)(g q:ℝ)(B:ℕ):=3* Perk.price W g q B
abbrev feeG (T:Till (Beta U) F) (g:ℝ)(s:Support (More N)):=3*T.currencyGas g s
omit V
lemma earnedG : Cash id (feeG T g) μ (dustC K g r F.p.B):= Cash.scale 3 (currencyPays S) (by norm_num)
include V
lemma whole_p (u:W.inBudget g): ‖wholeG V T s p W‖≤ feeG T g s:=by
 unfold wholeG; have hp:= T.currencyGas g s; exact (norm_add_le ..).trans (((add_le_add ((norm_sub_le ..).trans (add_le_add (S.Gas_bill _ 1 (by simp) p u) (pure_p S _))) (pure_on _ _ _ _ S))).trans_eq (by ring)) -- tune syntax have var
lemma whole_k (z:barren F W s): wholeG V T s p W=pureG V T s p W.field.1:=by unfold wholeG; rw [S.still_gas p 1 _ z]; unfold pure_; dsimp only; rw [sub_self,zero_add] -- tune
lemma whole_m {D:Type}[MeasurableSpace D](F:D→ Shot N)(H:Shot.Given F)(X:D→U.Pose)(v:Measurable X) : Measurable fun x=> wholeG V T s (X x) (F x) := by
 have hp: Continuous U.decks.KG := (Plain.cont_spin false).comp ((continuous_subtype_val (p:=Driver.Hallowed U)).prodMk (g:=fun _=> (2:ℝ)) continuous_const); let g(x) := (X x,(F x).field.1); have hu: Measurable g:= v.prodMk H.field.fst
 have hv: Measurable (pure_ T s ∘ g):= (pure_meas S s).comp hu; have ht: Measurable ((fun x:Ω=>pureG V T s x.1 x.2) ∘ g) := (pure_m V s S).comp hu
 exact Measurable.add (Measurable.sub (S.gas_f (α:=fun _:D=>1) measurable_const v H hp.measurable s) hv) ht
lemma whole_read {x:U.Pose} (u: Along s p.val x.val)(W':Shot N)(ζ:Camera W U.decks p x s W' F.p.B (P:=Beta U)): wholeG V T s p W=wholeG V T s x W':=by unfold wholeG; rw [S.gas_read p x _ s ζ]; exact congrArg₂ (·+·) (congrArg (_-·) (S.reg_read p x 1 s _ _ u.price0 ζ.view)) (pure_read V s p _ S u ζ.view) -- tune infer
lemma total_c : ∑ s:Support (More N), pureG V T s p h=∑ s:Support (More N), RegGas T U.decks 1 p h s:=by
 unfold pureG; rw [(Ω_worker V).total_avg (pure_ T) (pure_meas S) (fun i x=>pure_p S (s:=i) x)]; simp_rw [ΩMove,pure_] ; simp_rw [S.gaugeG p _ h _ (Driver.body p V _)]; simp
lemma full_cost : ∑ s:Support (More N),wholeG V T s p W=∑ s:Support (More N), T.logGas (decks U) p W 1 s:= by unfold wholeG; rw [sum_add_distrib,sum_sub_distrib, total_c V p _ S]; exact sub_add_cancel ..
end Dust
end YM.CF.BPress.Primary
