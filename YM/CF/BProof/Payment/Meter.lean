import YM.CF.BProof.Anthem.Waltz
/- Envelope receipts (prior to gauge action reissue) -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Payment
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular Anthem Girt
open Vault Paige Drapes Moment RG Wilson Charge
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I]{Y:Yard (More N)}(Q:Score Y I)
local instance (I : Type)[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _
local instance (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
variable (b:Y.FaceS)(Z:Pane N)
section e
variable {V X D:Type}[MeasurableSpace D][NormedAddCommGroup V][MeasurableSpace V][MeasurableAdd₂ V]
theorem totalEnv (F:I→D→V) (h:∀ i,Envelope (F i))(S:Finset I): Envelope (fun x=>∑ i∈S, F i x):=by
 obtain ⟨C,p⟩:= Classical.axiomOfChoice (fun i=> (h i).cost); refine ⟨Finset.measurable_sum _ (fun i _=>(h i).meas),∑ i∈S,C i,fun i=> (norm_sum_le ..).trans (sum_le_sum (fun j _=>p j i))⟩ -- tune choose!
variable {c:Clip}{W R U:ℝ}{G:Gauge}(T:PathData G)(β:ℝ)
lemma bigEnv {s:Side}(Y:Yard s)(q:BudgetPoint)(M:ℕ)(p:T.Bounds c W R U)(v:0≤β): Envelope (big Y c q T M β):=by
 let l (i:Tile s)(x: Config G s):= heavy c q T M β x i; refine Envelope.sum _ l (fun i=>⟨heavy_c _ _ _ _ _ i p,?_⟩) -- tune syntax
 rcases i with i|i; exact ⟨_,fun x=>by change ‖directQ c q β x i‖ ≤_; rw [Real.norm_of_nonneg (direct_pos ..)]; exact direct_cost c q β x _ v q.threshold_le; exact v⟩; exact ⟨_,fun x=> by change ‖higher c q T M β x i‖≤_; rw [Real.norm_of_nonneg (higher_pos ..)]; exact higher_cost c q T M β x p i v; exact v⟩ -- tune
end e
variable {A B C:ℝ}(h:Q.Budget A B C)
@[fun_prop] lemma SBook_m : Measurable (uncurry Q.SBook):= by
 apply measurable_pi_lambda; intro i; let j:= Trek.hr Y i; let t (p:Pane N × Y.FaceS):=(p.1,p.2 j); have ht:Measurable t:=by unfold t; fun_prop
 unfold uncurry Score.SBook; split
 · change Measurable ((fun x:Quilt N=>x i) ∘ ((uncurry (Q.H j)) ∘ t)); exact (measurable_pi_apply (X:=fun _: Site (More N)=>Stamp) i).comp ((Q.seat_m j).comp ht)
 exact measurable_const
lemma crop_m : Envelope (fun p:Pane N × Y.FaceS=> (Madd (Q.SBook p.1 p.2)).prod (Score.chamber Y univ)) :=
 ⟨(Madd_cont (Score.chamber Y univ)).measurable.comp (SBook_m Q), _,fun p=> Madd_money (Q.healthy p.1 p.2) (Score.chamber Y univ)⟩
include h
lemma shade_m(i:Y.Index): Envelope (uncurry (Q.mask i)):= ⟨(Q.M.feeMeas Y i Q.r).comp (fiddle_m Y i Q.S Q.f), _,fun p=> Q.maks i p.1 p.2 h⟩
lemma holePay (S:Finset Y.Index): Envelope (uncurry (Q.exponent S)):=by
 let f(i:Y.Index)(p:Pane N × Y.FaceS):= (Q.gaugeCharge i p.1:ℂ)- Q.mask i p.1 (p.2 i); refine totalEnv f (fun i=>?_ ) S; let e: Envelope (Q.gaugeCharge i):= ⟨h.meas i,_,fun x=> h.costG i x⟩
 let g(p:Pane N × Y.FaceS):=(p.1,p.2 i); have hg:Measurable g:= by unfold g; fun_prop
 exact kitE (fun p:Pane N × Y.FaceS=> Q.gaugeCharge i p.1) (fun p=>uncurry (Q.mask i) (g p)) (fun (a:ℝ)(b:ℂ)=> (a:ℂ)-b) (by unfold uncurry; fun_prop) (snap (X:= (Prod.fst : Pane N × Y.FaceS → Pane N)) e measurable_fst) (show Envelope (fun p=> Q.mask i (g p).1 (g p).2) from snap (X:=g) (shade_m Q h i) hg)
end YM.CF.BProof.Payment
