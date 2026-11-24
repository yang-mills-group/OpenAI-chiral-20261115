import YM.CF.BPress.Habitat.Mascot
/-! PCC. chart meas & near costs. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Upled Plain Engine
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N s:Side}{D:Type}{j:ℕ}{r q p σ δ:ℝ}
def Plot (C:ℝ→ Paint s):Prop:= ∀ x:Site s,Continuous fun i=> C i x
variable (C C':ℝ → Paint (More N))(u:Plot C)(v:Plot C') (Y:Stun N)(U:Bkg (More N))(X:Support N)
def crevice(C:ℝ→Paint s)(u: Plot C): Lamp s:=fun i=>⟨fun t=> C t.val i, (u i).comp continuous_subtype_val⟩
def portrait : Plain N:= (U, Y,fun i=>decide (i∈X),crevice C u,crevice C' v)
local notation "Ψ"=> portrait C C' u v Y U X
lemma portrait_key : key Ψ=X:=by ext i; simp [key,portrait,stars]
lemma crease (C:ℝ → Paint s)(u: Plot C)(t:ℝ)(h:t∈Set.Icc (-1:ℝ) 3): (fun i=> Upled.decode (crevice C u i) t)= C t:=by funext i; change C (tap t).val i= _; rw [tap_v h]
private lemma subsetP: Set.Icc (0:ℝ) 2⊆ Set.Ioo (-1:ℝ) 3 := Set.Icc_subset_Ioo (by norm_num) (by norm_num) -- tune
lemma early_bill (t:ℝ)(g:t∈Set.Icc (0:ℝ) 2):Plain.spin Ψ false t=C t∧ Plain.spin Ψ true t=C' t:=⟨crease C u _ (Set.Ioo_subset_Icc_self (subsetP g)),crease C' v _ (Set.Ioo_subset_Icc_self (subsetP g))⟩
lemma passport (p0:Looks U X C C' j r σ q δ) : Looks (Plain.G Ψ) (key Ψ) (Plain.spin Ψ false) (Plain.spin Ψ true) j r σ q δ:=by
 let T:=Plain.spin Ψ; have hh(i:Bool): Continuous (T i):= (cont_spin i).comp (f:=fun x=>(Ψ, x)) (continuous_const.prodMk continuous_id); have ht:= early_bill C C' u v Y U X; rw [portrait_key]; refine ⟨p0.support, fun i h=> by rw [(ht i h).1]; exact p0.guards i h, fun i h=>by rw [(ht i h).1]; exact p0.frisky i h,?_,?_ ,?_, (hh true).continuousOn ⟩
 · rw [(ht 1 (by norm_num)).1]; exact p0.stop
 · intro x v'; rw [(ht x (Set.Icc_subset_Icc_left (by norm_num : (0:ℝ)≤1) v')).1]; exact p0.end_me x v'
 intro x y; rw [(ht x y).2]; refine (p0.dP x y).congr_of_eventuallyEq ?_; filter_upwards [Ioo_mem_nhds (subsetP y).1 (subsetP y).2] with x u'; exact crease C u x (Set.Ioo_subset_Icc_self u') -- tune namespace order
variable {Y U X}
private lemma keyk {α:Type*}[MeasurableSpace α]{v:α→ Lamp s}(u:∀ i:Site s,Measurable (fun x=>v x i)):Measurable v:= measurable_pi_lambda v u
lemma portrait_meas [MeasurableSpace D]{u:D→ ℝ→Paint (More N)}{w:D→ℝ→ Paint (More N)}(p:∀ i,Plot (u i))(q:∀ i,Plot (w i)){F:D→ Bkg (More N)}{V:D→ Stun N}{S:D→ Support N}(x:Measurable F)(t:Measurable V)(a: ∀ i:Site N,MeasurableSet {l|i∈S l}) (k:∀ i v,Measurable fun x=>u x v i)(h:∀ i v,Measurable fun x=>w x v i): Measurable fun i:D=> portrait (u i) (w i) (p i) (q i) (V i) (F i) (S i):=by
 refine tagStar (N:=N) _ x t ?_ ?_; · refine measurable_pi_lambda _ (?_ ); intro i; change Measurable fun l=> decide (i∈ S l); convert! Measurable.ite (a i) (measurable_const (a:=true)) (measurable_const (a:=false)) using 1
 intro i; cases i; exact keyk (v:= fun i=> crevice (u i) (p i)) (fun i=> salute _ (fun t=> k i t.val)); exact keyk (v:= fun i=> crevice (w i) (q i)) (fun i=> salute _ (fun t=> h i t.val))
end YM.CF.BPress.Habitat
