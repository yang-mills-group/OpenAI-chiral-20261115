import YM.CF.BPress.Habitat.Porter
/- includes gauge moves of comparison coordinates. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Upled Plain Engine
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N:Side}{U:Driver N}{A B C:Pledge}
open Pf Actor
namespace Driver
variable (x y: U.Pose)(V: Wish U A B C)(g:Mach (More N))
local notation "𝕏"=> U.model
include V
lemma twist_a : Actor.bodyG g U.model x.val (τ x.val g):=by
 let R:= U.packsA x.val.G; have he: U.packsA (gauge g x.val.G)=twist (tradew N g) R := V.pen.tag U.M (x:=fundsX U x) g; refine ⟨rfl,he,Plain.spin_move ..,?_⟩; change Ts _ (U.packsA (Lattice.gauge g x.val.G)) (Lattice.gauge g x.val.G)=_; rw [he,Ts, aim_tag U.F V.pay]; change Kennel.capT _ _= twist _ (Kennel.capT _ _); simp [Kennel.capT,R]
lemma permit_move : U.Hallowed (τ x.val g):=by
 let p:=tradew N g; have he:= twist_a x V g; have hv(Ω: Bool): coupling ∘ Plain.spin (τ x.val g) Ω=Pf.Frame.atC p (coupling ∘ Plain.spin x.val Ω):=by funext i; simp only [Function.comp_apply,Plain.spin_move,Paint.coupe_gauge]; rfl
 refine ⟨x.property.glow.cov _, ?_, ?_ ,?_, ?_⟩; swap; pick_goal 1; · intro i a z u; rw [Plain.spin_move]; change ‖congrC _ _‖≤ _; rw [congr_norm]; exact x.property.toll i a z u
 pick_goal 1; · exact slow_g _ _ _ x.property.tuneK -- tune arguments
 · unfold Actor.col Actor.col' Actor.keys; change Pf.Issued (Stride.Locks _ true) (Stride.Locks _ false) _ _ (coupling ∘ Plain.spin _ _) (coupling ∘ Plain.spin _ _) _ _; rw [hv,hv, he.a, he.t,← he.s]; exact Pf.Frame.transport _ x.property.state (Hole.terra_l (S:=x.val.key) true g) (Hole.terra_l (S:=x.val.key) false g) -- maybe typecheck heavy.
 rw [he.k]; exact fun x'=> Spin.Paint.turn_plan (x.property.day _) (g x') -- tune
abbrev moveW : U.Pose:= ⟨τ x.val g, permit_move x V g⟩
lemma pose_one : moveW x V 1=x:=Subtype.ext (Plain.τ_one x.val)
lemma pose_seq (h:Mach (More N)): moveW (moveW x V g) V h=moveW x V (h*g):=Subtype.ext (Plain.τ_ρ _ _ _)
lemma feeling : Continuous (fun x:Mach (More N)× U.Pose=>moveW x.2 V x.1):=by
 let f(x:Mach (More N)× U.Pose):= moveW x.2 V x.1; change Continuous f; apply Continuous.subtype_mk; exact Plain.ambiance.comp (f:=fun x : Mach (More N)× U.Pose=> (x.1,x.2.val)) (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
lemma posesτ(t:Support (More N)): U.Beta.eval t (moveW x V g) (moveW y V g)= U.Beta.eval t x y:=τ_canon ..
lemma body : Actor.bodyG g U.decks x (moveW x V g):= ⟨rfl,(twist_a x V g).a, (twist_a x V g).k,(twist_a x V g).t⟩
lemma voices: (U.decks.col (moveW x V g)= Pf.Frame.atC (tradew N g) (U.decks.col x)) ∧ (U.decks.col' (moveW x V g)=Pf.Frame.atC (tradew N g) (U.decks.col' x)):= by
 have hp(i:Bool)(t:ℝ): coupling (Plain.spin (τ x.val g) i t)= congrC (tradew N g) (coupling (Plain.spin x.val i t)):= by rw [Plain.spin_move,coupe_gauge]
 exact ⟨funext (hp false),funext (hp true)⟩
end Driver
end YM.CF.BPress.Habitat
