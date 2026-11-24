import YM.SU5.Reconstruction.Anvil.Gap
import YM.SU5.Reconstruction.Anvil.Avenue
/-! # Three-axes analytic crossing for real reconstruction. Every session on
 the spacelike Umbrella, horizontal strip through it. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup MeasureTheory Price Terrain ConePrice Sail
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {a:Axis}{x:Meter}{b T d r e:ℝ}{K:Finset Axis}{P:Terrain a K}(C:Umbrella a x b T d r e P)
-- r allowance on vertical widths, d offset for testing far. Nucleus
local notation "Λ"=> LedgerRide a
variable {D:K→Hilbert}(S:∀ k,OS.Semigroup (D k) k.val)
variable (A B:∀ k:K,(D k).Op)(p q:∀ k, (D k).space)
local notation "Yp" i:max=> (P.P i).extend T
local notation "vest" i:max=> (Yp i).sale (P.first i) (S i) (A i) (B i) (p i) (q i)
local notation "chapel" i:max=> (Yp i).permeates (i:↥K).val (P.first i)
variable (h:∀ i j:K,∀ z:Wage, ((P.P i).extend T).permeates i.val (P.first i) z → ((P.P j).extend T).permeates j.val (P.first j) z →
    ((P.P i).extend T).sale (P.first i) (S i) (A i) (B i) (p i) (q i) z = ((P.P j).extend T).sale (P.first j) (S j) (A j) (B j) (p j) (q j) z)
variable {v w: ℝ}
variable {H:Hilbert} (L: OS.Semigroup H a) (R U:H.Op) (V W:H)
local notation "f"=> vertical T v w
local notation "Hq" y:max=> (vertical T v w).sale y L R U V W
variable (g:∀ i:K,∀ y:Bool,∀ z:Wage, ((P.P i).extend T).permeates i.val (P.first i) z → (vertical T v w).permeates a y z →
    ((P.P i).extend T).sale (P.first i) (S i) (A i) (B i) (p i) (q i) z = (vertical T v w).sale y L R U V W z)

namespace Umbrella
variable (k₁ k₂:K→ℝ)
def shared (Z:Wage):= if e: ∃ i:K,(chapel i) Z then (vest e.choose) Z else 0
-- include P T implicit? if only through body types need bind notation
local notation "F"=> shared (P:=P) (T:=T) S A B p q
include h
lemma shared_repr (z:Wage)(i:K)(t: ((P.P i).extend T).permeates i.val (P.first i) z) : F z= (vest i) z:= by
 have hx:∃ i:↥K,(chapel i) z:=⟨i,t⟩; unfold shared; rw [dif_pos hx, h _ _ z hx.choose_spec t]
lemma shared_cont (z:Wage)(i:K)(t: ((P.P i).extend T).permeates i.val (P.first i) z) : ContinuousAt (shared (P:=P) (T:=T) S A B p q) z:= by
 apply ((P.P i).extend T|>.saleCont (P.first i) (S i) (A i) (B i) (p i) (q i) t).congr; exact Eventually.mono ( (Yp i).permeates_open (i:Axis) (P.first i)|>.mem_nhds t) (fun y v=> Eq.symm (shared_repr S A B p q h y i v)) -- likely orientation
omit h
noncomputable def overture (s:ℂ):= averages (fun s z=> (shared (P:=P) (T:=T) S A B p q) (LedgerRide a (C.X z) s)) s
local notation "G"=> C.overture S A B p q
include C h
lemma sweep (z:ℂ)(t:z∈ Rim): DifferentiableOn ℂ (fun s=> F (Λ (C.X z) s)) (slit e):= by
  intro k e; obtain ⟨i,v⟩:= C.overlay z t k e; let W:ℂ→Wage:= LedgerRide a (C.X z); let U:= W⁻¹'{z|(chapel i) z}; let w: k∈U:=v
  have hv:IsOpen U:= ((Yp i).permeates_open ..).preimage (by unfold W; exact continuous_pi fun j=> (show Differentiable ℂ (fun x=> LedgerRide a (C.X z) x j) from by apply differentiableOn_univ.mp; exact ride_h a _ _ j).continuous)
  refine ((( (Yp i).saleHol (P.first i) (S i) (A i) (B i) (p i) (q i) U W (ride_h a (C.X z) U) hv (fun i v=>v) k w).differentiableAt).congr_of_eventuallyEq ?_).differentiableWithinAt -- .. tune
  exact Eventually.mono (hv.mem_nhds w) (fun x p=> shared_repr S A B _ _ h (W x) i p)
def limitFare : ℝ:= ∑ i:K, |‖p i‖*k₁ i*k₂ i*‖q i‖|
local notation "𝓒"=> limitFare (D:=D) p q k₁ k₂
variable (h1:∀ k,‖A k‖ ≤ k₁ k) (h2:∀ k,‖B k‖ ≤ k₂ k)
include h1 h2
lemma paid (s:ℂ)(w:s∈ Sail.slit e)(z:ℂ)(v:z∈Rim): ‖shared (P:=P) (T:=T) S A B p q (Λ (C.X z) s)‖ ≤ limitFare (D:=D) p q k₁ k₂:= by
 obtain ⟨i,u⟩:= C.overlay z v s w; rw [shared_repr S A B p q h _ i u]; exact ((Yp i).tariff (P.first i) (S i) _ _ (L:=p i) (R:=q i) u (h1 i) (h2 i)).trans ((le_abs_self ..).trans (Finset.single_le_sum («f»:= fun i=> |‖p i‖*k₁ i*k₂ i*‖q i‖|) (fun t _=>abs_nonneg _) (Finset.mem_univ i))) -- tune ..
lemma costs(s:ℂ)(w:s∈ Sail.slit e): ‖G s‖ ≤ limitFare (D:=D) p q k₁ k₂:= average_cost (fun z=>F (Λ (C.X z) s)) (C.paid S A B p q h k₁ k₂ h1 h2 s w)
lemma overture_hol : AnalyticOnNhd ℂ (C.overture S A B p q) (Sail.slit e):= by
 apply averages_rented (Q:=𝓒) (fun s z=> F (Λ (C.X z) s)) (slit_open e) (fun z hz=> C.sweep S A B p q h z hz) _ (C.paid S A B p q h k₁ k₂ h1 h2)
 intro x t y p'; obtain ⟨z,p₀⟩:= C.overlay y p' x t; exact ((shared_cont S A B p q h _ z p₀).comp («f»:=fun y=> Λ (C.X y) x) ((C.life y (sphere_subset_closedBall p')).add (continuousAt_const (y:= onlyTime a x)))).continuousWithinAt -- k₁ explicit
omit h1 h2
-- compares against a single F-vertical actor, not assuming sequences yet
include g
private lemma relative (y:Bool)(s:ℂ)(t:s∈ Sail.slit e) (T':∀ z∈Pane,(vertical T v w).permeates a y (Λ (C.X z) s)) : G s= (Hq y) (Λ (aim a x b) s):=by
 let z(ζ:ℂ):=Λ (C.X ζ) s; unfold overture averages; trans Real.circleAverage (fun ζ=> (f).sale y L R U V W (z ζ)) 0 1;
 · apply Real.circleAverage_congr_sphere; simp only [abs_one]; intro x t'; obtain ⟨k,H⟩:= C.overlay x t' s t; dsimp only; rw [shared_repr S A B p q h _ k H]; exact g k y _ H (T' x (sphere_subset_closedBall t'))
 have hx(i):DifferentiableOn ℂ (fun x=>z x i) Well:=fun x t=> ((C.pulse i x t).add (differentiableAt_const _)).differentiableWithinAt
 rw [average_of]; exact congrArg ((f).sale y L R U V W ∘ fun x=>Λ x s) C.atSpot
 · exact (saleHol (vertical T v w) y L R U V W Well z hx isOpen_ball (fun x y'=> T' x (ball_subset_closedBall y'))).differentiableOn
 exact fun x t=> ((saleCont (vertical T v w) y L R U V W (T' x t)).comp («f»:=fun x=> Λ (C.X x) s) ((C.life x t).add (continuousAt_const (y:=onlyTime a s)))).continuousWithinAt
-- analytic continuation of EACH directions to full horizontal strip through center
lemma verdict (s:ℂ)(p':s∈ Sail.slit e)(u':v≤r)(v':w≤r) :
    (s.re∈ Set.Icc d (d+1) → G s= (Hq true) (Λ (aim a x b) s)) ∧
    (-s.re∈ Set.Icc d (d+1) → G s= (Hq false) (Λ (aim a x b) s)) := by
   exact ⟨fun u=> C.relative S A B p q h L R U V W g true s p' (fun z t=>(C.horizon z t s v w u' v').1 u),
     fun u=> C.relative S A B p q h L R U V W g false s p' (fun z t=>(C.horizon z t s v w u' v').2 u)⟩
end Umbrella
end YM.Anvil
