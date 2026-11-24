import YM.SU5.FiniteGaugeData.Signal.Campfire
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic
namespace Play
variable {m n:Side}{x' a b u v e t w x z γ Ω H:ℝ}{i j k d d0 q r:ℕ}
variable (o:Seat n)(f: SU.Slot)(l:List (Site n))
variable {N:Loom n}{F:GramM n}{X Y : Support (More n)}{S:Finset (Site n)} (g:Pane n→ Plum.Troupe n)
local notation "t·" i=> bay (terr (More n)) o i
local notation "P"=> F.J.P
local notation "K"=> F.J.M
local notation "B"=>Booted j F N z H X
variable {b':Side}{L:Side}{h': Odd L.val}{Y0:Pricing j L h' (Thread j)}{P0:Grasp Y0 b' v}
variable (W: P0.roundZ ≤ n.val)(hp:1 ≤ H)(wg:Roof n u v i N)(hK:∀ x∈l,x∈S) (hs:∀ x∈S,node x∈(bay (terr (More n)) o k))
variable (K0:Site n→ Ket (Single n))(hv:∀ v∈S,Column (bay (terr (More n)) o k) j F.J.M f S H a b (Baby f v) (K0 v))
variable (ha:F.J.P.toll e t x γ)(π:∀ (T:Pane n),Guard T v→Tulip.fare (bay (terr (More n)) o (k+q)) (profile T) 1≤ Ω→ ∀ y:Ket (Single n),‖y‖≤ a→acts (cutM (colorWall (bay (terr (More n)) o k))) y=y→ ‖acts (priceOp j F.J.P F.J.M H (profile T)) y-acts (priceOp j F.J.P F.J.M H 1) y‖ ≤ z-b)
include W hp wg hv ha π
lemma igniting (f':Invest.Look o N x' (k+q) d Ω g)(v':Orbit n)(r:Healthy x' (bay (terr (More n)) o (k+q+d+1)) v'.1){x:Site n}(hx:x∈S): Spike.lit (spar j K (N v')) (pullP j P K (N v')) H z (create (rise g v'.1 (K0 x))):=by
 let V:= N v'; let s:=g v'.1; let V':=gauge s V; let U:=tradew n s; let f:= rise g v'.1 (K0 x); let c:=Furnace.upstairs (spar j K V) H*(1-pullP j P K V); let y:=acts (priceOp j P K H (profile V')); have ht: Guard V v:=wg.paid v'; let ct:=hv x hx
 have he: acts U.val f=K0 x:= act_starUnit U _
 have H₁: ‖acts c f‖=‖y (K0 x)‖:=by
    nth_rw 1 [←act_unit_norm U (acts c f)]; rw [Fock.swivel,he]; unfold y; rw [Supplies.atPose]; rw [Momentum.price_gauge W P K V s ht ha]; rfl -- tune
 have hl:= π V' (ht.cov s) (f'.price v' r) _ ct.cost ct.supported; rw [Supplies.atOne] at hl -- danger
 apply Spike.inferior (pillar W K _ ht) (refuge W P K _ ht) (zero_lt_one.trans_le hp); change ‖acts c f‖≤ _; rw [H₁]; -- simplify
 have hl': ‖y (K0 x)-acts (upstairs (funde j K n 1) H) (K0 x)‖ ≤ z-b:=hl; have hp := ct.pay ; linarith [norm_sub_norm_le (y (K0 x)) (acts (upstairs (funde j K n 1) H) (K0 x))]
-- cuts and legs. projector free Kea Pad known externally.
include hK hs
lemma branded (X0:Invest.Look o N x' (k+q) d Ω g)(hm:l.Nodup) : let X:= bay (terr (More n)) o (k+q+d+1); let μ:= inspected X; Booted j F N z H μ l.length (radiant f l K0 g X x') := by
 intro T μ; apply Eventually.of_forall; intro v; let x:=v.1; by_cases h:Healthy x' T v.1; swap; · left; unfold radiant maskT toMark drawn; simp [Set.indicator,h]
 right
 let L:=fun i:Site n=> rise g v.1 (Baby f i); let M:=fun i=> rise g v.1 (K0 i); let F':= Vine.radiate (T:=Tset n) l L M
 let U:=tradew n (g v.1)
 rw [show radiant f l K0 g T x' (drawn N v) = F' from (by unfold radiant maskT toMark drawn; simp only [Set.indicator, Set.mem_setOf_eq,h,if_true]; rfl)]; let W':=colorWall (bay (terr (More n)) o k)
 refine Vine.crucible (S:=modesIn n μ) («P»:=spar j K (N v)) l L M (fun i u=>?_) (fun i u j w'=> ?_) hm (fun i p=>?_) (fun i p=>?_) (fun i p=> igniting o f g W hp wg K0 hv ha π X0 v h (hK i p)) (fun i p=>?_)
 · rw [show acts (cutM (Tset n)) (L i)=acts (star U.val) (acts (cutM (Tset n)) (Baby f i)) from below_blend .., baby_upper,map_zero]
 · rw [show inner ℂ (L i) (M j)=_ from act_unit_inner (star U) (Baby f i) (K0 j)]; nth_rw 1 [←baby_to f S (hK i u)]; rw [←show star (cutM (colorsOne S f))=_ from (cutM_idp _).isSelfAdjoint,act_inner,(hv j (hK j w')).anchor]; by_cases h:i=j<;> simp [Baby,h]
 · have he: W' ⊆ modesIn n μ :=by rw [←port_size]; exact wallUp (Subset.trans (Invest.rail (by omega:k≤ k+q+d+1) o) subset_union_left)
   exact closedCut he (patch_size _ ((hv i (hK i p)).supported))
 · have he: W' ⊆ modesIn n μ :=by rw [←port_size]; exact wallUp (Subset.trans (Invest.rail (by omega:k≤ k+q+d+1) o) subset_union_left)
   exact closedCut he (patch_size _ (closedCut (rack o f (fun i h=> (bay_mem _).1 (hs i h))) (baby_to f S (hK i p))))
 · exact (act_unit_norm (star U) _).le.trans (baby_fee f _).le
end Play
end YM.CF.Signal
