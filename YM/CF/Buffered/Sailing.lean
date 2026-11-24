import YM.CF.Buffered.Hothouse
/-!
# Cross-volume launches. Move the bounds on the unnormalized integrals
actual, with shared parameters & coherence on exact curl/Bᵢ & seed. Formalizes
from the coherent W/B/Y of the prescription. Not claiming independent Scroll/pin choices
satisfy these! Only need at repeated inputs; can use reflection extension already built.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B l n k:Side}
variable {e x:ℝ} (K: Ticket m v B p e x)(K': Ticket n v B l e x) (q:Clip)(β u:ℝ)
namespace Ticket
-- input coherence across joint cubes on lifts as in VolumeBurn. State for the
-- actual reflections of one tile (`whole K` reifies into uniform cube) so applies on a single
-- Ticket (refl) or two generated coherently across the list. If using lemma Ember as input,
-- include its proof's additional statements (equality of water,Y not just tab).
-- See Mail.sizes (Reruns.lean) to reduce paint/water.
structure Coherent (K:Ticket m v B p e x)(L:Ticket n v B l e x):Prop where
 water (i)(u:Locale v B): small K.K i u=small L.K i u
 bill (i)(u:Locale v B)(p:u∈permitted K.K e x): K.tabV i u=L.tabV i u
 -- equal Paint slots as in its construction
 paint (i)(u:Locale v B)(p:u∈permitted K.K e x): K.paintI i u=L.paintI i u

local notation "G" => GridM v B
local notation "S" => Locale v B
variable {δ:Axis→Side}
lemma Coherent.test (h:Coherent K K') : permitted (B:=B) K.K e x=permitted K'.K e x := by unfold permitted; simp_rw [h.water]
lemma Coherent.rect (h:Coherent K K')(Z: Rail δ→Badge v B) : prism δ K Z q β u=prism δ K' Z q β u:=by
 have ht:= Coherent.test K K' h
 have he (z:S): deck K q β z=deck K' q β z:=by
    unfold deck; by_cases p:z∈permitted K.K e x; · rw [Set.indicator_of_mem p, Set.indicator_of_mem (ht ▸ p)]; unfold portion drizzle sumBill; simp_rw [h.water,h.bill _ z p]
    rw [Set.indicator_of_notMem p, Set.indicator_of_notMem (ht ▸ p)]
 have hx (z:S) : Tile.seed K z=Tile.seed K' z:=by
    unfold Tile.seed; apply sum_congr rfl; intro i _; apply congrArg; unfold seedM; by_cases p:z∈permitted K.K e x; · rw [Set.indicator_of_mem p, Set.indicator_of_mem (ht ▸ p), h.paint i z p]
    rw [Set.indicator_of_notMem p, Set.indicator_of_notMem (ht ▸ p)]
 unfold prism Rect.vista; apply integral_congr_ae; refine Eventually.of_forall fun v=>?_ ; unfold Rect.emit Rect.gold Rect.player Rect.quiet; simp_rw [he,hx]

open Growth
local notation "s" => Brace.northZ m B
-- same formulas use moments (not ratios)
def moment (K:Ticket m v B p e x)(Z:Badge v B)(q:Clip)(β u:ℝ) := heatNum K.pin K.W q β x e u (Brace.northZ m B) (K.estate Z.reflected)
lemma moment_s (Z:Badge v B) : moment K Z q β u= prism (Uniform p) K Z.reflected q β u:= pressure ..
lemma trivial : K.estate (1 : Rail (Uniform p)→Badge v B)=1:=by
 funext v'; let f:= Rect.Badge.one (K.K.erect B) (1: Rail (Uniform p)→_) (fun i=> reel i (K.K.fromCube v')); change pal f (show Pairwise _ from Rect.Badge.paired (K.K.erect B) 1 (fun i=>reel i (K.K.fromCube v'))) univ=(1:FC (Xmind m B)); unfold pal; rw [noncommProd_eq_pow_card _ f _ 1,one_pow]; exact fun _ _=>map_one _
lemma moment_zero : K.moment 1 q β u=heatNum K.pin K.W q β x e u s 1 :=by rw [moment, Badge.reflected_one]; congr 2; exact K.trivial -- tune
variable (Z:Badge v B)
lemma cluster_iff : layout p (Uniform 1)=Uniform p:=funext fun _=> one_mul _
lemma forward (h: K.Coherent K')(b: l=k*p) : ‖K'.moment Z q β u‖=Growth.heightK K q β u Z p (Uniform k) :=by -- tune
 rw [moment_s, ←Coherent.rect K K' q β u h]; unfold heightK; apply congrArg; rw [b]; rfl -- tune dep rewrite
lemma starter : ‖K.moment Z q β u‖= heightK K q β u Z p (Uniform 1) :=by unfold heightK; rw [cluster_iff,moment_s]

variable (h: K.Coherent K') (hk:l=k*p)(hu:0 ≤ u)
include h hk hu
lemma at_most : ‖K'.moment Z q β u‖ ≤ ‖K.moment Z q β u‖^(k.val^4):=by
 rw [forward K K' _ _ _ Z h hk, starter, ←uni_v]; exact height_min K q β u Z p (K.K.onGrid 0) hu _

-- translate ∆ exactly, don't use separate unknown bounds at two anchors in escort.
def lux (k:Side)(z:ℝ)(Z:ℝ):= Real.log z - Real.log Z/(k.val:ℝ)^4
lemma escort_data {a b:Side} (K₃:Ticket a v B b e x) (h': K.Coherent K₃) (f:b= 3*p) (g:Odd k.val)
 (p₀: 0 < ‖K.moment 1 q β u‖) (p₃: 0 < ‖K₃.moment 1 q β u‖) :
 0 < ‖K'.moment 1 q β u‖ ∧ lux k ‖K.moment 1 q β u‖ ‖K'.moment 1 q β u‖ ≤ (3/2:ℝ)^4 * lux 3 ‖K.moment 1 q β u‖ ‖K₃.moment 1 q β u‖ :=by
 let A:=heightK K q β u 1 p; let D₀:=A (Uniform 1); rw [forward K K' _ _ _ 1 h hk,forward K K₃ _ _ _ 1 h' f,K.starter]
 have he:= altitude K q β u 1 p (K.K.onGrid 0) hu k g; have hp :∀ t:Side,debit K q β u 1 p (Uniform t) = lux t D₀ (A (Uniform t)):=by intro t; unfold debit lux; rw [uni_v]; push_cast; rfl
 obtain ⟨a,b⟩:= he (by rw [←starter]; exact p₀) (by rw [←forward K K₃ _ _ _ 1 h' f]; exact p₃); exact ⟨a, by rw [hp,hp] at b; exact b⟩
omit hk h
lemma momentP : 0 ≤ moment K Z q β u:=by rw [moment_s, ←cluster_iff]; exact positive_cube K q β u Z p (K.K.onGrid 0) hu _
omit hu
lemma lux_nonneg₃ {a b:Side} (K₃:Ticket a v B b e x) (h': K.Coherent K₃) (hu:0≤u) (f:b=3*p)(p₃: 0 < ‖K₃.moment 1 q β u‖) : 0 ≤ lux 3 ‖K.moment 1 q β u‖ ‖K₃.moment 1 q β u‖:=by
 rw [K.starter,forward K K₃ _ _ _ 1 h' f] -- tune
 rw [show lux 3 _ _=debit K q β u 1 p (Uniform 3) from ?_]; swap; · unfold debit lux; rw [uni_v]; norm_num [heightK]
 exact base_debit K q β u 1 p (K.K.onGrid 0) hu (Uniform 3) (by rw [←K.forward K₃ _ _ _ 1 h' f]; exact p₃)
end Ticket
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ticket.escort_data
