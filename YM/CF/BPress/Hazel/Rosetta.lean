import YM.CF.BPress.Hazel.Calendar
import YM.CF.BPress.Bias.Burn
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Locale Tunnel Bands Branch Clipγ Letter Chrono Meadow.Frame Meadow.Stamps
open Bias
variable (X:Bands s B)
def pivotal (i:X.Index) : SU.E:=if i∈X.dc then 1 else orb z
abbrev readBase(s: Side)(t:ℝ):=theme (0,t) -- Height. Clue day * lift
abbrev MiniMark (i:X.Index) (x:Site s):=scaledV (pivotal z X i) Seed
abbrev PlateM (i:X.Index)(t:ℝ) (x:Site s):= swivelC (pivotal z X i) (theme (0,t))
def Reference : Letter X:= ⟨fun _=>Mag.center z,fun _=>z,MiniMark z X,PlateM z X⟩
lemma ref_h : (Reference z X).Tint:=by
 constructor
 · intro i; let u:= pivotal z X i; refine {
     scheme :=fun i x=> turn_plan (theme_v _) u
     station t p:= funext fun i=>congrArg (swivelC u) (theme_exit p _)
     origin x:=by change swivelC u (theme (0,0))= fullM (scaledV u Seed).val; rw [theme_entry,shuffle_r]; rfl
     smooth:=fun i=> (swivel_smooth u).comp ((theme_s).comp (f:=fun x:ℝ=> (0,x)) (by fun_prop))
     pace:=fun x=> ?_
   }
   apply LipschitzOnWith.of_dist_le_mul; intro q a y b; rw [dist_eq_norm]; change ‖swivelC u (theme (0,q))-swivelC u (theme (0,y))‖≤ _; rw [Paint.iso, ←dist_eq_norm]; exact (day_plan (X.band i)).pace x|>.dist_le_mul q a y b
 · intro i h x u; unfold Reference MiniMark PlateM; dsimp only; rw [pivotal,if_pos h,scaled_one]; exact ⟨rfl,fun _=> turn_one ..|>.trans (theme_o _ _ (by norm_num))⟩
 intro i h x u t; unfold Reference frameN MiniMark PlateM pivotal; dsimp only; rw [if_neg h]; exact ⟨rfl, fun v=> congrArg (swivelC _) (theme_o _ _ (by norm_num))⟩ -- tune order of unfold
lemma ref_grains(i:X.Index)(A:Support s) {u v:ℝ} (t:0≤u)(w:0 ≤v): Grains A (1:Micro s) ((Reference z X).plant i) ((Reference z X).brush i) u v:=by
 constructor; · intro j h; unfold Reference MiniMark urgent; dsimp only; rw [Pi.one_apply,scaled_one, dist_self]; exact t
 intro k l j h; unfold Reference fare PlateM; dsimp only; rw [Pi.one_apply, turn_one]; simpa
variable (W:Rental)(R:Hangar s)(m:Tiling s)
def RosettaX := Xactual W R ∅ (Reference z X) m 1
def Rosetta := Kactual W R ∅ (Reference z X) m 1
-- identity law gives true Licence if pre-prices.
section ferm
variable {N:Side}(X:Bands (More N) B)(W:Rental)(R:Hangar (More N))(m:Tiling (More N))
variable {r:Side}{q q' δ d:ℝ}{k:ℕ}(F:Booked d k W r q q')(c:StageC r q δ W B 0)(Z':Dusk B R W)(D:Record r (More N))
include F c Z'
lemma refLicence : Licence (R:=R) (Reference z X) D.key 0 ∅ (1:Micro (More N)) W q q' δ:=by
 let H:=(Reference z X); have hp: Grip X W R ∅ H (1:Micro (More N)) (soil r) (Chrono.η q) 0:={
    tint:=ref_h z X
    power:=Z'
    credit:=le_rfl
    nSeat:=fun x q=> by change chord (Mag.center z) (Mag.center z)≤0; rw [chord.refl]
    uSeat:=fun _ _ _ _ _=> (chord.refl (1:E)).le
    settle:=fun _ _ _ _ _=>rfl
    safe_g:=fun i=> ref_grains z X i _ (by unfold soil; positivity) (by unfold Chrono.η; positivity [F.good_q]) -- syntax
 }; have he:Rings (1:Micro (More N)) univ (climate r):=by intro i t; rw [←chord.one,show faceValue (1:Micro (More N)) i=1 by simp [Lattice.faceValue, BPress.Travel.price],chord.refl]; unfold climate; positivity -- tune
 let Q:=legit c F.credit F.tone F.good_q.le hp D he; exact ⟨hp,Q, shake Q c.wage c.bear c.radiusC le_rfl⟩
end ferm
-- for arbitrary tiling nose with stopped; preserve HARD exact H equality incl all v.
variable {q q' δ g h:ℝ}
theorem read_ref {c:ℝ}{p:Grip X W R ∅ (Reference z X) 1 g h c}(P:Stopped (Reference z X) m p q q') (x:Site s) : RosettaX z X W R m x= (Reference z X).G x∧ ∀ v,Rosetta z X W R m v x=H W (Reference z X) v x:= by
 refine P.groomed ?_; unfold Danger Near Local; simp [halo_spec]
section time
open Bias.Sails Bias.Taper
-- Taper x supports
variable {c:ℝ}{p:Grip X W R ∅ (Reference z X) 1 g h c}(P:Stopped (Reference z X) m p q q')
include P
lemma path_shape {x y:Site s}(h:x 0=y 0)(u:ℝ): Rosetta z X W R m u x= Rosetta z X W R m u y:=by
 simp_rw [(read_ref z X W R m P _).2]; by_cases p: Welkin X x
 · obtain ⟨i,p⟩:= p; obtain ⟨b,c⟩:= Tent.corners (X.mark i) p h; rw [Hband W (Reference z X) p,Hband W (Reference z X) b]; have f:correction W i x↔ correction W i y:= by unfold correction; rw [c]
                                                             -- tune
   by_cases e:correction W i x; rw [if_pos e,if_pos (f.mp e)]; unfold amend; rw [c]; rfl; rw [if_neg e,if_neg (mt f.mpr e)]; rfl
 have e:¬ Welkin X y:=by rintro ⟨i,f⟩; exact p ⟨i,(Tent.corners (X.mark i) f h.symm).1⟩
 rw [Hmiss W (Reference z X) p,Hmiss W (Reference z X) e]; change dict z (_ ,u)= dict z (_,u); unfold zoneD adult age corner; simp only [town,h] -- tune
lemma stamp_ref {i:X.Index}{x:Site s}(f:x∈ X.band i): Rosetta z X W R m 2 x = if X.Dmark i then Music.basis else Music.wave z:=by
 rw [(read_ref z X W R m P _).2, H_later W (Reference z X) (ref_h ..) p.power.summer f le_rfl]; change swivelC (pivotal z X i) (theme (_, _)) = _; unfold pivotal; rw [theme_o _ _ (by norm_num), alpha_final (by norm_num : (1/2:ℝ) ≤ 2),shape_cost.tail]; simp only [dc_index]; split; exact turn_one ..; rfl
end time
end YM.CF.BPress.Hazel
