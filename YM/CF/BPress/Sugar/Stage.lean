import YM.CF.BPress.Mount.Cast
import YM.CF.BPress.Lily.Vases
import YM.CF.BPress.Hazel.Red
import YM.CF.BPress.Hazel.Seers
/-! Hallowed portrait machinery.Herm.* Uses arbitrary color.Huge. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Sugar
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary Hazel Mount Stamps Skye Port Locale Cube
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N:Side}{B:BandWidth}(A:Bands (More N) B)(R:Hangar (More N))
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor
structure Stage (N:Side) where
 W:Rental
 tile:Grid.Tiling (More N)
 q:ℝ
 qX:ℝ
 δ:ℝ
namespace Stage
variable (X:Stage N)
def mine(L:Letter A)(b:Seal (SiteX A R))(U:Micro (More N))(c:ℝ) :Prop:= Licence (R:=R) L X.tile c b U X.W X.q X.qX X.δ
variable (Y:Driver N) (L:Letter A)(M: Seal (SiteX A R))(U: Micro (More N))
abbrev way := Xactual X.W R M L X.tile U
abbrev tower := Kactual X.W R M L X.tile U
abbrev keycap:= Picks A R M -- tuning X not included
lemma travel {c:ℝ}(T: Stage.mine A R X L M U c)(b:ℝ)(h:X.qX<b) : Slow U (hook (way A R X L M U)) b:=by
 intro x i; exact ((urgent_norm U (x,i) _).trans_le ((show Licence _ _ _ _ _ _ _ _ _ from T).progress.on_torus.1 (x,i) (by simp [inside, inside_iff]))).trans_lt h -- tune reducible mine as .2?
-- pose.NewTech
variable {c d:ℝ}(P:Licence (R:=R) L X.tile c M U X.W X.q X.qX X.δ)
include P
lemma towers : Plot (tower A R X L M U):=fun x=> (P.progress.Ksmooth x).continuous
lemma towerD : Plot (primeC (tower A R X L M U)):= fun i=>(continuous_apply i).comp (dconC _ (fun i=> P.progress.Ksmooth i))
omit P
def sketch : Plain N:= portrait _ _ (towers A R X L M U P) (towerD A R X L M U P) (way A R X L M U) U (Picks A R M)
include P
lemma sketch_spin{t:ℝ}(v:t∈ Set.Icc (0:ℝ) 2): let b:=sketch A R X L M U P; b.spin false t=tower A R X L M U t∧ b.spin true t=primeC (tower A R X L M U) t:=early_bill _ _ _ _ _ _ _ _ v -- tune needs v
omit P
structure Stamp (Y:Driver N): Prop where
 right : X.qX < Y.p
 stamp(L:Letter A)(M:Seal (SiteX A R))(U:Micro (More N))(c:ℝ)(p:Licence (R:=R) L X.tile c M U X.W X.q X.qX X.δ): Guard U Y.d→ Y.Hallowed (sketch A R X L M U p)
lemma stamp {H Z α: Pledge}{v n:ℕ}{d g:ℝ}{u:Side}{t:Worthy H Z α Y.j d X.q g v}(K: Voucher t u Ringmark 3 Y.v X.W.P n Y.ε X.δ)(hc: Y.d≤d)(k:0<Y.d)(a:X.qX<Y.p)(f:n≤N.val)(h: B.D=u.val)(ℓ: max 1 (priceTone:ℝ) ≤ Y.h)(v:Y.Wish H Z α) : Stamp A R X Y:=by
 refine ⟨a, ?_⟩; intro L M U c P l; let C:= tower A R X L M U; let b:= sketch A R X L M U P; let U':Spin.OpenW N Y.d:= ⟨U,l⟩; let p:= key b; have hp:b.key=Picks A R M:= portrait_key ..; have ht:= passport C (primeC C) (towers A R X L M U P) (towerD A R X L M U P) (way A R X L M U) _ _ P.looks; have he:Dark A p:=(show _ = p from hp.symm) ▸ (dark A R M); refine {
   glow:=l
   tuneK:=travel A R X L M U P _ a
   state:= point K f k hc Y.M Y.F v.pay U' h p he _ _ (show Looks U p (b.spin false) (b.spin true) X.W.P Ringmark 3 X.q X.δ from ht)
   day:=ht.guards 2 (by norm_num)
   toll:= fun t ht i v=>le_trans ?_ ℓ
 }; change ‖b.spin v t i‖ ≤ _; have he:= sketch_spin A R X L M U P ht; cases v; rw [show b.spin false t=_ from he.1]; exact (Paint.MatPlan.one (P.progress.Kplan t) i).trans (le_max_left ..); rw [show b.spin true t=_ from he.2]; exact (pegged _ (fun x=> P.progress.rate x) i t ht).trans (le_max_right ..) -- tune args & open
variable {A R X Y L M U}
abbrev player(H:Stamp A R X Y)(P:Licence (R:=R) L X.tile c M U X.W X.q X.qX X.δ)(h:Guard U Y.d) : Y.Pose:= ⟨sketch A R X L M U P, H.stamp _ _ _ _ P h⟩
variable (H:Stamp A R X Y)(h:Guard U Y.d)
include P
lemma player_entry : Y.decks.H (player H P h) 0= fun i=> SU.Pair.fullM (hook (player H P h).val.X i):=by -- arg
 set v:Y.Pose:=player H P h; let Z:=tower A R X L M U; change v.val.spin false 0=_; rw [show v.val.spin false 0=Z 0 from (sketch_spin _ _ _ _ _ _ P (by norm_num)).1]; exact funext fun i=> P.progress.K_seed _
lemma player_key : Y.decks.seat (player H P h)= Picks A R M:= portrait_key ..
lemma player_KG : Y.decks.KG (player H P h)=tower A R X L M U 2:= (sketch_spin A R X L M U P (by norm_num)).1
lemma player_vase : Lily.Vase (Y.decks.KG (player H P h)) (Lily.interest A L) (Y.decks.seat (player H P h)) (Lily.vacancy A) (specialB X.W A R M):=by rw [player_key,player_KG]; exact Lily.valid_vase A L P.progress -- tune
end Stage
end YM.CF.BPress.Sugar
