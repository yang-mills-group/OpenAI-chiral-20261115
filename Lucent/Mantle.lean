import Lucent.Reveil
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment
set_option quotPrecheck false

open Peaks Scree Mir Buffered.Afterglow
open Lattice
open RG
variable (N:Side)(s:ℤ)
local notation:max "pl" s:max => plane 3 s
local notation:max "mₛ" s:max => (pl s).motion
local notation:max "fₛ" s:max => (pl s).flee
local notation:max "t₃" s:max N:max => theta (carR 3 s N)

variable {I J:Type}
abbrev rods (s:ℤ)(W:I→Staff): I→Staff := sash s∘W
def Join.hammer (q:Join I) : Join I:= ⟨q.flash,q.loom.map (Prod.map id Prod.swap)⟩
def Bill.cameo (q:Bill I):Bill I:=⟨q.toJoin.hammer,star q.k⟩
def castDown (S:Stencil I):Stencil I:=⟨S.out.map Bill.cameo⟩
lemma castGrade {m d:ℕ}{S:Stencil I}(h:S.degree m d): (castDown S).degree m d:=by
 intro q v; change q∈S.out.map Bill.cameo at v; obtain ⟨i,z,rfl⟩:=List.mem_map.mp v; obtain ⟨a,b⟩:=h i z; exact ⟨a,(List.length_map ..).trans b⟩

variable (W:I→Staff) (S:Stencil I)(G:I→SU.group.Color)
lemma glint_r (x:Tint I→ℝ)(L:List (Tint I)): star (glint x L)=glint x L:=by
 induction L with|nil=>simp [glint_nil]|cons i L ih=>rw [glint_cons,star_mul',ih]; simp

lemma hammer_pay (q: Join I): (t₃ s N) (knit N W G q)= knit N (rods s W) G q.hammer:=by
 obtain ⟨u,v⟩:=q; unfold knit; rw [theta_smul,glint_r]; refine congrArg ((glint (hues G) u) • ·) ?_
 change (t₃ s N) (weave N (seat W) _ v) = weave N _ _ (v.map _)
 induction v with
 | nil=>exact theta_one _
 | cons i v ih=>unfold weave at *; rw [List.map_cons,List.prod_cons,List.map_cons,List.map_cons,List.prod_cons,theta_mul,cellSwap,ih]; try rfl

lemma dreamCast : t₃ s N (dream N W S G)=dream N (rods s W) (castDown S) G:=by
 cases S with
 | mk L=> induction L with
   | nil=>exact theta_zero _
   | cons j L ih=> unfold dream castDown at *; rw [List.map_cons,Stencil.cons_q,Stencil.cons_q,theta_add,theta_smul,hammer_pay,ih]; try rfl

def dayStars(W:I→ Staff):Prop:= ∀ i,day (W i).face.2
lemma cast_wide (r:ℕ)(ρ t:ℝ)(h:dayStars W): Celeste.fluent 3 s (kite r ρ t W S) = kite r ρ t (rods s W) (castDown S):=by
 funext n x; have hx:volley n W r ρ t (reflFields 3 s x).1= volley n (rods s W) r ρ t x.1:=funext fun i=> pearl_reflect n s _ _ _ _ _ (h i)
 unfold fluent reflMark kite; rw [hx,dreamCast]

lemma dream_sec : Sector univ false (dream N W S G) := by
 cases S with|mk L=>induction L with
 | nil=>exact .zero _
 | cons j L ih=>
    have hx : Sector univ false (spind N W j.loom) := by
      generalize j.loom=l; induction l with
      | nil=>exact .one
      | cons i l h=>
        have u : Sector univ false (cell N (W i.1).u (W i.1).spin i.2.1 i.2.2):=(Cin.uncreate _).mul (Cin.unremove _)
        exact u.mul h
    exact .add ((hx.scale (glint (hues G) j.flash)).scale j.k) ih

lemma singingCast(h:Singing W S): Singing (rods s W) (castDown S):=by
 intro n G g
 let j:=(pl s).anon n
 have z:crown n (rods s W) g G=crown n W (g ∘ j) G:=by 
    have hp(i): (rods s W i).scope n=j ((W i).scope n):= ((pl s|>.anno (W i).xo).trans (congrArg _ ((pl s).mote _))).symm
    funext i; unfold crown; rw [hp]; rfl
 rw [z,←dreamCast,←dreamCast,h]
 exact theta_twist_right _ _ _ (congrArg Subtype.val (Lifted.gaugeSquare 3 s n g)) (dream_sec ..)

section new
variable (V:J→Staff)(q:I→J)(H:J→SU.group.Color)

lemma readdressDream : dream N V (S.remake q) H = dream N (V ∘ q) S (H ∘ q):=by
 unfold dream; rw [Stencil.remake_q]; congr; funext j; unfold knit glint spind weave; rw [List.map_map,List.map_map]; rfl
lemma singingRemake (h:Singing (V ∘ q) S): Singing V (S.remake q):=by
 intro N M g; rw [readdressDream,readdressDream]; exact h N (M ∘ q) g
lemma kite_readdress (r:ℕ)(ρ t:ℝ): kite r ρ t V (S.remake q)=kite r ρ t (V ∘ q) S:= funext fun n=>funext fun x=> readdressDream n S V q _
end new
lemma Singing.both {S T:Stencil I} (h:Singing W S) (k:Singing W T) : Singing W (S*T):=by intro n G g; rw [dream_mul,dream_mul,h,k,map_mul]
