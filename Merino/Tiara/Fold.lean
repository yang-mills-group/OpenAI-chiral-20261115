import Merino.Tiara.Coil
import Merino.Plume.Murky
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Afterglow Tower Lifted Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Journey Satin Sound

open Plume

variable {n:Side}(m:ℕ)(τ C L:ℝ)
abbrev centerB(n:Side)(m:ℕ):=purse m (0:Seat n)
/-- Qualification uniform on biographies of different tours:
locality, Lipschitz off a finite pattern, singlet. -/
structure Floss (R:Evaluation n):Prop where
 safety: AtSupport false (centerB n m) (toMark R)
 sang: covariant (toMark R)
 med(x):‖R x‖ ≤ C
 budget(x y):quiz m τ x=quiz m τ y→
   dist (R (dark n m x)) (R (dark n m y)) ≤ L*dist (echoC m x) (echoC m y)

structure Gilt (K: Calibration) (f:Tassels (Lattice.box m)):Prop extends Willow K C f where
 sport(i x y): quiz m τ x=quiz m τ y→
    dist (f i x) (f i y) ≤ L*dist (echoC m x) (echoC m y)
variable {m τ C L}
lemma vestibule: centerB n m ⊆ Satin.region (Lattice.box m) n:=by
 intro x h; exact mem_image.mpr ⟨Lattice.lift x,doorstep h, wrap_lift x⟩
lemma simple {R:Evaluation n}(r:Floss m τ C L R):LocalOn (centerB n m) R:=fun x y h=>r.safety.dep (x,x) (y,y) h h
lemma thresholdFloss {R:Evaluation n}(r:Floss m τ C L R)
 (t:Tivoli (Lattice.box m) n)(x:LinksC):
 R (graft (Lattice.box m) n x)=R (dark n m x):=by
 let u:Pane n:=graft (Lattice.box m) n x
 have h:Agrees (centerB n m) u (dark n m x):=by
   intro i g _
   let a:Edge Cover:= (Lattice.lift i.1,i.2)
   have e:(onC n u) a=x a:=tail (Lattice.box m) n t.hosp x _ (doorstep g)
   rw [key x g]
   have b:=onC_spec n u a
   rw [show a=(Lattice.lift i.1,i.2) from rfl] at b e
   simp only [wrap_lift] at b
   rw [← e,b]
 exact simple r _ _ h

variable {K:Calibration}{a:Side}
local notation "η"=>K.c a
abbrev dos (m:ℕ)(t:Tivoli (Lattice.box m) η)(R:Evaluation η):
 Tassels (Lattice.box m) :=fun i x=> Tower.costume _ K a t (R (graft (Lattice.box m) η x)) i

private lemma fee {R:Evaluation η}
 (t:Tivoli (Lattice.box m) η)(r:Floss m τ C L R)
 (i:Evens (Lattice.box m))(x y:LinksC)(h:quiz m τ x=quiz m τ y):
 dist ((dos m t R) i x) ((dos m t R) i y) ≤ L*dist (echoC m x) (echoC m y):=by
 let A:= R (dark η m x)
 let B:= R (dark η m y)
 have w:=r.budget x y h
 rw [dist_eq_norm] at w ⊢
 refine le_trans ?_ w
 simp only [dos,thresholdFloss r t]
 have k:=linearity _ K a t (q:=i) B A (-1)
 rw [neg_one_smul,add_comm,neg_one_mul,add_comm (-(costume _ _ _ _ _ _)), ←sub_eq_add_neg,←sub_eq_add_neg] at k
 change ‖Tower.costume _ K a t A i - Tower.costume _ K a t B i‖≤‖A-B‖
 rw [←k];exact biotech ..

/-- Extend each costed tour at its native volume; no lift assumption
on families of torus observables. -/
lemma fancy {R:Evaluation η}
 (t:Tivoli (Lattice.box m) η)(r:Floss m τ C L R):
 ∃ f,Gilt m τ C L K f ∧ braid K f a=toMark R:=by
 let f:=dos m t R
 let S:= Lattice.box m
 have u:AtSupport false (Satin.region (Lattice.box m) (K.c a)) (toMark R):=
    r.safety.mono vestibule
 have g i:=painting S K a t (toMark R) u i

 have e:braid K f=extendAtlas S K a t (toMark R):=by
   unfold braid extendAtlas;refine sum_congr rfl fun j _=>?_
   apply congrArg (fun g=>Sound.note K g _)
   funext x
   simp only [f,dos,comp_apply,Tower.piece,toMark,replant,S]
 refine ⟨f,⟨⟨?_,?_,fun i x=> (Tower.biotech S K a t (R (graft _ _ x)) i).trans (r.med _),?s⟩,fee t r⟩,?n⟩
 case n=> rw [e,native S K a t _ u]
 case s=> rw [e]; exact atlas_color K a t u r.sang
 · intro i
   have v:Measurable (Tower.piece S K a t (toMark R) i ∘ (fun Z:LinksC=>(Z,Z))):=(g i).env.meas.comp (measurable_id.prodMk measurable_id)
   simpa only [Function.comp_def,Tower.piece,toMark,replant,f,S] using v
 · intro i x y h
   have v:=(g i).locus (x,x) (y,y) h h
   simpa only [Tower.piece,toMark,replant,f,dos,S] using v

/-- Say it through `ship`: regulator side presented by a formula
equal to K.c. -/
lemma fancy_at (e:K.c a=n)(h:Tivoli (Lattice.box m) n){R:Evaluation n}
    (r:Floss m τ C L R):
 ∃ f,Gilt m τ C L K f ∧ ship e (braid K f a)=toMark R:=by
 subst n;exact fancy h r

lemma void {m:ℕ}(h:0≤C)(w:0≤L):
    Gilt m τ C L K (fun _ _=>0):=by
 refine ⟨⟨fun _=>measurable_const,fun _ _ _ _=>rfl,fun _ _=>norm_zero.trans_le h,?_⟩,fun _ _ _ _=>
   (dist_self _).trans_le (mul_nonneg w dist_nonneg)⟩
 rw [show braid K (S:=Lattice.box m) (fun _ _=>0)=0 from ?_]
 · exact covariant_zero _
 funext i V;simp [braid, note_v]

end YM.CF.Merino.Tiara
