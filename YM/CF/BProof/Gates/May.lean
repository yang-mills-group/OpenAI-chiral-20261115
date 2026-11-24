import YM.CF.BProof.Gates.Foundation
import YM.CF.BProof.Mapping.Plate

/- Away from raw bad, Face labels & link usage short. condition well whether tests passed.
 Not relying on good patch connectivity through diagonal corner-contact of two arbitrary
 blocks. Use Plate connectivity inside tangent patch when `uniform` needed.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates.Stage.Setup
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){s:Side}(Y:S.Setup L a s d y)
variable (T:PathData G)(θ:ℝ)(x:Pawn Y.yard)(h:T.Bounds c w R v)(k:θ∈Set.Icc (1/2) 2)
abbrev Block (Y:S.Setup L a s d y) := House.Block Y.yard Y.c'
abbrev Place (b:Y.yard.Col):= House.hide Y.yard Y.g b
def Clear (t:ℕ)(a:Y.Block):=Disjoint (Y.bad x) (House.ray Y.yard a t) -- Clear iff distance >t
abbrev Green (p:Y.yard.Col) := Clear Y x 1 (Y.Place p)
lemma green (b:Y.yard.Col)(p:Green Y x b) (a:Y.yard.Col) (v:(Gauss.base Y.yard).N b a Y.g.count.val):a∉Model.raw y Y.yard x.sev x.gauss:=by
 intro he; apply Finset.disjoint_left.mp p (mem_image_of_mem _ he); apply (House.ray_spec ..).2; exact ⟨House.near_hide Y.yard Y.g b a 1 (by simpa only [one_mul]),v.1.symm⟩
include P
lemma cover : 1+steady c Y.yard.short S.M R y≤ Y.g.count.val:= (Y.agenda P).coverage -- tune include
lemma ease : Ease S.K c Y.yard.short S.M R S.κ y:=by rw [Y.width]; exact P.dull.ease
include h k
lemma green_wave (b:Y.yard.Col)(p:Green Y x b) (a:Y.yard.Col) (v:(Gauss.base Y.yard).N b a 1) (i:Y.yard.Apt): cd G (Locale.A Y.yard y a i) (Pawn.level x y T θ (soil P Y) a i)≤ wc y:= by
 let p':=Y.pulse P; exact Pricing.Model.temper S.K S.P c S.M R S.κ y Y.yard T p' (room P Y) h k x.sev x.gauss x.gap a _ le_rfl (fun j q=>green Y x b p j ((Gauss.base _).mono (cover P Y) ((Gauss.base _).triangle v q))) (ease P Y) i
variable {i:Y.yard.Index}(b:Bool)(p:Space s)
abbrev owner (p : Space s):Y.yard.Col:= (Y.yard.location i b,p)
abbrev obtainF := inlet (Y.yard.u i) Y.yard.long (F' P Y T θ x) b
abbrev sig := x.mood i (b,p)
abbrev swell := Face.Mood S.K y (obtainF (i:=i) P Y T θ x b) p (color P Y T θ x i b p)
variable (u:¬Y.yard.D i)
include u
lemma breezy (v:Green Y x (owner Y (i:=i) b p))(q:Space s)(e:Grid.dist p q≤1)(r:TAxis): cd G (Mag.bg y r) (obtainF (i:=i) P Y T θ x b (q,r)) ≤ wc y:=by
 unfold obtainF F'; rw [x.paid y T θ _ i b u]; exact green_wave P Y T θ x h k _ v (owner Y (i:=i) b q) ⟨rfl,e⟩ (Y.yard.lastDepth,r) -- tune last_depth background
lemma colorful (v:Green Y x (owner Y (i:=i) b p)): swell (i:=i) P Y T θ x b p ∧ cd G (color P Y T θ x i b p) (Mag.center (sig Y (i:=i) x b p)) ≤ S.scene.C*Face.fine y:=by
 let D:=obtainF P Y T θ x b (i:=i); have hx(j:Fin 3):=breezy P Y T θ x h k b p u v p (by simp) j
 have he : color P Y T θ x i b p=Face.orient S.K y D p (sig Y x b p (i:=i)):=by unfold color Pawn.rent sweepLabel; rw [if_neg u]; rfl
 unfold swell; rw [he]; refine P.dull.view s D p (fun i'=>?_) _
 let f:=Mag.f₁ i'; let q:=Mag.f₂ i'
 have hp(j l): cd G (Mag.bg y j) (D (p+tstep l,j))≤wc y:= by apply breezy P Y T θ x h k b p u v; exact Face.slide_t .. ▸ Grid.near_slide ..
 apply (Mag.curl_bound ..).trans; exact (add_le_add (add_le_add (add_le_add (hx f) (hp q f)) (hp f q)) (hx q)).trans_eq (by ring) -- tune
lemma fol (r:TAxis)(v:Green Y x (owner Y (i:=i) b p))(w:Green Y x (owner Y (i:=i) b (p+tstep r))) : Face.Follow y (color P Y T θ x i b p) (color P Y T θ x i b (p+tstep r)) (obtainF (i:=i) P Y T θ x b (p,r)) ↔ sig Y x b p (i:=i)=sig Y x b (p+tstep r) (i:=i):= P.dull.lead _ _ _ _ _ r (colorful P Y T θ x h k b p u v).2 (colorful P Y T θ x h k b _ u w).2 (breezy P Y T θ x h k b p u v p (by simp) r)
lemma frozen (r:ℕ) (a:Space Y.c')(hv:∀ q:Space s, Grid.dist a (elder Y.g q)≤r → Green Y x (owner Y (i:=i) b q))(k':certified P Y T θ x) (v:Grid.dist a (elder Y.g p)≤r): sig Y x b p (i:=i)= sig Y x b (Grid.grow Y.g a) (i:=i):=by
 refine Mapping.Plate.ticket _ _ _ _ r a v (by simp) (fun x' j u' e=>?_); rw [Face.slide_t] at e ⊢; apply (fol P Y T θ x h k b x' u j (hv _ u') (hv _ e)).1; exact (yard_climb P Y T θ x k' i u b).2 _ _
end YM.CF.BProof.Gates.Stage.Setup
