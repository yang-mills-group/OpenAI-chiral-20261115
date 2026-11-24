import YM.SU5.FiniteGaugeData.Pannier.FoyerSeat
import YM.SU5.FiniteGaugeData.Tapestry.Neutral
/-!
# Native filament check

The tomes (in Filigree.lean) will require cover data actually carried forward at this observing scale.
Here also store the witness's native operator properties. Identity-subtraction leaves only words
with at least one anchored removal, all removals charged and at *distinct* announced centers,
all corresponding creators away from *all* those centers. All in one species.
No adjoints of the physical algebra inserted here: this is Fine.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Window (mem_Tset family)
open Py.Rate.Pannier
open Lifted
open Reed (Fine)
open Afterglow
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{M:Tulip.Male}{n:Side}{o:Seat n}{k d:ℕ}{r:Fin k→ Site n}
variable {D T:Finset (Seat n)}{a:Fin k}{s:SU.Slot}{W:Window.Family}{x y:Ket (Single n)}{f:FC (Single n)}
structure Removal (W:Window.Family)(r:Fin k→ Site n)(a:Fin k)(x: Ket (Single n)) : Prop where
  venue: withinM (modesIn n {node (r a)}) x
  spin: withinM (Tset n)ᶜ x
  foot: withinM (labelQ n W) x
structure Creator (W:Window.Family)(r:Fin k→ Site n)(D:Finset (Seat n))(x: Ket (Single n)) : Prop where
  venue: withinM (modesIn n D) x
  spin: withinM (Tset n) x
  foot: withinM (labelQ n W) x
  banned: withinM (modesIn n (VolumeX r))ᶜ x
lemma waveRoll (s:SU.Slot)(i:Fin k): Removal (family s) r i (Waved (r i) s):= ⟨waved_stand ..,by unfold withinM; rw [dim_cut]; exact waved_pay ..,within_basis _ (Poi (r i) s) ((labelAt ..).2 rfl)⟩
lemma waveLift (p:1 ≤ j)(u:VolumeX r ⊆ BlockP d o)(l:IsUnit (Fock.padded (modesIn n (VolumeX r)) (sp false j M (1:Pane n)))) (s:SU.Slot)(i:Fin k)(x:Pane n): Creator (family s) r (BlockP d o) (Forward o d r j M s i x):=⟨out_turn ..,out_half ..,out_bank l p i x, blankPaid u l i⟩ -- order of feet?
lemma mode_color (V:Seat n→SU.E)(D: Finset (Seat n))(x:Ket (Single n)) (h:withinM (modesIn n D)ᶜ x):withinM (modesIn n D)ᶜ (acts (tradew n V).val x):=by
 unfold withinM at *; rw [dim_cut] at h ⊢; exact trim_field (by rw [map_sub,map_one,show twist (tradew n V) (cutM (modesIn n D))= _ from gauge_frost D V]) h
lemma Removal.germ (V:Seat n→SU.E)(h:Removal W r a x) : Removal W r a (acts (tradew n V).val x):=by
 refine ⟨coverSense.mpr h.venue, ?_, (book_rest ..).2 h.foot⟩; have he:=h.spin; unfold withinM at *; rw [dim_cut] at he ⊢; exact (sense (b:=true)).2 he
lemma Creator.germ (V:Seat n→SU.E)(h:Creator W r D y) : Creator W r D (acts (tradew n V).val y):=⟨coverSense.mpr h.venue,(sense (b:=false)).2 h.spin,(book_rest ..).2 h.foot,mode_color V (VolumeX r) y h.banned⟩ -- syntax mode_color .. h
inductive Line (W:Window.Family)(r:Fin k→Site n)(D:Finset (Seat n)) : List (Fin k) → FC (Single n) → Prop where
 | nil : Line W r D [] 1
 | push {l x y f}(i:Fin k): Removal W r i x → Creator W r D y → Line W r D l f → Line W r D (i::l) ((remove x*create y)*f)
def Hap (W:Window.Family)(r:Fin k→Site n)(D:Finset (Seat n)) := Submodule.span ℂ { f| ∃ l,l ≠ [] ∧ l.Nodup ∧ Line W r D l f}
lemma emplace {K:List (Fin k)}(p: K ≠ [])(q:K.Nodup)(v:Line W r D K f): f∈ Hap W r D:= Submodule.subset_span (show _∈ {f|∃ l,l ≠ []∧ l.Nodup∧ Line W r D l f} from ⟨K,p,q,v⟩)
def bloomSolo (S:Finset (Fin k)) (l:List (Fin k)):List (Fin k):=l.filter fun i=> i∈ S
private def Lathe(W:Window.Family)(r:Fin k→Site n)(D:Finset (Seat n))(L:List (Fin k)):Submodule ℂ (FC (Single n)):= Submodule.span ℂ {f|∃ K:List (Fin k), K ≠ [] ∧ K.Sublist L ∧ Line W r D K f}
private lemma hurls {L:List (Fin k)}(a:Fin k)(p:Removal W r a x)(t:Creator W r D y)(h: f∈ Lathe W r D L): remove x*create y * f∈ Lathe W r D (a::L):=by
 refine Submodule.span_induction (p:=fun f _=> _ * _ * f ∈ _) (fun f v=> ?_) (by simp) (fun x y u v hx hy=> by rw [mul_add]; exact Submodule.add_mem _ hx hy) (fun x y u v=> by rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ _ v) h -- tune
 obtain ⟨l,d,q,H⟩:= v; exact Submodule.subset_span (show _∈{f|∃ K:List (Fin k), K ≠ [] ∧ K.Sublist (a::L) ∧ Line W r D K f} from ⟨_,by simp,List.Sublist.cons₂ _ q,(Line.push a p t H)⟩)
private lemma journeyUp (b:1≤j)(e:VolumeX r ⊆BlockP d o)(g:IsUnit (Fock.padded (modesIn n (VolumeX r)) (sp false j M (1:Pane n)))) (s:SU.Slot)(L:List (Fin k))(x:Pane n): (((L.map fun a=>handy false (Tset n) (Waved (r a) s) (astral o d r j M s a x)).prod)-(1:FC _))∈ Lathe (family s) r (BlockP d o) L:= by
 let S:= BlockP d o; let X(i:Fin k):= Waved (r i) s; let Y(i:Fin k):= Forward o d r j M s i x
 induction L with
 | nil=> simp
 | cons a L ih=>
    let F:=(L.map (fun i=> handy false (Tset n) (X i) (astral o d r j M s i x))).prod -- tune
    let R:= remove (X a)* create (Y a); let Z:= Lathe (family s) r S (a::L); change (1+R)*F-1∈ Z; rw [show (1+R)*F-1= R+(F-1)+R*(F-1) from ?_]; swap; · rw [add_mul,one_mul,mul_sub,mul_one]; abel
    have u: Lathe (family s) r S L≤ Z:= Submodule.span_mono fun i h=> by obtain ⟨l,g,h,w⟩:=h; exact ⟨l,g,h.cons a,w⟩ -- note h.cons
    have hx:= waveRoll (r:=r) s a; have v:= waveLift b e g s a x
    exact Z.add_mem (Z.add_mem (Submodule.subset_span (show R∈ {f|∃ K:List (Fin k), K ≠ [] ∧ K.Sublist (a::L) ∧ Line (family s) r S K f} from ⟨[a],by simp,by simp,(by have hp:= Line.push a hx v Line.nil; rw [mul_one] at hp; exact hp)⟩)) (u ih)) (hurls _ hx v ih)
lemma blossomHap (b:1≤j)(e:VolumeX r ⊆BlockP d o)(g:IsUnit (Fock.padded (modesIn n (VolumeX r)) (sp false j M (1:Pane n))))(x:Fields n): ((repast o d r j M s).frame-(1:Mark n)) x∈ Hap (family s) r (BlockP d o):=by
 have p:(race k).Nodup:=List.nodup_ofFn_ofInjective injective_id
 have ht: Lathe (family s) r (BlockP d o) (race k) ≤ Hap (family s) r (BlockP d o):= Submodule.span_mono (by rintro a (⟨L,w,a1,g⟩:∃ L,L ≠ []∧_∧_); exact ⟨_,w,p.sublist a1,g⟩) -- tune
 change (repast _ _ _ _ _ _).frame x-1∈_; rw [tasteR]; exact ht (journeyUp b e g s _ _)
lemma Line.germ (V:Seat n→SU.E)(L:List (Fin k))(p:Line W r D L f) : Line W r D L (twist (quantU (tradew n V)) f):=by
 induction p with
 |nil=>rw [map_one]; exact Line.nil
 |push i u v p ih=> rw [map_mul,map_mul,twist_create,twist_remove]; exact Line.push _ (u.germ _) (v.germ _) ih
lemma Hap_germ (V:Seat n→SU.E)(p:f∈ Hap W r D) : twist (quantU (tradew n V)) f ∈ Hap W r D:=by
 let S:= Hap W r D; let U:= twist (quantU (tradew n V)); change U _∈ S
 refine Submodule.span_induction (p:=fun f _=> U f∈S) (fun f v=>?_) (by simpa using S.zero_mem) (fun a b _ _ x y=> by rw [map_add]; exact S.add_mem x y) (fun z a _ u=> by unfold U; rw [Fock.twist_scalar]; exact S.smul_mem _ u) p
 obtain ⟨l,h,x,z⟩:=v; exact emplace h x (z.germ ..)
lemma Hap_Fine (u: VolumeX r⊆ D)(p:f∈ Hap W r D): Fine (Tset n) (modesIn n D) false f := by
 refine Submodule.span_induction (p:=fun f _=>Fine _ _ false f) (fun f v=>?_) (.empty _) (fun _ _ _ _ x y=> x.add y) (fun a _ _ x=> x.scale a) p
 obtain ⟨l,v,w,h⟩:=v; clear p v w; induction h with
 | nil=> exact Fine.one
 | push i g q h ih=> exact ((fine_remove _ g.spin (within_more g.venue (modes_monotone (singleton_subset_iff.mpr (u (mem_image_of_mem (node ∘ r) (mem_univ i))))))).grow (fine_create _ q.spin q.venue)).grow ih
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.blossomHap
#print axioms YM.CF.Pannier.Chancel.Hap_germ
