import YM.CF.BPress.Neumann
import YM.CF.BPress.Assignment
import YM.CF.BPress.Law
import YM.CF.BPress.SumTool
/-! Sum over location labels with restricted allowed sets, frame products counted exactly (implicitly same lift). This interface uses internal per-Mark 2 × label set; switch to gap-wise labels later. `payments` for all charged links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Tunnel Finset RG Wilson
open scoped Topology BigOperators Classical Matrix
namespace Bands
variable {s:Side}{B : BandWidth}{T : BPress.Sheet.Atlas}{y C C' Lf : ℝ}{N:ℕ}(F:Net s T Lf y C C' N) (X:Bands s B) (U : Micro s)
abbrev Labels (s:Side):= Sheet.Law s × Sheet.Law s
abbrev Slates := X.Index→ Labels s
variable (T y)
def choices (i:X.Index) : Finset (Labels s):= if i∈X.dc then {0} else T.room y (((X.mark i).reads U).1) ×ˢ T.room y (((X.mark i).reads U).2)
def putF (k:X.Index)(i:Labels s): Duo s:= if k∈X.dc then 1 else (T.frame y (((X.mark k).reads U).1) i.1,T.frame y (((X.mark k).reads U).2) i.2)
def permit : Finset (X.Slates):= Fintype.piFinset (X.choices T y U)
lemma choices_D {i : X.Index}(p:i∈X.dc): X.choices T y U i={0}:=if_pos p
lemma putF_D {i:X.Index}(p:i∈X.dc)(k): X.putF T y U i k=1:=if_pos p
lemma putF_s (k:X.Index)(v:k∉X.dc): Injective (X.putF T y U k):=by intro i j e; unfold putF at e; split at e; contradiction; exact Prod.ext (T.frame_inj y _ (congrArg Prod.fst e)) (T.frame_inj y _ (congrArg Prod.snd e)) -- tune
lemma choices_B {k:X.Index}(v:k∉ X.dc) : (X.choices T y U k).image (X.putF T y U k) = T.pairs y ((X.mark k).reads U):= by
 unfold putF choices; simp only [if_neg v]; let W:= X.mark k; let H:= W.reads U; ext p; rcases p with ⟨a,b⟩; simp [Sheet.Atlas.pairs,Sheet.Atlas.seats]; -- maybe aesop after
 constructor; rintro ⟨i,j,⟨a,b⟩,e,v⟩; exact ⟨⟨i,a,e⟩,j,b,v⟩; rintro ⟨⟨i,q,v⟩,l,u,k⟩; exact ⟨i,l,⟨q,u⟩,v,k⟩
lemma putF_local (i:X.Index)(k:Labels s): LocalOn (X.band i) (fun U : Micro s=> X.putF T y U i k):= fun U V p=> by unfold putF; dsimp only; rw [(X.mark i).reads_local U V p]
lemma choices_local (i:X.Index) : LocalOn (X.band i) (fun U : Micro s=> X.choices T y U i):= fun U V p=> by unfold choices; dsimp only; rw [(X.mark i).reads_local U V p]
lemma choices_air {U V:Micro s}(p:Set.EqOn U V X.air)(i:X.Index): X.choices T y U i=X.choices T y V i:=by
 unfold choices; split; rfl; next t=> rw [(X.mark i).reads_crown U V (p.mono (X.crown_air i (fun h=> t ((X.dc_index ..).mpr h))))]
lemma permit_air {U V:Micro s}(p:Set.EqOn U V X.air): X.permit T y U=X.permit T y V:=by unfold permit; rw [show X.choices T y U=X.choices T y V from funext fun i=> X.choices_air _ _ p i]
lemma putF_air {U V:Micro s}(p:Set.EqOn U V X.air)(i:X.Index)(l:Labels s): X.putF T y U i l=X.putF T y V i l:=by
 unfold putF; split; rfl; next t=> rw [(X.mark i).reads_crown U V (p.mono (X.crown_air i (fun h=> t ((X.dc_index ..).mpr h))))]
lemma putF_meas (i:X.Index)(v) : Measurable (fun U:Micro s=> X.putF T y U i v):=by
 unfold putF; split; exact measurable_const; exact Measurable.prodMk ((T.frame_meas y _).comp (measurable_fst.comp (X.mark i).reads_cont.measurable)) ((T.frame_meas y _).comp (measurable_snd.comp (X.mark i).reads_cont.measurable))
lemma choices_meas (i:X.Index)(v) : MeasurableSet {U:Micro s| v∈X.choices T y U i}:=by
 unfold choices; split; exact (by by_cases h:v=0<;>simp [h]); simp_rw [mem_product,Sheet.Atlas.room_ok, Set.setOf_and]; let W := X.mark i; have f (q : Micro s → Horiz s)(p:Measurable q)(h) : MeasurableSet {U:Micro s| T.allowed y (q U) (T.frame y (q U) h)}:= (p.prodMk ((T.frame_meas y _).comp p)) (T.allowed_meas y);
 exact (f (horizontal W.o) (cont_horizontal W.o).measurable _).inter (f (horizontal W.last) (cont_horizontal W.last).measurable _)
lemma permit_meas (w : X.Slates): MeasurableSet {U: Micro s| w∈ X.permit T y U}:=by simp_rw [permit,Fintype.mem_piFinset,Set.setOf_forall]; exact MeasurableSet.iInter fun i=> X.choices_meas T y _ _
lemma choices_bound (h:T.Coasts y)(i:X.Index): (X.choices T y U i).card≤25:=by
 by_cases v:i∈ X.dc; rw [X.choices_D _ _ _ v]; simp; rw [←card_image_of_injective (X.choices T y U i) (X.putF_s _ _ _ _ v),X.choices_B T y U v]; exact T.pairs_ceiling y _ h -- tune
end Bands
namespace Net
open Bands Sheet
variable {s:Side}{B : BandWidth}{T : BPress.Sheet.Atlas}{y C C' Lf : ℝ}{N:ℕ} (F:Net s T Lf y C C' N)(X:Bands s B) (U : Micro s)
-- angular Mark weights, before orienting/fixing forests. split the sum over labels
def takeN (i : X.Index)(p:Duo s) := if i∈X.dc then BPress.dirichlet (X.band i) y U else F.markN (X.mark i) U p
lemma takeN_D {i:X.Index}(p:i∈X.dc)(h) : F.takeN X U i h=BPress.dirichlet (X.band i) y U:=if_pos p
lemma takeN_pos (i:X.Index)(h): 0≤ F.takeN X U i h:=by unfold takeN; split; exact prod_nonneg fun _ _=>chord.density_nonneg ..; exact F.markN_nonneg ..
def quoteN (i:X.Index) := chord.charge group (xi y)^(X.pay i).card
lemma quoteN_bound (i:X.Index)(p:Duo s): F.takeN X U i p ≤ quoteN (y:=y) X i:=by
 unfold quoteN takeN pay; split; exact (le_abs_self _).trans (dirichlet_bound ..); exact F.markN_bound ..
lemma takeN_local (i:X.Index)(p): LocalOn (X.band i) (fun U:Micro s=>F.takeN X U i p):= by unfold takeN; split; exact dirichlet_local (X.band i) y; exact F.markN_local (X.mark i) p
lemma takeN_meas (i:X.Index) : Measurable (fun u : Micro s× Duo s=> F.takeN X u.1 i u.2):=by unfold takeN; split; exact (dirichlet_meas ..).comp measurable_fst; exact F.markN_meas ..

-- owner(i) for template issues. In tone use.
def avgN (i:X.Index)(p:Duo s) : Micro s:= if i∈ X.dc then background y else F.template (X.mark i) ((X.mark i).reads U) p
lemma charge_all (p : ∀ i∈X.poles,U i=1)(i:X.Index)(t) : F.takeN X U i t=∏ j∈ X.pay i,chord.ballDensity (xi y) (F.avgN X U i t j) (U j):=by
 unfold takeN pay avgN; split; rfl; next h=> apply F.exact_in; intro j k; apply p; refine X.poles_s i ?_; rwa [Bands.storesN,if_neg h]
end Net
end YM.CF.BPress
